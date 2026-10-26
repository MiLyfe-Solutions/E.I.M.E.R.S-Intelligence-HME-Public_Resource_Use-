import V185TrunkScan21Chunk074

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_909091 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 6]
def baseStart_909091 : Nat := 118140960795 + 909091 * 2 ^ 59
def prefixEnd_909091 : Nat := 4983230072969 + 3 ^ 40 * 909091 * 2
def baseEnd_909091 : Nat := 207466951856270182658521

theorem tailTrace_909091 : CollatzResearch.WordTrace tailWord_909091 prefixEnd_909091 207466951856270182658521 := by
  unfold tailWord_909091
  simp only [CollatzResearch.WordTrace]
  refine ⟨33157272749526042226999127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22104848499684028151332751 33157272749526042226999127)
  ·
    refine ⟨49735909124289063340498691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33157272749526042226999127 49735909124289063340498691)
    ·
      refine ⟨74603863686433595010748037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49735909124289063340498691 74603863686433595010748037)
      ·
        refine ⟨13988224441206299064515257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74603863686433595010748037 13988224441206299064515257)
        ·
          refine ⟨10491168330904724298386443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13988224441206299064515257 10491168330904724298386443)
          ·
            refine ⟨15736752496357086447579665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10491168330904724298386443 15736752496357086447579665)
            ·
              refine ⟨11802564372267814835684749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15736752496357086447579665 11802564372267814835684749)
              ·
                refine ⟨4425961639600430563381781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11802564372267814835684749 4425961639600430563381781)
                ·
                  refine ⟨207466951856270182658521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4425961639600430563381781 207466951856270182658521)
                  ·
                    rfl

theorem cell21_909091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_909091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909091 prefixEnd_909091 := by exact prefixLift 909091
  have htrace : WordTrace (prefixWord ++ tailWord_909091) baseStart_909091 baseEnd_909091 := by
    simpa [prefixWord, tailWord_909091, baseEnd_909091] using wordTrace_append hprefix tailTrace_909091
  have hstable : (prefixWord ++ tailWord_909091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909091).length < 2 ^ (prefixWord ++ tailWord_909091).sum := by decide
  have hdescent : baseEnd_909091 < baseStart_909091 := by decide
  rcases family_descends (prefixWord ++ tailWord_909091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909136 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_909136 : Nat := 118140960795 + 909136 * 2 ^ 59
def prefixEnd_909136 : Nat := 4983230072969 + 3 ^ 40 * 909136 * 2
def baseEnd_909136 : Nat := 207477221469360104408429

theorem tailTrace_909136 : CollatzResearch.WordTrace tailWord_909136 prefixEnd_909136 207477221469360104408429 := by
  unfold tailWord_909136
  simp only [CollatzResearch.WordTrace]
  refine ⟨16579457017181507456193631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22105942689575343274924841 16579457017181507456193631)
  ·
    refine ⟨24869185525772261184290447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16579457017181507456193631 24869185525772261184290447)
    ·
      refine ⟨37303778288658391776435671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24869185525772261184290447 37303778288658391776435671)
      ·
        refine ⟨55955667432987587664653507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37303778288658391776435671 55955667432987587664653507)
        ·
          refine ⟨83933501149481381496980261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55955667432987587664653507 83933501149481381496980261)
          ·
            refine ⟨15737531465527759030683799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83933501149481381496980261 15737531465527759030683799)
            ·
              refine ⟨23606297198291638546025699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15737531465527759030683799 23606297198291638546025699)
              ·
                refine ⟨35409445797437457819038549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23606297198291638546025699 35409445797437457819038549)
                ·
                  refine ⟨207477221469360104408429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35409445797437457819038549 207477221469360104408429)
                  ·
                    rfl

theorem cell21_909136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_909136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909136 prefixEnd_909136 := by exact prefixLift 909136
  have htrace : WordTrace (prefixWord ++ tailWord_909136) baseStart_909136 baseEnd_909136 := by
    simpa [prefixWord, tailWord_909136, baseEnd_909136] using wordTrace_append hprefix tailTrace_909136
  have hstable : (prefixWord ++ tailWord_909136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909136).length < 2 ^ (prefixWord ++ tailWord_909136).sum := by decide
  have hdescent : baseEnd_909136 < baseStart_909136 := by decide
  rcases family_descends (prefixWord ++ tailWord_909136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909153 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 5]
def baseStart_909153 : Nat := 118140960795 + 909153 * 2 ^ 59
def prefixEnd_909153 : Nat := 4983230072969 + 3 ^ 40 * 909153 * 2
def baseEnd_909153 : Nat := 207481101100971852625061

theorem tailTrace_909153 : CollatzResearch.WordTrace tailWord_909153 prefixEnd_909153 207481101100971852625061 := by
  unfold tailWord_909153
  simp only [CollatzResearch.WordTrace]
  refine ⟨33159534075301426815756113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22106356050200951210504075 33159534075301426815756113)
  ·
    refine ⟨24869650556476070111817085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33159534075301426815756113 24869650556476070111817085)
    ·
      refine ⟨9326118958678526291931407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24869650556476070111817085 9326118958678526291931407)
      ·
        refine ⟨13989178438017789437897111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9326118958678526291931407 13989178438017789437897111)
        ·
          refine ⟨20983767657026684156845667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13989178438017789437897111 20983767657026684156845667)
          ·
            refine ⟨31475651485540026235268501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20983767657026684156845667 31475651485540026235268501)
            ·
              refine ⟨1475421163384688729778211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31475651485540026235268501 1475421163384688729778211)
              ·
                refine ⟨2213131745077033094667317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475421163384688729778211 2213131745077033094667317)
                ·
                  refine ⟨207481101100971852625061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2213131745077033094667317 207481101100971852625061)
                  ·
                    rfl

theorem cell21_909153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_909153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909153 prefixEnd_909153 := by exact prefixLift 909153
  have htrace : WordTrace (prefixWord ++ tailWord_909153) baseStart_909153 baseEnd_909153 := by
    simpa [prefixWord, tailWord_909153, baseEnd_909153] using wordTrace_append hprefix tailTrace_909153
  have hstable : (prefixWord ++ tailWord_909153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909153).length < 2 ^ (prefixWord ++ tailWord_909153).sum := by decide
  have hdescent : baseEnd_909153 < baseStart_909153 := by decide
  rcases family_descends (prefixWord ++ tailWord_909153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909187 : List Nat := [1, 1, 1, 3, 4, 4, 1, 3, 3]
def baseStart_909187 : Nat := 118140960795 + 909187 * 2 ^ 59
def prefixEnd_909187 : Nat := 4983230072969 + 3 ^ 40 * 909187 * 2
def baseEnd_909187 : Nat := 207488860364195349058325

theorem tailTrace_909187 : CollatzResearch.WordTrace tailWord_909187 prefixEnd_909187 207488860364195349058325 := by
  unfold tailWord_909187
  simp only [CollatzResearch.WordTrace]
  refine ⟨33160774157178250622493815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22107182771452167081662543 33160774157178250622493815)
  ·
    refine ⟨49741161235767375933740723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33160774157178250622493815 49741161235767375933740723)
    ·
      refine ⟨74611741853651063900611085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49741161235767375933740723 74611741853651063900611085)
      ·
        refine ⟨27979403195119148962729157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74611741853651063900611085 27979403195119148962729157)
        ·
          refine ⟨5246138099084840430511717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27979403195119148962729157 5246138099084840430511717)
          ·
            refine ⟨983650893578407580720947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5246138099084840430511717 983650893578407580720947)
            ·
              refine ⟨1475476340367611371081421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983650893578407580720947 1475476340367611371081421)
              ·
                refine ⟨553303627637854264155533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1475476340367611371081421 553303627637854264155533)
                ·
                  refine ⟨207488860364195349058325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 553303627637854264155533 207488860364195349058325)
                  ·
                    rfl

theorem cell21_909187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 3].length) (baseStart_909187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909187 prefixEnd_909187 := by exact prefixLift 909187
  have htrace : WordTrace (prefixWord ++ tailWord_909187) baseStart_909187 baseEnd_909187 := by
    simpa [prefixWord, tailWord_909187, baseEnd_909187] using wordTrace_append hprefix tailTrace_909187
  have hstable : (prefixWord ++ tailWord_909187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909187).length < 2 ^ (prefixWord ++ tailWord_909187).sum := by decide
  have hdescent : baseEnd_909187 < baseStart_909187 := by decide
  rcases family_descends (prefixWord ++ tailWord_909187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909204 : List Nat := [2, 4, 2, 1, 1, 3, 3, 2, 3]
def baseStart_909204 : Nat := 118140960795 + 909204 * 2 ^ 59
def prefixEnd_909204 : Nat := 4983230072969 + 3 ^ 40 * 909204 * 2
def baseEnd_909204 : Nat := 207492739995807097274957

theorem tailTrace_909204 : CollatzResearch.WordTrace tailWord_909204 prefixEnd_909204 207492739995807097274957 := by
  unfold tailWord_909204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16580697099058331262931333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22107596132077775017241777 16580697099058331262931333)
  ·
    refine ⟨3108880706073437111799625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16580697099058331262931333 3108880706073437111799625)
    ·
      refine ⟨2331660529555077833849719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3108880706073437111799625 2331660529555077833849719)
      ·
        refine ⟨3497490794332616750774579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2331660529555077833849719 3497490794332616750774579)
        ·
          refine ⟨5246236191498925126161869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3497490794332616750774579 5246236191498925126161869)
          ·
            refine ⟨1967338571812096922310701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5246236191498925126161869 1967338571812096922310701)
            ·
              refine ⟨737751964429536345866513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1967338571812096922310701 737751964429536345866513)
              ·
                refine ⟨553313973322152259399885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737751964429536345866513 553313973322152259399885)
                ·
                  refine ⟨207492739995807097274957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 553313973322152259399885 207492739995807097274957)
                  ·
                    rfl

theorem cell21_909204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_909204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909204 prefixEnd_909204 := by exact prefixLift 909204
  have htrace : WordTrace (prefixWord ++ tailWord_909204) baseStart_909204 baseEnd_909204 := by
    simpa [prefixWord, tailWord_909204, baseEnd_909204] using wordTrace_append hprefix tailTrace_909204
  have hstable : (prefixWord ++ tailWord_909204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909204).length < 2 ^ (prefixWord ++ tailWord_909204).sum := by decide
  have hdescent : baseEnd_909204 < baseStart_909204 := by decide
  rcases family_descends (prefixWord ++ tailWord_909204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909215 : List Nat := [1, 1, 2, 5, 3, 1, 2, 6]
def baseStart_909215 : Nat := 118140960795 + 909215 * 2 ^ 59
def prefixEnd_909215 : Nat := 4983230072969 + 3 ^ 40 * 909215 * 2
def baseEnd_909215 : Nat := 69165083448557840863867

theorem tailTrace_909215 : CollatzResearch.WordTrace tailWord_909215 prefixEnd_909215 69165083448557840863867 := by
  unfold tailWord_909215
  simp only [CollatzResearch.WordTrace]
  refine ⟨33161795401076811404513099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22107863600717874269675399 33161795401076811404513099)
  ·
    refine ⟨49742693101615217106769649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33161795401076811404513099 49742693101615217106769649)
    ·
      refine ⟨37307019826211412830077237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49742693101615217106769649 37307019826211412830077237)
      ·
        refine ⟨3497533108707319952819741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37307019826211412830077237 3497533108707319952819741)
        ·
          refine ⟨1311574915765244982307403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3497533108707319952819741 1311574915765244982307403)
          ·
            refine ⟨1967362373647867473461105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311574915765244982307403 1967362373647867473461105)
            ·
              refine ⟨1475521780235900605095829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1967362373647867473461105 1475521780235900605095829)
              ·
                refine ⟨69165083448557840863867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1475521780235900605095829 69165083448557840863867)
                ·
                  rfl

theorem cell21_909215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 6].length) (baseStart_909215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909215 prefixEnd_909215 := by exact prefixLift 909215
  have htrace : WordTrace (prefixWord ++ tailWord_909215) baseStart_909215 baseEnd_909215 := by
    simpa [prefixWord, tailWord_909215, baseEnd_909215] using wordTrace_append hprefix tailTrace_909215
  have hstable : (prefixWord ++ tailWord_909215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909215).length < 2 ^ (prefixWord ++ tailWord_909215).sum := by decide
  have hdescent : baseEnd_909215 < baseStart_909215 := by decide
  rcases family_descends (prefixWord ++ tailWord_909215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909260 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 4]
def baseStart_909260 : Nat := 118140960795 + 909260 * 2 ^ 59
def prefixEnd_909260 : Nat := 4983230072969 + 3 ^ 40 * 909260 * 2
def baseEnd_909260 : Nat := 207505519958763444341509

theorem tailTrace_909260 : CollatzResearch.WordTrace tailWord_909260 prefixEnd_909260 207505519958763444341509 := by
  unfold tailWord_909260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16581718342956892044950617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22108957790609189393267489 16581718342956892044950617)
  ·
    refine ⟨12436288757217669033712963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16581718342956892044950617 12436288757217669033712963)
    ·
      refine ⟨18654433135826503550569445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12436288757217669033712963 18654433135826503550569445)
      ·
        refine ⟨3497706212967469415731771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18654433135826503550569445 3497706212967469415731771)
        ·
          refine ⟨5246559319451204123597657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3497706212967469415731771 5246559319451204123597657)
          ·
            refine ⟨3934919489588403092698243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5246559319451204123597657 3934919489588403092698243)
            ·
              refine ⟨5902379234382604639047365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934919489588403092698243 5902379234382604639047365)
              ·
                refine ⟨1106696106446738369821381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5902379234382604639047365 1106696106446738369821381)
                ·
                  refine ⟨207505519958763444341509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1106696106446738369821381 207505519958763444341509)
                  ·
                    rfl

theorem cell21_909260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_909260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909260 prefixEnd_909260 := by exact prefixLift 909260
  have htrace : WordTrace (prefixWord ++ tailWord_909260) baseStart_909260 baseEnd_909260 := by
    simpa [prefixWord, tailWord_909260, baseEnd_909260] using wordTrace_append hprefix tailTrace_909260
  have hstable : (prefixWord ++ tailWord_909260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909260).length < 2 ^ (prefixWord ++ tailWord_909260).sum := by decide
  have hdescent : baseEnd_909260 < baseStart_909260 := by decide
  rcases family_descends (prefixWord ++ tailWord_909260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909322 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_909322 : Nat := 118140960795 + 909322 * 2 ^ 59
def prefixEnd_909322 : Nat := 4983230072969 + 3 ^ 40 * 909322 * 2
def baseEnd_909322 : Nat := 207519669203465114308049

theorem tailTrace_909322 : CollatzResearch.WordTrace tailWord_909322 prefixEnd_909322 207519669203465114308049 := by
  unfold tailWord_909322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8291424502922292169664555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22110465341126112452438813 8291424502922292169664555)
  ·
    refine ⟨12437136754383438254496833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8291424502922292169664555 12437136754383438254496833)
    ·
      refine ⟨9327852565787578690872625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12437136754383438254496833 9327852565787578690872625)
      ·
        refine ⟨6995889424340684018154469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9327852565787578690872625 6995889424340684018154469)
        ·
          refine ⟨1311729267063878253403963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6995889424340684018154469 1311729267063878253403963)
          ·
            refine ⟨1967593900595817380105945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311729267063878253403963 1967593900595817380105945)
            ·
              refine ⟨1475695425446863035079459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1967593900595817380105945 1475695425446863035079459)
              ·
                refine ⟨2213543138170294552619189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475695425446863035079459 2213543138170294552619189)
                ·
                  refine ⟨207519669203465114308049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2213543138170294552619189 207519669203465114308049)
                  ·
                    rfl

theorem cell21_909322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_909322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909322 prefixEnd_909322 := by exact prefixLift 909322
  have htrace : WordTrace (prefixWord ++ tailWord_909322) baseStart_909322 baseEnd_909322 := by
    simpa [prefixWord, tailWord_909322, baseEnd_909322] using wordTrace_append hprefix tailTrace_909322
  have hstable : (prefixWord ++ tailWord_909322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909322).length < 2 ^ (prefixWord ++ tailWord_909322).sum := by decide
  have hdescent : baseEnd_909322 < baseStart_909322 := by decide
  rcases family_descends (prefixWord ++ tailWord_909322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909440 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_909440 : Nat := 118140960795 + 909440 * 2 ^ 59
def prefixEnd_909440 : Nat := 4983230072969 + 3 ^ 40 * 909440 * 2
def baseEnd_909440 : Nat := 207546598411123131341141

theorem tailTrace_909440 : CollatzResearch.WordTrace tailWord_909440 prefixEnd_909440 207546598411123131341141 := by
  unfold tailWord_909440
  simp only [CollatzResearch.WordTrace]
  refine ⟨16585000912630837415726887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22113334550174449887635849 16585000912630837415726887)
  ·
    refine ⟨24877501368946256123590331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16585000912630837415726887 24877501368946256123590331)
    ·
      refine ⟨37316252053419384185385497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24877501368946256123590331 37316252053419384185385497)
      ·
        refine ⟨27987189040064538139039123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37316252053419384185385497 27987189040064538139039123)
        ·
          refine ⟨41980783560096807208558685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27987189040064538139039123 41980783560096807208558685)
          ·
            refine ⟨15742793835036302703209507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41980783560096807208558685 15742793835036302703209507)
            ·
              refine ⟨23614190752554454054814261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15742793835036302703209507 23614190752554454054814261)
              ·
                refine ⟨2213830383051980067638837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23614190752554454054814261 2213830383051980067638837)
                ·
                  refine ⟨207546598411123131341141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2213830383051980067638837 207546598411123131341141)
                  ·
                    rfl

theorem cell21_909440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_909440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909440 prefixEnd_909440 := by exact prefixLift 909440
  have htrace : WordTrace (prefixWord ++ tailWord_909440) baseStart_909440 baseEnd_909440 := by
    simpa [prefixWord, tailWord_909440, baseEnd_909440] using wordTrace_append hprefix tailTrace_909440
  have hstable : (prefixWord ++ tailWord_909440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909440).length < 2 ^ (prefixWord ++ tailWord_909440).sum := by decide
  have hdescent : baseEnd_909440 < baseStart_909440 := by decide
  rcases family_descends (prefixWord ++ tailWord_909440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909547 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 4]
def baseStart_909547 : Nat := 118140960795 + 909547 * 2 ^ 59
def prefixEnd_909547 : Nat := 4983230072969 + 3 ^ 40 * 909547 * 2
def baseEnd_909547 : Nat := 207571017268914723057589

theorem tailTrace_909547 : CollatzResearch.WordTrace tailWord_909547 prefixEnd_909547 207571017268914723057589 := by
  unfold tailWord_909547
  simp only [CollatzResearch.WordTrace]
  refine ⟨33173904435874032105598895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22115936290582688070399263 33173904435874032105598895)
  ·
    refine ⟨49760856653811048158398343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33173904435874032105598895 49760856653811048158398343)
    ·
      refine ⟨74641284980716572237597515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49760856653811048158398343 74641284980716572237597515)
      ·
        refine ⟨111961927471074858356396273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74641284980716572237597515 111961927471074858356396273)
        ·
          refine ⟨83971445603306143767297205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111961927471074858356396273 83971445603306143767297205)
          ·
            refine ⟨7872323025309950978184113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83971445603306143767297205 7872323025309950978184113)
            ·
              refine ⟨5904242268982463233638085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7872323025309950978184113 5904242268982463233638085)
              ·
                refine ⟨1107045425434211856307141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5904242268982463233638085 1107045425434211856307141)
                ·
                  refine ⟨207571017268914723057589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107045425434211856307141 207571017268914723057589)
                  ·
                    rfl

theorem cell21_909547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 4].length) (baseStart_909547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909547 prefixEnd_909547 := by exact prefixLift 909547
  have htrace : WordTrace (prefixWord ++ tailWord_909547) baseStart_909547 baseEnd_909547 := by
    simpa [prefixWord, tailWord_909547, baseEnd_909547] using wordTrace_append hprefix tailTrace_909547
  have hstable : (prefixWord ++ tailWord_909547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909547).length < 2 ^ (prefixWord ++ tailWord_909547).sum := by decide
  have hdescent : baseEnd_909547 < baseStart_909547 := by decide
  rcases family_descends (prefixWord ++ tailWord_909547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909564 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 4]
def baseStart_909564 : Nat := 118140960795 + 909564 * 2 ^ 59
def prefixEnd_909564 : Nat := 4983230072969 + 3 ^ 40 * 909564 * 2
def baseEnd_909564 : Nat := 207574896900526471274221

theorem tailTrace_909564 : CollatzResearch.WordTrace tailWord_909564 prefixEnd_909564 207574896900526471274221 := by
  unfold tailWord_909564
  simp only [CollatzResearch.WordTrace]
  refine ⟨16587262238406222004483873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22116349651208296005978497 16587262238406222004483873)
  ·
    refine ⟨12440446678804666503362905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16587262238406222004483873 12440446678804666503362905)
    ·
      refine ⟨9330335009103499877522179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12440446678804666503362905 9330335009103499877522179)
      ·
        refine ⟨13995502513655249816283269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9330335009103499877522179 13995502513655249816283269)
        ·
          refine ⟨2624156721310359340553113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13995502513655249816283269 2624156721310359340553113)
          ·
            refine ⟨1968117540982769505414835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2624156721310359340553113 1968117540982769505414835)
            ·
              refine ⟨2952176311474154258122253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968117540982769505414835 2952176311474154258122253)
              ·
                refine ⟨1107066116802807846795845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2952176311474154258122253 1107066116802807846795845)
                ·
                  refine ⟨207574896900526471274221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107066116802807846795845 207574896900526471274221)
                  ·
                    rfl

theorem cell21_909564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_909564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909564 prefixEnd_909564 := by exact prefixLift 909564
  have htrace : WordTrace (prefixWord ++ tailWord_909564) baseStart_909564 baseEnd_909564 := by
    simpa [prefixWord, tailWord_909564, baseEnd_909564] using wordTrace_append hprefix tailTrace_909564
  have hstable : (prefixWord ++ tailWord_909564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909564).length < 2 ^ (prefixWord ++ tailWord_909564).sum := by decide
  have hdescent : baseEnd_909564 < baseStart_909564 := by decide
  rcases family_descends (prefixWord ++ tailWord_909564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909598 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_909598 : Nat := 118140960795 + 909598 * 2 ^ 59
def prefixEnd_909598 : Nat := 4983230072969 + 3 ^ 40 * 909598 * 2
def baseEnd_909598 : Nat := 207582656163749967707485

theorem tailTrace_909598 : CollatzResearch.WordTrace tailWord_909598 prefixEnd_909598 207582656163749967707485 := by
  unfold tailWord_909598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4146970569836158476963181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22117176372459511877136965 4146970569836158476963181)
  ·
    refine ⟨1555113963688559428861193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4146970569836158476963181 1555113963688559428861193)
    ·
      refine ⟨1166335472766419571645895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1555113963688559428861193 1166335472766419571645895)
      ·
        refine ⟨1749503209149629357468843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166335472766419571645895 1749503209149629357468843)
        ·
          refine ⟨2624254813724444036203265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1749503209149629357468843 2624254813724444036203265)
          ·
            refine ⟨1968191110293333027152449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2624254813724444036203265 1968191110293333027152449)
            ·
              refine ⟨1476143332719999770364337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968191110293333027152449 1476143332719999770364337)
              ·
                refine ⟨1107107499539999827773253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476143332719999770364337 1107107499539999827773253)
                ·
                  refine ⟨207582656163749967707485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107107499539999827773253 207582656163749967707485)
                  ·
                    rfl

theorem cell21_909598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_909598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909598 prefixEnd_909598 := by exact prefixLift 909598
  have htrace : WordTrace (prefixWord ++ tailWord_909598) baseStart_909598 baseEnd_909598 := by
    simpa [prefixWord, tailWord_909598, baseEnd_909598] using wordTrace_append hprefix tailTrace_909598
  have hstable : (prefixWord ++ tailWord_909598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909598).length < 2 ^ (prefixWord ++ tailWord_909598).sum := by decide
  have hdescent : baseEnd_909598 < baseStart_909598 := by decide
  rcases family_descends (prefixWord ++ tailWord_909598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909685 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 5]
def baseStart_909685 : Nat := 118140960795 + 909685 * 2 ^ 59
def prefixEnd_909685 : Nat := 4983230072969 + 3 ^ 40 * 909685 * 2
def baseEnd_909685 : Nat := 207602510749057149757307

theorem tailTrace_909685 : CollatzResearch.WordTrace tailWord_909685 prefixEnd_909685 207602510749057149757307 := by
  unfold tailWord_909685
  simp only [CollatzResearch.WordTrace]
  refine ⟨33178937709374081674122509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22119291806249387782748339 33178937709374081674122509)
  ·
    refine ⟨12442101641015280627795941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33178937709374081674122509 12442101641015280627795941)
    ·
      refine ⟨2332894057690365117711739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12442101641015280627795941 2332894057690365117711739)
      ·
        refine ⟨3499341086535547676567609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332894057690365117711739 3499341086535547676567609)
        ·
          refine ⟨2624505814901660757425707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3499341086535547676567609 2624505814901660757425707)
          ·
            refine ⟨3936758722352491136138561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2624505814901660757425707 3936758722352491136138561)
            ·
              refine ⟨2952569041764368352103921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3936758722352491136138561 2952569041764368352103921)
              ·
                refine ⟨2214426781323276264077941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2952569041764368352103921 2214426781323276264077941)
                ·
                  refine ⟨207602510749057149757307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2214426781323276264077941 207602510749057149757307)
                  ·
                    rfl

theorem cell21_909685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_909685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909685 prefixEnd_909685 := by exact prefixLift 909685
  have htrace : WordTrace (prefixWord ++ tailWord_909685) baseStart_909685 baseEnd_909685 := by
    simpa [prefixWord, tailWord_909685, baseEnd_909685] using wordTrace_append hprefix tailTrace_909685
  have hstable : (prefixWord ++ tailWord_909685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909685).length < 2 ^ (prefixWord ++ tailWord_909685).sum := by decide
  have hdescent : baseEnd_909685 < baseStart_909685 := by decide
  rcases family_descends (prefixWord ++ tailWord_909685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909730 : List Nat := [3, 3, 1, 2, 1, 1, 4, 6]
def baseStart_909730 : Nat := 118140960795 + 909730 * 2 ^ 59
def prefixEnd_909730 : Nat := 4983230072969 + 3 ^ 40 * 909730 * 2
def baseEnd_909730 : Nat := 69204260120715690502405

theorem tailTrace_909730 : CollatzResearch.WordTrace tailWord_909730 prefixEnd_909730 69204260120715690502405 := by
  unfold tailWord_909730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295144748552763589877661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22120385996140702906340429 8295144748552763589877661)
  ·
    refine ⟨3110679280707286346204123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8295144748552763589877661 3110679280707286346204123)
    ·
      refine ⟨4666018921060929519306185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3110679280707286346204123 4666018921060929519306185)
      ·
        refine ⟨3499514190795697139479639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4666018921060929519306185 3499514190795697139479639)
        ·
          refine ⟨5249271286193545709219459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3499514190795697139479639 5249271286193545709219459)
          ·
            refine ⟨7873906929290318563829189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249271286193545709219459 7873906929290318563829189)
            ·
              refine ⟨1476357549241934730717973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7873906929290318563829189 1476357549241934730717973)
              ·
                refine ⟨69204260120715690502405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1476357549241934730717973 69204260120715690502405)
                ·
                  rfl

theorem cell21_909730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_909730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909730 prefixEnd_909730 := by exact prefixLift 909730
  have htrace : WordTrace (prefixWord ++ tailWord_909730) baseStart_909730 baseEnd_909730 := by
    simpa [prefixWord, tailWord_909730, baseEnd_909730] using wordTrace_append hprefix tailTrace_909730
  have hstable : (prefixWord ++ tailWord_909730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909730).length < 2 ^ (prefixWord ++ tailWord_909730).sum := by decide
  have hdescent : baseEnd_909730 < baseStart_909730 := by decide
  rcases family_descends (prefixWord ++ tailWord_909730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909826 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_909826 : Nat := 118140960795 + 909826 * 2 ^ 59
def prefixEnd_909826 : Nat := 4983230072969 + 3 ^ 40 * 909826 * 2
def baseEnd_909826 : Nat := 207634688870072237907019

theorem tailTrace_909826 : CollatzResearch.WordTrace tailWord_909826 prefixEnd_909826 207634688870072237907019 := by
  unfold tailWord_909826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8296020100465815688751333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22122720267908841836670221 8296020100465815688751333)
  ·
    refine ⟨1555503768837340441640875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8296020100465815688751333 1555503768837340441640875)
    ·
      refine ⟨2333255653256010662461313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1555503768837340441640875 2333255653256010662461313)
      ·
        refine ⟨1749941739942007996845985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2333255653256010662461313 1749941739942007996845985)
        ·
          refine ⟨1312456304956505997634489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1749941739942007996845985 1312456304956505997634489)
          ·
            refine ⟨984342228717379498225867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1312456304956505997634489 984342228717379498225867)
            ·
              refine ⟨1476513343076069247338801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984342228717379498225867 1476513343076069247338801)
              ·
                refine ⟨1107385007307051935504101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476513343076069247338801 1107385007307051935504101)
                ·
                  refine ⟨207634688870072237907019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107385007307051935504101 207634688870072237907019)
                  ·
                    rfl

theorem cell21_909826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_909826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909826 prefixEnd_909826 := by exact prefixLift 909826
  have htrace : WordTrace (prefixWord ++ tailWord_909826) baseStart_909826 baseEnd_909826 := by
    simpa [prefixWord, tailWord_909826, baseEnd_909826] using wordTrace_append hprefix tailTrace_909826
  have hstable : (prefixWord ++ tailWord_909826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909826).length < 2 ^ (prefixWord ++ tailWord_909826).sum := by decide
  have hdescent : baseEnd_909826 < baseStart_909826 := by decide
  rcases family_descends (prefixWord ++ tailWord_909826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909941 : List Nat := [1, 3, 4, 2, 11]
def baseStart_909941 : Nat := 118140960795 + 909941 * 2 ^ 59
def prefixEnd_909941 : Nat := 4983230072969 + 3 ^ 40 * 909941 * 2
def baseEnd_909941 : Nat := 2563715227615525845557

theorem tailTrace_909941 : CollatzResearch.WordTrace tailWord_909941 prefixEnd_909941 2563715227615525845557 := by
  unfold tailWord_909941
  simp only [CollatzResearch.WordTrace]
  refine ⟨33188274796446637395441677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22125516530964424930294451 33188274796446637395441677)
  ·
    refine ⟨12445603048667489023290629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33188274796446637395441677 12445603048667489023290629)
    ·
      refine ⟨2333550571625154191866993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12445603048667489023290629 2333550571625154191866993)
      ·
        refine ⟨1750162928718865643900245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2333550571625154191866993 1750162928718865643900245)
        ·
          refine ⟨2563715227615525845557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1750162928718865643900245 2563715227615525845557)
          ·
            rfl

theorem cell21_909941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 11].length) (baseStart_909941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909941 prefixEnd_909941 := by exact prefixLift 909941
  have htrace : WordTrace (prefixWord ++ tailWord_909941) baseStart_909941 baseEnd_909941 := by
    simpa [prefixWord, tailWord_909941, baseEnd_909941] using wordTrace_append hprefix tailTrace_909941
  have hstable : (prefixWord ++ tailWord_909941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909941).length < 2 ^ (prefixWord ++ tailWord_909941).sum := by decide
  have hdescent : baseEnd_909941 < baseStart_909941 := by decide
  rcases family_descends (prefixWord ++ tailWord_909941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910003 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 4]
def baseStart_910003 : Nat := 118140960795 + 910003 * 2 ^ 59
def prefixEnd_910003 : Nat := 4983230072969 + 3 ^ 40 * 910003 * 2
def baseEnd_910003 : Nat := 207675082681559263456657

theorem tailTrace_910003 : CollatzResearch.WordTrace tailWord_910003 prefixEnd_910003 207675082681559263456657 := by
  unfold tailWord_910003
  simp only [CollatzResearch.WordTrace]
  refine ⟨33190536122222021984198663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22127024081481347989465775 33190536122222021984198663)
  ·
    refine ⟨49785804183333032976297995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33190536122222021984198663 49785804183333032976297995)
    ·
      refine ⟨74678706274999549464446993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49785804183333032976297995 74678706274999549464446993)
      ·
        refine ⟨56009029706249662098335245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74678706274999549464446993 56009029706249662098335245)
        ·
          refine ⟨21003386139843623286875717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56009029706249662098335245 21003386139843623286875717)
          ·
            refine ⟨3938134901220679366289197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21003386139843623286875717 3938134901220679366289197)
            ·
              refine ⟨1476800587957754762358449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3938134901220679366289197 1476800587957754762358449)
              ·
                refine ⟨1107600440968316071768837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476800587957754762358449 1107600440968316071768837)
                ·
                  refine ⟨207675082681559263456657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107600440968316071768837 207675082681559263456657)
                  ·
                    rfl

theorem cell21_910003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 4].length) (baseStart_910003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910003 prefixEnd_910003 := by exact prefixLift 910003
  have htrace : WordTrace (prefixWord ++ tailWord_910003) baseStart_910003 baseEnd_910003 := by
    simpa [prefixWord, tailWord_910003, baseEnd_910003] using wordTrace_append hprefix tailTrace_910003
  have hstable : (prefixWord ++ tailWord_910003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910003).length < 2 ^ (prefixWord ++ tailWord_910003).sum := by decide
  have hdescent : baseEnd_910003 < baseStart_910003 := by decide
  rcases family_descends (prefixWord ++ tailWord_910003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910034 : List Nat := [3, 2, 2, 2, 3, 1, 1, 7]
def baseStart_910034 : Nat := 118140960795 + 910034 * 2 ^ 59
def prefixEnd_910034 : Nat := 4983230072969 + 3 ^ 40 * 910034 * 2
def baseEnd_910034 : Nat := 69227385767970032813309

theorem tailTrace_910034 : CollatzResearch.WordTrace tailWord_910034 prefixEnd_910034 69227385767970032813309 := by
  unfold tailWord_910034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8297916696277428569644289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22127777856739809519051437 8297916696277428569644289)
  ·
    refine ⟨6223437522208071427233217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8297916696277428569644289 6223437522208071427233217)
    ·
      refine ⟨4667578141656053570424913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6223437522208071427233217 4667578141656053570424913)
      ·
        refine ⟨3500683606242040177818685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4667578141656053570424913 3500683606242040177818685)
        ·
          refine ⟨1312756352340765066682007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3500683606242040177818685 1312756352340765066682007)
          ·
            refine ⟨1969134528511147600023011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312756352340765066682007 1969134528511147600023011)
            ·
              refine ⟨2953701792766721400034517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969134528511147600023011 2953701792766721400034517)
              ·
                refine ⟨69227385767970032813309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2953701792766721400034517 69227385767970032813309)
                ·
                  rfl

theorem cell21_910034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_910034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910034 prefixEnd_910034 := by exact prefixLift 910034
  have htrace : WordTrace (prefixWord ++ tailWord_910034) baseStart_910034 baseEnd_910034 := by
    simpa [prefixWord, tailWord_910034, baseEnd_910034] using wordTrace_append hprefix tailTrace_910034
  have hstable : (prefixWord ++ tailWord_910034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910034).length < 2 ^ (prefixWord ++ tailWord_910034).sum := by decide
  have hdescent : baseEnd_910034 < baseStart_910034 := by decide
  rcases family_descends (prefixWord ++ tailWord_910034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910068 : List Nat := [2, 6, 1, 1, 2, 1, 2, 6]
def baseStart_910068 : Nat := 118140960795 + 910068 * 2 ^ 59
def prefixEnd_910068 : Nat := 4983230072969 + 3 ^ 40 * 910068 * 2
def baseEnd_910068 : Nat := 69229972189044531624397

theorem tailTrace_910068 : CollatzResearch.WordTrace tailWord_910068 prefixEnd_910068 69229972189044531624397 := by
  unfold tailWord_910068
  simp only [CollatzResearch.WordTrace]
  refine ⟨16596453433493269042657429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22128604577991025390209905 16596453433493269042657429)
  ·
    refine ⟨777958754694996986374567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16596453433493269042657429 777958754694996986374567)
    ·
      refine ⟨1166938132042495479561851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 777958754694996986374567 1166938132042495479561851)
      ·
        refine ⟨1750407198063743219342777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166938132042495479561851 1750407198063743219342777)
        ·
          refine ⟨1312805398547807414507083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1750407198063743219342777 1312805398547807414507083)
          ·
            refine ⟨1969208097821711121760625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312805398547807414507083 1969208097821711121760625)
            ·
              refine ⟨1476906073366283341320469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1969208097821711121760625 1476906073366283341320469)
              ·
                refine ⟨69229972189044531624397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1476906073366283341320469 69229972189044531624397)
                ·
                  rfl

theorem cell21_910068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_910068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910068 prefixEnd_910068 := by exact prefixLift 910068
  have htrace : WordTrace (prefixWord ++ tailWord_910068) baseStart_910068 baseEnd_910068 := by
    simpa [prefixWord, tailWord_910068, baseEnd_910068] using wordTrace_append hprefix tailTrace_910068
  have hstable : (prefixWord ++ tailWord_910068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910068).length < 2 ^ (prefixWord ++ tailWord_910068).sum := by decide
  have hdescent : baseEnd_910068 < baseStart_910068 := by decide
  rcases family_descends (prefixWord ++ tailWord_910068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910116 : List Nat := [2, 3, 1, 3, 4, 1, 2, 2, 3]
def baseStart_910116 : Nat := 118140960795 + 910116 * 2 ^ 59
def prefixEnd_910116 : Nat := 4983230072969 + 3 ^ 40 * 910116 * 2
def baseEnd_910116 : Nat := 207700870821096178073093

theorem tailTrace_910116 : CollatzResearch.WordTrace tailWord_910116 prefixEnd_910116 207700870821096178073093 := by
  unfold tailWord_910116
  simp only [CollatzResearch.WordTrace]
  refine ⟨16597328785406321141531101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22129771713875094855374801 16597328785406321141531101)
  ·
    refine ⟨6223998294527370428074163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16597328785406321141531101 6223998294527370428074163)
    ·
      refine ⟨9335997441791055642111245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223998294527370428074163 9335997441791055642111245)
      ·
        refine ⟨3500999040671645865791717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9335997441791055642111245 3500999040671645865791717)
        ·
          refine ⟨656437320125933599835947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3500999040671645865791717 656437320125933599835947)
          ·
            refine ⟨984655980188900399753921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656437320125933599835947 984655980188900399753921)
            ·
              refine ⟨738491985141675299815441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984655980188900399753921 738491985141675299815441)
              ·
                refine ⟨553868988856256474861581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738491985141675299815441 553868988856256474861581)
                ·
                  refine ⟨207700870821096178073093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 553868988856256474861581 207700870821096178073093)
                  ·
                    rfl

theorem cell21_910116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_910116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910116 prefixEnd_910116 := by exact prefixLift 910116
  have htrace : WordTrace (prefixWord ++ tailWord_910116) baseStart_910116 baseEnd_910116 := by
    simpa [prefixWord, tailWord_910116, baseEnd_910116] using wordTrace_append hprefix tailTrace_910116
  have hstable : (prefixWord ++ tailWord_910116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910116).length < 2 ^ (prefixWord ++ tailWord_910116).sum := by decide
  have hdescent : baseEnd_910116 < baseStart_910116 := by decide
  rcases family_descends (prefixWord ++ tailWord_910116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910141 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 5]
def baseStart_910141 : Nat := 118140960795 + 910141 * 2 ^ 59
def prefixEnd_910141 : Nat := 4983230072969 + 3 ^ 40 * 910141 * 2
def baseEnd_910141 : Nat := 207706576161701690156375

theorem tailTrace_910141 : CollatzResearch.WordTrace tailWord_910141 prefixEnd_910141 207706576161701690156375 := by
  unfold tailWord_910141
  simp only [CollatzResearch.WordTrace]
  refine ⟨33195569395722071552722277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22130379597148047701814851 33195569395722071552722277)
  ·
    refine ⟨6224169261697888416135427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33195569395722071552722277 6224169261697888416135427)
    ·
      refine ⟨9336253892546832624203141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6224169261697888416135427 9336253892546832624203141)
      ·
        refine ⟨1750547604852531117038089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9336253892546832624203141 1750547604852531117038089)
        ·
          refine ⟨1312910703639398337778567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1750547604852531117038089 1312910703639398337778567)
          ·
            refine ⟨1969366055459097506667851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312910703639398337778567 1969366055459097506667851)
            ·
              refine ⟨2954049083188646260001777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969366055459097506667851 2954049083188646260001777)
              ·
                refine ⟨2215536812391484695001333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2954049083188646260001777 2215536812391484695001333)
                ·
                  refine ⟨207706576161701690156375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2215536812391484695001333 207706576161701690156375)
                  ·
                    rfl

theorem cell21_910141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_910141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910141 prefixEnd_910141 := by exact prefixLift 910141
  have htrace : WordTrace (prefixWord ++ tailWord_910141) baseStart_910141 baseEnd_910141 := by
    simpa [prefixWord, tailWord_910141, baseEnd_910141] using wordTrace_append hprefix tailTrace_910141
  have hstable : (prefixWord ++ tailWord_910141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910141).length < 2 ^ (prefixWord ++ tailWord_910141).sum := by decide
  have hdescent : baseEnd_910141 < baseStart_910141 := by decide
  rcases family_descends (prefixWord ++ tailWord_910141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910172 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 4]
def baseStart_910172 : Nat := 118140960795 + 910172 * 2 ^ 59
def prefixEnd_910172 : Nat := 4983230072969 + 3 ^ 40 * 910172 * 2
def baseEnd_910172 : Nat := 207713650784052525139645

theorem tailTrace_910172 : CollatzResearch.WordTrace tailWord_910172 prefixEnd_910172 207713650784052525139645 := by
  unfold tailWord_910172
  simp only [CollatzResearch.WordTrace]
  refine ⟨16598350029304881923550385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22131133372406509231400513 16598350029304881923550385)
  ·
    refine ⟨12448762521978661442662789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16598350029304881923550385 12448762521978661442662789)
    ·
      refine ⟨2334142972870999020499273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12448762521978661442662789 2334142972870999020499273)
      ·
        refine ⟨1750607229653249265374455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2334142972870999020499273 1750607229653249265374455)
        ·
          refine ⟨2625910844479873898061683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750607229653249265374455 2625910844479873898061683)
          ·
            refine ⟨3938866266719810847092525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625910844479873898061683 3938866266719810847092525)
            ·
              refine ⟨1477074850019929067659697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3938866266719810847092525 1477074850019929067659697)
              ·
                refine ⟨1107806137514946800744773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1477074850019929067659697 1107806137514946800744773)
                ·
                  refine ⟨207713650784052525139645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107806137514946800744773 207713650784052525139645)
                  ·
                    rfl

theorem cell21_910172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_910172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910172 prefixEnd_910172 := by exact prefixLift 910172
  have htrace : WordTrace (prefixWord ++ tailWord_910172) baseStart_910172 baseEnd_910172 := by
    simpa [prefixWord, tailWord_910172, baseEnd_910172] using wordTrace_append hprefix tailTrace_910172
  have hstable : (prefixWord ++ tailWord_910172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910172).length < 2 ^ (prefixWord ++ tailWord_910172).sum := by decide
  have hdescent : baseEnd_910172 < baseStart_910172 := by decide
  rcases family_descends (prefixWord ++ tailWord_910172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910217 : List Nat := [1, 2, 1, 1, 5, 2, 3, 3, 3]
def baseStart_910217 : Nat := 118140960795 + 910217 * 2 ^ 59
def prefixEnd_910217 : Nat := 4983230072969 + 3 ^ 40 * 910217 * 2
def baseEnd_910217 : Nat := 207723920397142446889553

theorem tailTrace_910217 : CollatzResearch.WordTrace tailWord_910217 prefixEnd_910217 207723920397142446889553 := by
  unfold tailWord_910217
  simp only [CollatzResearch.WordTrace]
  refine ⟨33198341343446736532488905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22132227562297824354992603 33198341343446736532488905)
  ·
    refine ⟨24898756007585052399366679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33198341343446736532488905 24898756007585052399366679)
    ·
      refine ⟨37348134011377578599050019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24898756007585052399366679 37348134011377578599050019)
      ·
        refine ⟨56022201017066367898575029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37348134011377578599050019 56022201017066367898575029)
        ·
          refine ⟨5252081345349971990491409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56022201017066367898575029 5252081345349971990491409)
          ·
            refine ⟨3939061009012478992868557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5252081345349971990491409 3939061009012478992868557)
            ·
              refine ⟨1477147878379679622325709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3939061009012478992868557 1477147878379679622325709)
              ·
                refine ⟨553930454392379858372141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1477147878379679622325709 553930454392379858372141)
                ·
                  refine ⟨207723920397142446889553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 553930454392379858372141 207723920397142446889553)
                  ·
                    rfl

theorem cell21_910217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 3].length) (baseStart_910217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910217 prefixEnd_910217 := by exact prefixLift 910217
  have htrace : WordTrace (prefixWord ++ tailWord_910217) baseStart_910217 baseEnd_910217 := by
    simpa [prefixWord, tailWord_910217, baseEnd_910217] using wordTrace_append hprefix tailTrace_910217
  have hstable : (prefixWord ++ tailWord_910217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910217).length < 2 ^ (prefixWord ++ tailWord_910217).sum := by decide
  have hdescent : baseEnd_910217 < baseStart_910217 := by decide
  rcases family_descends (prefixWord ++ tailWord_910217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910234 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 5]
def baseStart_910234 : Nat := 118140960795 + 910234 * 2 ^ 59
def prefixEnd_910234 : Nat := 4983230072969 + 3 ^ 40 * 910234 * 2
def baseEnd_910234 : Nat := 207727800028754195106185

theorem tailTrace_910234 : CollatzResearch.WordTrace tailWord_910234 prefixEnd_910234 207727800028754195106185 := by
  unfold tailWord_910234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8299740346096287108964439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22132640922923432290571837 8299740346096287108964439)
  ·
    refine ⟨12449610519144430663446659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8299740346096287108964439 12449610519144430663446659)
    ·
      refine ⟨18674415778716645995169989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12449610519144430663446659 18674415778716645995169989)
      ·
        refine ⟨3501452958509371124094373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18674415778716645995169989 3501452958509371124094373)
        ·
          refine ⟨656522429720507085767695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3501452958509371124094373 656522429720507085767695)
          ·
            refine ⟨984783644580760628651543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656522429720507085767695 984783644580760628651543)
            ·
              refine ⟨1477175466871140942977315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984783644580760628651543 1477175466871140942977315)
              ·
                refine ⟨2215763200306711414465973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477175466871140942977315 2215763200306711414465973)
                ·
                  refine ⟨207727800028754195106185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2215763200306711414465973 207727800028754195106185)
                  ·
                    rfl

theorem cell21_910234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_910234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910234 prefixEnd_910234 := by exact prefixLift 910234
  have htrace : WordTrace (prefixWord ++ tailWord_910234) baseStart_910234 baseEnd_910234 := by
    simpa [prefixWord, tailWord_910234, baseEnd_910234] using wordTrace_append hprefix tailTrace_910234
  have hstable : (prefixWord ++ tailWord_910234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910234).length < 2 ^ (prefixWord ++ tailWord_910234).sum := by decide
  have hdescent : baseEnd_910234 < baseStart_910234 := by decide
  rcases family_descends (prefixWord ++ tailWord_910234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910380 : List Nat := [2, 2, 1, 1, 1, 2, 5, 7]
def baseStart_910380 : Nat := 118140960795 + 910380 * 2 ^ 59
def prefixEnd_910380 : Nat := 4983230072969 + 3 ^ 40 * 910380 * 2
def baseEnd_910380 : Nat := 69253706405963461890851

theorem tailTrace_910380 : CollatzResearch.WordTrace tailWord_910380 prefixEnd_910380 69253706405963461890851 := by
  unfold tailWord_910380
  simp only [CollatzResearch.WordTrace]
  refine ⟨16602143220928107685336297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22136190961237476913781729 16602143220928107685336297)
  ·
    refine ⟨12451607415696080764002223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16602143220928107685336297 12451607415696080764002223)
    ·
      refine ⟨18677411123544121146003335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12451607415696080764002223 18677411123544121146003335)
      ·
        refine ⟨28016116685316181719005003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18677411123544121146003335 28016116685316181719005003)
        ·
          refine ⟨42024175027974272578507505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28016116685316181719005003 42024175027974272578507505)
          ·
            refine ⟨31518131270980704433880629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42024175027974272578507505 31518131270980704433880629)
            ·
              refine ⟨2954824806654441040676309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31518131270980704433880629 2954824806654441040676309)
              ·
                refine ⟨69253706405963461890851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2954824806654441040676309 69253706405963461890851)
                ·
                  rfl

theorem cell21_910380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_910380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910380 prefixEnd_910380 := by exact prefixLift 910380
  have htrace : WordTrace (prefixWord ++ tailWord_910380) baseStart_910380 baseEnd_910380 := by
    simpa [prefixWord, tailWord_910380, baseEnd_910380] using wordTrace_append hprefix tailTrace_910380
  have hstable : (prefixWord ++ tailWord_910380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910380).length < 2 ^ (prefixWord ++ tailWord_910380).sum := by decide
  have hdescent : baseEnd_910380 < baseStart_910380 := by decide
  rcases family_descends (prefixWord ++ tailWord_910380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910397 : List Nat := [1, 4, 1, 3, 1, 4, 7]
def baseStart_910397 : Nat := 118140960795 + 910397 * 2 ^ 59
def prefixEnd_910397 : Nat := 4983230072969 + 3 ^ 40 * 910397 * 2
def baseEnd_910397 : Nat := 23084999872166903765465

theorem tailTrace_910397 : CollatzResearch.WordTrace tailWord_910397 prefixEnd_910397 23084999872166903765465 := by
  unfold tailWord_910397
  simp only [CollatzResearch.WordTrace]
  refine ⟨33204906482794627274041445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22136604321863084849360963 33204906482794627274041445)
  ·
    refine ⟨6225919965523992613882771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33204906482794627274041445 6225919965523992613882771)
    ·
      refine ⟨9338879948285988920824157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6225919965523992613882771 9338879948285988920824157)
      ·
        refine ⟨3502079980607245845309059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9338879948285988920824157 3502079980607245845309059)
        ·
          refine ⟨5253119970910868767963589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502079980607245845309059 5253119970910868767963589)
          ·
            refine ⟨984959994545787893993173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5253119970910868767963589 984959994545787893993173)
            ·
              refine ⟨23084999872166903765465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 984959994545787893993173 23084999872166903765465)
              ·
                rfl

theorem cell21_910397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 7].length) (baseStart_910397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910397 prefixEnd_910397 := by exact prefixLift 910397
  have htrace : WordTrace (prefixWord ++ tailWord_910397) baseStart_910397 baseEnd_910397 := by
    simpa [prefixWord, tailWord_910397, baseEnd_910397] using wordTrace_append hprefix tailTrace_910397
  have hstable : (prefixWord ++ tailWord_910397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910397).length < 2 ^ (prefixWord ++ tailWord_910397).sum := by decide
  have hdescent : baseEnd_910397 < baseStart_910397 := by decide
  rcases family_descends (prefixWord ++ tailWord_910397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910425 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 8]
def baseStart_910425 : Nat := 118140960795 + 910425 * 2 ^ 59
def prefixEnd_910425 : Nat := 4983230072969 + 3 ^ 40 * 910425 * 2
def baseEnd_910425 : Nat := 207771388830980307422461

theorem tailTrace_910425 : CollatzResearch.WordTrace tailWord_910425 prefixEnd_910425 207771388830980307422461 := by
  unfold tailWord_910425
  simp only [CollatzResearch.WordTrace]
  refine ⟨33205927726693188056060729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22137285151128792037373819 33205927726693188056060729)
  ·
    refine ⟨24904445795019891042045547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33205927726693188056060729 24904445795019891042045547)
    ·
      refine ⟨37356668692529836563068321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24904445795019891042045547 37356668692529836563068321)
      ·
        refine ⟨28017501519397377422301241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37356668692529836563068321 28017501519397377422301241)
        ·
          refine ⟨21013126139548033066725931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28017501519397377422301241 21013126139548033066725931)
          ·
            refine ⟨31519689209322049600088897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21013126139548033066725931 31519689209322049600088897)
            ·
              refine ⟨23639766906991537200066673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31519689209322049600088897 23639766906991537200066673)
              ·
                refine ⟨17729825180243652900050005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23639766906991537200066673 17729825180243652900050005)
                ·
                  refine ⟨207771388830980307422461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17729825180243652900050005 207771388830980307422461)
                  ·
                    rfl

theorem cell21_910425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_910425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910425 prefixEnd_910425 := by exact prefixLift 910425
  have htrace : WordTrace (prefixWord ++ tailWord_910425) baseStart_910425 baseEnd_910425 := by
    simpa [prefixWord, tailWord_910425, baseEnd_910425] using wordTrace_append hprefix tailTrace_910425
  have hstable : (prefixWord ++ tailWord_910425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910425).length < 2 ^ (prefixWord ++ tailWord_910425).sum := by decide
  have hdescent : baseEnd_910425 < baseStart_910425 := by decide
  rcases family_descends (prefixWord ++ tailWord_910425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910473 : List Nat := [1, 2, 1, 1, 4, 5, 1, 6]
def baseStart_910473 : Nat := 118140960795 + 910473 * 2 ^ 59
def prefixEnd_910473 : Nat := 4983230072969 + 3 ^ 40 * 910473 * 2
def baseEnd_910473 : Nat := 69260781028314296874121

theorem tailTrace_910473 : CollatzResearch.WordTrace tailWord_910473 prefixEnd_910473 69260781028314296874121 := by
  unfold tailWord_910473
  simp only [CollatzResearch.WordTrace]
  refine ⟨33207678430519292253808073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22138452287012861502538715 33207678430519292253808073)
  ·
    refine ⟨24905758822889469190356055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33207678430519292253808073 24905758822889469190356055)
    ·
      refine ⟨37358638234334203785534083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24905758822889469190356055 37358638234334203785534083)
      ·
        refine ⟨56037957351501305678301125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37358638234334203785534083 56037957351501305678301125)
        ·
          refine ⟨10507117003406494814681461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56037957351501305678301125 10507117003406494814681461)
          ·
            refine ⟨985042219069358888876387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10507117003406494814681461 985042219069358888876387)
            ·
              refine ⟨1477563328604038333314581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985042219069358888876387 1477563328604038333314581)
              ·
                refine ⟨69260781028314296874121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1477563328604038333314581 69260781028314296874121)
                ·
                  rfl

theorem cell21_910473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 6].length) (baseStart_910473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910473 prefixEnd_910473 := by exact prefixLift 910473
  have htrace : WordTrace (prefixWord ++ tailWord_910473) baseStart_910473 baseEnd_910473 := by
    simpa [prefixWord, tailWord_910473, baseEnd_910473] using wordTrace_append hprefix tailTrace_910473
  have hstable : (prefixWord ++ tailWord_910473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910473).length < 2 ^ (prefixWord ++ tailWord_910473).sum := by decide
  have hdescent : baseEnd_910473 < baseStart_910473 := by decide
  rcases family_descends (prefixWord ++ tailWord_910473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910487 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 7]
def baseStart_910487 : Nat := 118140960795 + 910487 * 2 ^ 59
def prefixEnd_910487 : Nat := 4983230072969 + 3 ^ 40 * 910487 * 2
def baseEnd_910487 : Nat := 207785538075681977389001

theorem tailTrace_910487 : CollatzResearch.WordTrace tailWord_910487 prefixEnd_910487 207785538075681977389001 := by
  unfold tailWord_910487
  simp only [CollatzResearch.WordTrace]
  refine ⟨33208189052468572644817715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22138792701645715096545143 33208189052468572644817715)
  ·
    refine ⟨49812283578702858967226573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33208189052468572644817715 49812283578702858967226573)
    ·
      refine ⟨18679606342013572112709965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49812283578702858967226573 18679606342013572112709965)
      ·
        refine ⟨7004852378255089542266237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18679606342013572112709965 7004852378255089542266237)
        ·
          refine ⟨2626819641845658578349839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7004852378255089542266237 2626819641845658578349839)
          ·
            refine ⟨3940229462768487867524759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626819641845658578349839 3940229462768487867524759)
            ·
              refine ⟨5910344194152731801287139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940229462768487867524759 5910344194152731801287139)
              ·
                refine ⟨8865516291229097701930709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5910344194152731801287139 8865516291229097701930709)
                ·
                  refine ⟨207785538075681977389001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8865516291229097701930709 207785538075681977389001)
                  ·
                    rfl

theorem cell21_910487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_910487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910487 prefixEnd_910487 := by exact prefixLift 910487
  have htrace : WordTrace (prefixWord ++ tailWord_910487) baseStart_910487 baseEnd_910487 := by
    simpa [prefixWord, tailWord_910487, baseEnd_910487] using wordTrace_append hprefix tailTrace_910487
  have hstable : (prefixWord ++ tailWord_910487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910487).length < 2 ^ (prefixWord ++ tailWord_910487).sum := by decide
  have hdescent : baseEnd_910487 < baseStart_910487 := by decide
  rcases family_descends (prefixWord ++ tailWord_910487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910490 : List Nat := [3, 1, 1, 5, 1, 2, 3, 5]
def baseStart_910490 : Nat := 118140960795 + 910490 * 2 ^ 59
def prefixEnd_910490 : Nat := 4983230072969 + 3 ^ 40 * 910490 * 2
def baseEnd_910490 : Nat := 69262074238851546279665

theorem tailTrace_910490 : CollatzResearch.WordTrace tailWord_910490 prefixEnd_910490 69262074238851546279665 := by
  unfold tailWord_910490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8302074617864426039294231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22138865647638469438117949 8302074617864426039294231)
  ·
    refine ⟨12453111926796639058941347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8302074617864426039294231 12453111926796639058941347)
    ·
      refine ⟨18679667890194958588412021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12453111926796639058941347 18679667890194958588412021)
      ·
        refine ⟨1751218864705777367663627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18679667890194958588412021 1751218864705777367663627)
        ·
          refine ⟨2626828297058666051495441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751218864705777367663627 2626828297058666051495441)
          ·
            refine ⟨1970121222793999538621581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2626828297058666051495441 1970121222793999538621581)
            ·
              refine ⟨738795458547749826983093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1970121222793999538621581 738795458547749826983093)
              ·
                refine ⟨69262074238851546279665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 738795458547749826983093 69262074238851546279665)
                ·
                  rfl

theorem cell21_910490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_910490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910490 prefixEnd_910490 := by exact prefixLift 910490
  have htrace : WordTrace (prefixWord ++ tailWord_910490) baseStart_910490 baseEnd_910490 := by
    simpa [prefixWord, tailWord_910490, baseEnd_910490] using wordTrace_append hprefix tailTrace_910490
  have hstable : (prefixWord ++ tailWord_910490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910490).length < 2 ^ (prefixWord ++ tailWord_910490).sum := by decide
  have hdescent : baseEnd_910490 < baseStart_910490 := by decide
  rcases family_descends (prefixWord ++ tailWord_910490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910541 : List Nat := [1, 6, 2, 2, 2, 1, 2, 5]
def baseStart_910541 : Nat := 118140960795 + 910541 * 2 ^ 59
def prefixEnd_910541 : Nat := 4983230072969 + 3 ^ 40 * 910541 * 2
def baseEnd_910541 : Nat := 69265953870463294496297

theorem tailTrace_910541 : CollatzResearch.WordTrace tailWord_910541 prefixEnd_910541 69265953870463294496297 := by
  unfold tailWord_910541
  simp only [CollatzResearch.WordTrace]
  refine ⟨33210158594272939867283477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22140105729515293244855651 33210158594272939867283477)
  ·
    refine ⟨1556726184106544056278913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33210158594272939867283477 1556726184106544056278913)
    ·
      refine ⟨1167544638079908042209185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1556726184106544056278913 1167544638079908042209185)
      ·
        refine ⟨875658478559931031656889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1167544638079908042209185 875658478559931031656889)
        ·
          refine ⟨656743858919948273742667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 875658478559931031656889 656743858919948273742667)
          ·
            refine ⟨985115788379922410614001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656743858919948273742667 985115788379922410614001)
            ·
              refine ⟨738836841284941807960501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985115788379922410614001 738836841284941807960501)
              ·
                refine ⟨69265953870463294496297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 738836841284941807960501 69265953870463294496297)
                ·
                  rfl

theorem cell21_910541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 5].length) (baseStart_910541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910541 prefixEnd_910541 := by exact prefixLift 910541
  have htrace : WordTrace (prefixWord ++ tailWord_910541) baseStart_910541 baseEnd_910541 := by
    simpa [prefixWord, tailWord_910541, baseEnd_910541] using wordTrace_append hprefix tailTrace_910541
  have hstable : (prefixWord ++ tailWord_910541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910541).length < 2 ^ (prefixWord ++ tailWord_910541).sum := by decide
  have hdescent : baseEnd_910541 < baseStart_910541 := by decide
  rcases family_descends (prefixWord ++ tailWord_910541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910549 : List Nat := [1, 3, 2, 4, 1, 2, 1, 7]
def baseStart_910549 : Nat := 118140960795 + 910549 * 2 ^ 59
def prefixEnd_910549 : Nat := 4983230072969 + 3 ^ 40 * 910549 * 2
def baseEnd_910549 : Nat := 69266562440127882451847

theorem tailTrace_910549 : CollatzResearch.WordTrace tailWord_910549 prefixEnd_910549 69266562440127882451847 := by
  unfold tailWord_910549
  simp only [CollatzResearch.WordTrace]
  refine ⟨33210450378243957233574701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22140300252162638155716467 33210450378243957233574701)
  ·
    refine ⟨12453918891841483962590513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33210450378243957233574701 12453918891841483962590513)
    ·
      refine ⟨9340439168881112971942885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12453918891841483962590513 9340439168881112971942885)
      ·
        refine ⟨1751332344165208682239291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9340439168881112971942885 1751332344165208682239291)
        ·
          refine ⟨2626998516247813023358937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751332344165208682239291 2626998516247813023358937)
          ·
            refine ⟨1970248887185859767519203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2626998516247813023358937 1970248887185859767519203)
            ·
              refine ⟨2955373330778789651278805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970248887185859767519203 2955373330778789651278805)
              ·
                refine ⟨69266562440127882451847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2955373330778789651278805 69266562440127882451847)
                ·
                  rfl

theorem cell21_910549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 7].length) (baseStart_910549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910549 prefixEnd_910549 := by exact prefixLift 910549
  have htrace : WordTrace (prefixWord ++ tailWord_910549) baseStart_910549 baseEnd_910549 := by
    simpa [prefixWord, tailWord_910549, baseEnd_910549] using wordTrace_append hprefix tailTrace_910549
  have hstable : (prefixWord ++ tailWord_910549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910549).length < 2 ^ (prefixWord ++ tailWord_910549).sum := by decide
  have hdescent : baseEnd_910549 < baseStart_910549 := by decide
  rcases family_descends (prefixWord ++ tailWord_910549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910746 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_910746 : Nat := 118140960795 + 910746 * 2 ^ 59
def prefixEnd_910746 : Nat := 4983230072969 + 3 ^ 40 * 910746 * 2
def baseEnd_910746 : Nat := 207844645404355082571805

theorem tailTrace_910746 : CollatzResearch.WordTrace tailWord_910746 prefixEnd_910746 207844645404355082571805 := by
  unfold tailWord_910746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8304408889632564969624023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22145090372353506585664061 8304408889632564969624023)
  ·
    refine ⟨12456613334448847454436035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8304408889632564969624023 12456613334448847454436035)
    ·
      refine ⟨18684920001673271181654053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12456613334448847454436035 18684920001673271181654053)
      ·
        refine ⟨3503422500313738346560135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18684920001673271181654053 3503422500313738346560135)
        ·
          refine ⟨5255133750470607519840203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3503422500313738346560135 5255133750470607519840203)
          ·
            refine ⟨7882700625705911279760305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5255133750470607519840203 7882700625705911279760305)
            ·
              refine ⟨5912025469279433459820229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7882700625705911279760305 5912025469279433459820229)
              ·
                refine ⟨1108504775489893773716293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5912025469279433459820229 1108504775489893773716293)
                ·
                  refine ⟨207844645404355082571805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1108504775489893773716293 207844645404355082571805)
                  ·
                    rfl

theorem cell21_910746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_910746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910746 prefixEnd_910746 := by exact prefixLift 910746
  have htrace : WordTrace (prefixWord ++ tailWord_910746) baseStart_910746 baseEnd_910746 := by
    simpa [prefixWord, tailWord_910746, baseEnd_910746] using wordTrace_append hprefix tailTrace_910746
  have hstable : (prefixWord ++ tailWord_910746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910746).length < 2 ^ (prefixWord ++ tailWord_910746).sum := by decide
  have hdescent : baseEnd_910746 < baseStart_910746 := by decide
  rcases family_descends (prefixWord ++ tailWord_910746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910867 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 5]
def baseStart_910867 : Nat := 118140960795 + 910867 * 2 ^ 59
def prefixEnd_910867 : Nat := 4983230072969 + 3 ^ 40 * 910867 * 2
def baseEnd_910867 : Nat := 207872259252885761054891

theorem tailTrace_910867 : CollatzResearch.WordTrace tailWord_910867 prefixEnd_910867 207872259252885761054891 := by
  unfold tailWord_910867
  simp only [CollatzResearch.WordTrace]
  refine ⟨33222048791091897543650855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22148032527394598362433903 33222048791091897543650855)
  ·
    refine ⟨49833073186637846315476283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33222048791091897543650855 49833073186637846315476283)
    ·
      refine ⟨74749609779956769473214425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49833073186637846315476283 74749609779956769473214425)
      ·
        refine ⟨56062207334967577104910819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74749609779956769473214425 56062207334967577104910819)
        ·
          refine ⟨84093311002451365657366229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56062207334967577104910819 84093311002451365657366229)
          ·
            refine ⟨1970936976619953882594521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 84093311002451365657366229 1970936976619953882594521)
            ·
              refine ⟨1478202732464965411945891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1970936976619953882594521 1478202732464965411945891)
              ·
                refine ⟨2217304098697448117918837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478202732464965411945891 2217304098697448117918837)
                ·
                  refine ⟨207872259252885761054891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2217304098697448117918837 207872259252885761054891)
                  ·
                    rfl

theorem cell21_910867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 5].length) (baseStart_910867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910867 prefixEnd_910867 := by exact prefixLift 910867
  have htrace : WordTrace (prefixWord ++ tailWord_910867) baseStart_910867 baseEnd_910867 := by
    simpa [prefixWord, tailWord_910867, baseEnd_910867] using wordTrace_append hprefix tailTrace_910867
  have hstable : (prefixWord ++ tailWord_910867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910867).length < 2 ^ (prefixWord ++ tailWord_910867).sum := by decide
  have hdescent : baseEnd_910867 < baseStart_910867 := by decide
  rcases family_descends (prefixWord ++ tailWord_910867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910901 : List Nat := [1, 3, 3, 1, 1, 5, 1, 3, 3]
def baseStart_910901 : Nat := 118140960795 + 910901 * 2 ^ 59
def prefixEnd_910901 : Nat := 4983230072969 + 3 ^ 40 * 910901 * 2
def baseEnd_910901 : Nat := 207880018516109257488155

theorem tailTrace_910901 : CollatzResearch.WordTrace tailWord_910901 prefixEnd_910901 207880018516109257488155 := by
  unfold tailWord_910901
  simp only [CollatzResearch.WordTrace]
  refine ⟨33223288872968721350388557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22148859248645814233592371 33223288872968721350388557)
  ·
    refine ⟨12458733327363270506395709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33223288872968721350388557 12458733327363270506395709)
    ·
      refine ⟨4672024997761226439898391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12458733327363270506395709 4672024997761226439898391)
      ·
        refine ⟨7008037496641839659847587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672024997761226439898391 7008037496641839659847587)
        ·
          refine ⟨10512056244962759489771381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008037496641839659847587 10512056244962759489771381)
          ·
            refine ⟨985505272965258702166067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10512056244962759489771381 985505272965258702166067)
            ·
              refine ⟨1478257909447888053249101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985505272965258702166067 1478257909447888053249101)
              ·
                refine ⟨554346716042958019968413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1478257909447888053249101 554346716042958019968413)
                ·
                  refine ⟨207880018516109257488155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554346716042958019968413 207880018516109257488155)
                  ·
                    rfl

theorem cell21_910901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_910901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910901 prefixEnd_910901 := by exact prefixLift 910901
  have htrace : WordTrace (prefixWord ++ tailWord_910901) baseStart_910901 baseEnd_910901 := by
    simpa [prefixWord, tailWord_910901, baseEnd_910901] using wordTrace_append hprefix tailTrace_910901
  have hstable : (prefixWord ++ tailWord_910901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910901).length < 2 ^ (prefixWord ++ tailWord_910901).sum := by decide
  have hdescent : baseEnd_910901 < baseStart_910901 := by decide
  rcases family_descends (prefixWord ++ tailWord_910901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910918 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_910918 : Nat := 118140960795 + 910918 * 2 ^ 59
def prefixEnd_910918 : Nat := 4983230072969 + 3 ^ 40 * 910918 * 2
def baseEnd_910918 : Nat := 207883898147721005704787

theorem tailTrace_910918 : CollatzResearch.WordTrace tailWord_910918 prefixEnd_910918 207883898147721005704787 := by
  unfold tailWord_910918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1038247153559597914179919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22149272609271422169171605 1038247153559597914179919)
  ·
    refine ⟨1557370730339396871269879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1038247153559597914179919 1557370730339396871269879)
    ·
      refine ⟨2336056095509095306904819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1557370730339396871269879 2336056095509095306904819)
      ·
        refine ⟨3504084143263642960357229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336056095509095306904819 3504084143263642960357229)
        ·
          refine ⟨1314031553723866110133961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3504084143263642960357229 1314031553723866110133961)
          ·
            refine ⟨985523665292899582600471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314031553723866110133961 985523665292899582600471)
            ·
              refine ⟨1478285497939349373900707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985523665292899582600471 1478285497939349373900707)
              ·
                refine ⟨2217428246909024060851061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478285497939349373900707 2217428246909024060851061)
                ·
                  refine ⟨207883898147721005704787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2217428246909024060851061 207883898147721005704787)
                  ·
                    rfl

theorem cell21_910918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_910918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910918 prefixEnd_910918 := by exact prefixLift 910918
  have htrace : WordTrace (prefixWord ++ tailWord_910918) baseStart_910918 baseEnd_910918 := by
    simpa [prefixWord, tailWord_910918, baseEnd_910918] using wordTrace_append hprefix tailTrace_910918
  have hstable : (prefixWord ++ tailWord_910918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910918).length < 2 ^ (prefixWord ++ tailWord_910918).sum := by decide
  have hdescent : baseEnd_910918 < baseStart_910918 := by decide
  rcases family_descends (prefixWord ++ tailWord_910918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910977 : List Nat := [1, 2, 4, 2, 1, 2, 4, 2, 3]
def baseStart_910977 : Nat := 118140960795 + 910977 * 2 ^ 59
def prefixEnd_910977 : Nat := 4983230072969 + 3 ^ 40 * 910977 * 2
def baseEnd_910977 : Nat := 207897362751550014221333

theorem tailTrace_910977 : CollatzResearch.WordTrace tailWord_910977 prefixEnd_910977 207897362751550014221333 := by
  unfold tailWord_910977
  simp only [CollatzResearch.WordTrace]
  refine ⟨33226060820693386330155185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22150707213795590886770123 33226060820693386330155185)
  ·
    refine ⟨24919545615520039747616389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33226060820693386330155185 24919545615520039747616389)
    ·
      refine ⟨4672414802910007452678073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24919545615520039747616389 4672414802910007452678073)
      ·
        refine ⟨3504311102182505589508555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4672414802910007452678073 3504311102182505589508555)
        ·
          refine ⟨5256466653273758384262833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504311102182505589508555 5256466653273758384262833)
          ·
            refine ⟨3942349989955318788197125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5256466653273758384262833 3942349989955318788197125)
            ·
              refine ⟨739190623116622272786961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3942349989955318788197125 739190623116622272786961)
              ·
                refine ⟨554392967337466704590221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739190623116622272786961 554392967337466704590221)
                ·
                  refine ⟨207897362751550014221333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554392967337466704590221 207897362751550014221333)
                  ·
                    rfl

theorem cell21_910977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 3].length) (baseStart_910977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_910977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_910977 prefixEnd_910977 := by exact prefixLift 910977
  have htrace : WordTrace (prefixWord ++ tailWord_910977) baseStart_910977 baseEnd_910977 := by
    simpa [prefixWord, tailWord_910977, baseEnd_910977] using wordTrace_append hprefix tailTrace_910977
  have hstable : (prefixWord ++ tailWord_910977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910977).length < 2 ^ (prefixWord ++ tailWord_910977).sum := by decide
  have hdescent : baseEnd_910977 < baseStart_910977 := by decide
  rcases family_descends (prefixWord ++ tailWord_910977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911036 : List Nat := [2, 2, 2, 3, 1, 2, 2, 4, 3]
def baseStart_911036 : Nat := 118140960795 + 911036 * 2 ^ 59
def prefixEnd_911036 : Nat := 4983230072969 + 3 ^ 40 * 911036 * 2
def baseEnd_911036 : Nat := 207910827355379022737879

theorem tailTrace_911036 : CollatzResearch.WordTrace tailWord_911036 prefixEnd_911036 207910827355379022737879 := by
  unfold tailWord_911036
  simp only [CollatzResearch.WordTrace]
  refine ⟨16614106363739819703276481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22152141818319759604368641 16614106363739819703276481)
  ·
    refine ⟨12460579772804864777457361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16614106363739819703276481 12460579772804864777457361)
    ·
      refine ⟨9345434829603648583093021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12460579772804864777457361 9345434829603648583093021)
      ·
        refine ⟨3504538061101368218659883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9345434829603648583093021 3504538061101368218659883)
        ·
          refine ⟨5256807091652052327989825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504538061101368218659883 5256807091652052327989825)
          ·
            refine ⟨3942605318739039245992369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5256807091652052327989825 3942605318739039245992369)
            ·
              refine ⟨2956953989054279434494277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3942605318739039245992369 2956953989054279434494277)
              ·
                refine ⟨554428872947677393967677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2956953989054279434494277 554428872947677393967677)
                ·
                  refine ⟨207910827355379022737879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554428872947677393967677 207910827355379022737879)
                  ·
                    rfl

theorem cell21_911036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_911036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911036 prefixEnd_911036 := by exact prefixLift 911036
  have htrace : WordTrace (prefixWord ++ tailWord_911036) baseStart_911036 baseEnd_911036 := by
    simpa [prefixWord, tailWord_911036, baseEnd_911036] using wordTrace_append hprefix tailTrace_911036
  have hstable : (prefixWord ++ tailWord_911036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911036).length < 2 ^ (prefixWord ++ tailWord_911036).sum := by decide
  have hdescent : baseEnd_911036 < baseStart_911036 := by decide
  rcases family_descends (prefixWord ++ tailWord_911036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911042 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_911042 : Nat := 118140960795 + 911042 * 2 ^ 59
def prefixEnd_911042 : Nat := 4983230072969 + 3 ^ 40 * 911042 * 2
def baseEnd_911042 : Nat := 207912196637124345637867

theorem tailTrace_911042 : CollatzResearch.WordTrace tailWord_911042 prefixEnd_911042 207912196637124345637867 := by
  unfold tailWord_911042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8307107891364475607817845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22152287710305268287514253 8307107891364475607817845)
  ·
    refine ⟨778791364815419588232923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8307107891364475607817845 778791364815419588232923)
    ·
      refine ⟨1168187047223129382349385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 778791364815419588232923 1168187047223129382349385)
      ·
        refine ⟨876140285417347036762039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1168187047223129382349385 876140285417347036762039)
        ·
          refine ⟨1314210428126020555143059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876140285417347036762039 1314210428126020555143059)
          ·
            refine ⟨1971315642189030832714589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314210428126020555143059 1971315642189030832714589)
            ·
              refine ⟨739243365820886562267971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1971315642189030832714589 739243365820886562267971)
              ·
                refine ⟨1108865048731329843401957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739243365820886562267971 1108865048731329843401957)
                ·
                  refine ⟨207912196637124345637867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1108865048731329843401957 207912196637124345637867)
                  ·
                    rfl

theorem cell21_911042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_911042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911042 prefixEnd_911042 := by exact prefixLift 911042
  have htrace : WordTrace (prefixWord ++ tailWord_911042) baseStart_911042 baseEnd_911042 := by
    simpa [prefixWord, tailWord_911042, baseEnd_911042] using wordTrace_append hprefix tailTrace_911042
  have hstable : (prefixWord ++ tailWord_911042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911042).length < 2 ^ (prefixWord ++ tailWord_911042).sum := by decide
  have hdescent : baseEnd_911042 < baseStart_911042 := by decide
  rcases family_descends (prefixWord ++ tailWord_911042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911047 : List Nat := [1, 1, 4, 1, 1, 1, 4, 8]
def baseStart_911047 : Nat := 118140960795 + 911047 * 2 ^ 59
def prefixEnd_911047 : Nat := 4983230072969 + 3 ^ 40 * 911047 * 2
def baseEnd_911047 : Nat := 69304445901748482684841

theorem tailTrace_911047 : CollatzResearch.WordTrace tailWord_911047 prefixEnd_911047 69304445901748482684841 := by
  unfold tailWord_911047
  simp only [CollatzResearch.WordTrace]
  refine ⟨33228613930439788285203395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22152409286959858856802263 33228613930439788285203395)
  ·
    refine ⟨49842920895659682427805093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33228613930439788285203395 49842920895659682427805093)
    ·
      refine ⟨9345547667936190455213455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49842920895659682427805093 9345547667936190455213455)
      ·
        refine ⟨14018321501904285682820183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9345547667936190455213455 14018321501904285682820183)
        ·
          refine ⟨21027482252856428524230275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14018321501904285682820183 21027482252856428524230275)
          ·
            refine ⟨31541223379284642786345413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21027482252856428524230275 31541223379284642786345413)
            ·
              refine ⟨5913979383615870522439765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31541223379284642786345413 5913979383615870522439765)
              ·
                refine ⟨69304445901748482684841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5913979383615870522439765 69304445901748482684841)
                ·
                  rfl

theorem cell21_911047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 8].length) (baseStart_911047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911047 prefixEnd_911047 := by exact prefixLift 911047
  have htrace : WordTrace (prefixWord ++ tailWord_911047) baseStart_911047 baseEnd_911047 := by
    simpa [prefixWord, tailWord_911047, baseEnd_911047] using wordTrace_append hprefix tailTrace_911047
  have hstable : (prefixWord ++ tailWord_911047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911047).length < 2 ^ (prefixWord ++ tailWord_911047).sum := by decide
  have hdescent : baseEnd_911047 < baseStart_911047 := by decide
  rcases family_descends (prefixWord ++ tailWord_911047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911095 : List Nat := [1, 1, 3, 1, 1, 1, 4, 6, 3]
def baseStart_911095 : Nat := 118140960795 + 911095 * 2 ^ 59
def prefixEnd_911095 : Nat := 4983230072969 + 3 ^ 40 * 911095 * 2
def baseEnd_911095 : Nat := 207924291959208031254425

theorem tailTrace_911095 : CollatzResearch.WordTrace tailWord_911095 prefixEnd_911095 207924291959208031254425 := by
  unfold tailWord_911095
  simp only [CollatzResearch.WordTrace]
  refine ⟨33230364634265892482950739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22153576422843928321967159 33230364634265892482950739)
  ·
    refine ⟨49845546951398838724426109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33230364634265892482950739 49845546951398838724426109)
    ·
      refine ⟨18692080106774564521659791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49845546951398838724426109 18692080106774564521659791)
      ·
        refine ⟨28038120160161846782489687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18692080106774564521659791 28038120160161846782489687)
        ·
          refine ⟨42057180240242770173734531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28038120160161846782489687 42057180240242770173734531)
          ·
            refine ⟨63085770360364155260601797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42057180240242770173734531 63085770360364155260601797)
            ·
              refine ⟨11828581942568279111362837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63085770360364155260601797 11828581942568279111362837)
              ·
                refine ⟨554464778557888083345133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11828581942568279111362837 554464778557888083345133)
                ·
                  refine ⟨207924291959208031254425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554464778557888083345133 207924291959208031254425)
                  ·
                    rfl

theorem cell21_911095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 3].length) (baseStart_911095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911095 prefixEnd_911095 := by exact prefixLift 911095
  have htrace : WordTrace (prefixWord ++ tailWord_911095) baseStart_911095 baseEnd_911095 := by
    simpa [prefixWord, tailWord_911095, baseEnd_911095] using wordTrace_append hprefix tailTrace_911095
  have hstable : (prefixWord ++ tailWord_911095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911095).length < 2 ^ (prefixWord ++ tailWord_911095).sum := by decide
  have hdescent : baseEnd_911095 < baseStart_911095 := by decide
  rcases family_descends (prefixWord ++ tailWord_911095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911157 : List Nat := [1, 3, 3, 1, 4, 2, 1, 6]
def baseStart_911157 : Nat := 118140960795 + 911157 * 2 ^ 59
def prefixEnd_911157 : Nat := 4983230072969 + 3 ^ 40 * 911157 * 2
def baseEnd_911157 : Nat := 69312813734636567073655

theorem tailTrace_911157 : CollatzResearch.WordTrace tailWord_911157 prefixEnd_911157 69312813734636567073655 := by
  unfold tailWord_911157
  simp only [CollatzResearch.WordTrace]
  refine ⟨33232625960041277071707725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22155083973360851381138483 33232625960041277071707725)
  ·
    refine ⟨12462234735015478901890397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33232625960041277071707725 12462234735015478901890397)
    ·
      refine ⟨4673338025630804588208899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12462234735015478901890397 4673338025630804588208899)
      ·
        refine ⟨7010007038446206882313349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4673338025630804588208899 7010007038446206882313349)
        ·
          refine ⟨1314376319708663790433753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7010007038446206882313349 1314376319708663790433753)
          ·
            refine ⟨985782239781497842825315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314376319708663790433753 985782239781497842825315)
            ·
              refine ⟨1478673359672246764237973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985782239781497842825315 1478673359672246764237973)
              ·
                refine ⟨69312813734636567073655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1478673359672246764237973 69312813734636567073655)
                ·
                  rfl

theorem cell21_911157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 6].length) (baseStart_911157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911157 prefixEnd_911157 := by exact prefixLift 911157
  have htrace : WordTrace (prefixWord ++ tailWord_911157) baseStart_911157 baseEnd_911157 := by
    simpa [prefixWord, tailWord_911157, baseEnd_911157] using wordTrace_append hprefix tailTrace_911157
  have hstable : (prefixWord ++ tailWord_911157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911157).length < 2 ^ (prefixWord ++ tailWord_911157).sum := by decide
  have hdescent : baseEnd_911157 < baseStart_911157 := by decide
  rcases family_descends (prefixWord ++ tailWord_911157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911168 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_911168 : Nat := 118140960795 + 911168 * 2 ^ 59
def prefixEnd_911168 : Nat := 4983230072969 + 3 ^ 40 * 911168 * 2
def baseEnd_911168 : Nat := 207940951553776126537609

theorem tailTrace_911168 : CollatzResearch.WordTrace tailWord_911168 prefixEnd_911168 207940951553776126537609 := by
  unfold tailWord_911168
  simp only [CollatzResearch.WordTrace]
  refine ⟨16616513581500712975179079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22155351442000950633572105 16616513581500712975179079)
  ·
    refine ⟨24924770372251069462768619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16616513581500712975179079 24924770372251069462768619)
    ·
      refine ⟨37387155558376604194152929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24924770372251069462768619 37387155558376604194152929)
      ·
        refine ⟨28040366668782453145614697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37387155558376604194152929 28040366668782453145614697)
        ·
          refine ⟨21030275001586839859211023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28040366668782453145614697 21030275001586839859211023)
          ·
            refine ⟨31545412502380259788816535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21030275001586839859211023 31545412502380259788816535)
            ·
              refine ⟨47318118753570389683224803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31545412502380259788816535 47318118753570389683224803)
              ·
                refine ⟨70977178130355584524837205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47318118753570389683224803 70977178130355584524837205)
                ·
                  refine ⟨207940951553776126537609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 70977178130355584524837205 207940951553776126537609)
                  ·
                    rfl

theorem cell21_911168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_911168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911168 prefixEnd_911168 := by exact prefixLift 911168
  have htrace : WordTrace (prefixWord ++ tailWord_911168) baseStart_911168 baseEnd_911168 := by
    simpa [prefixWord, tailWord_911168, baseEnd_911168] using wordTrace_append hprefix tailTrace_911168
  have hstable : (prefixWord ++ tailWord_911168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911168).length < 2 ^ (prefixWord ++ tailWord_911168).sum := by decide
  have hdescent : baseEnd_911168 < baseStart_911168 := by decide
  rcases family_descends (prefixWord ++ tailWord_911168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911188 : List Nat := [2, 4, 1, 1, 3, 1, 1, 5, 3]
def baseStart_911188 : Nat := 118140960795 + 911188 * 2 ^ 59
def prefixEnd_911188 : Nat := 4983230072969 + 3 ^ 40 * 911188 * 2
def baseEnd_911188 : Nat := 207945515826260536204235

theorem tailTrace_911188 : CollatzResearch.WordTrace tailWord_911188 prefixEnd_911188 207945515826260536204235 := by
  unfold tailWord_911188
  simp only [CollatzResearch.WordTrace]
  refine ⟨16616878311464484683043109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22155837748619312910724145 16616878311464484683043109)
  ·
    refine ⟨3115664683399590878070583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16616878311464484683043109 3115664683399590878070583)
    ·
      refine ⟨4673497025099386317105875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3115664683399590878070583 4673497025099386317105875)
      ·
        refine ⟨7010245537649079475658813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4673497025099386317105875 7010245537649079475658813)
        ·
          refine ⟨2628842076618404803372055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7010245537649079475658813 2628842076618404803372055)
          ·
            refine ⟨3943263114927607205058083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628842076618404803372055 3943263114927607205058083)
            ·
              refine ⟨5914894672391410807587125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943263114927607205058083 5914894672391410807587125)
              ·
                refine ⟨554521375536694763211293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5914894672391410807587125 554521375536694763211293)
                ·
                  refine ⟨207945515826260536204235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554521375536694763211293 207945515826260536204235)
                  ·
                    rfl

theorem cell21_911188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_911188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911188 prefixEnd_911188 := by exact prefixLift 911188
  have htrace : WordTrace (prefixWord ++ tailWord_911188) baseStart_911188 baseEnd_911188 := by
    simpa [prefixWord, tailWord_911188, baseEnd_911188] using wordTrace_append hprefix tailTrace_911188
  have hstable : (prefixWord ++ tailWord_911188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911188).length < 2 ^ (prefixWord ++ tailWord_911188).sum := by decide
  have hdescent : baseEnd_911188 < baseStart_911188 := by decide
  rcases family_descends (prefixWord ++ tailWord_911188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911199 : List Nat := [1, 1, 2, 3, 1, 5, 8]
def baseStart_911199 : Nat := 118140960795 + 911199 * 2 ^ 59
def prefixEnd_911199 : Nat := 4983230072969 + 3 ^ 40 * 911199 * 2
def baseEnd_911199 : Nat := 23105336241791884613431

theorem tailTrace_911199 : CollatzResearch.WordTrace tailWord_911199 prefixEnd_911199 23105336241791884613431 := by
  unfold tailWord_911199
  simp only [CollatzResearch.WordTrace]
  refine ⟨33234157825889118244736651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22156105217259412163157767 33234157825889118244736651)
  ·
    refine ⟨49851236738833677367104977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33234157825889118244736651 49851236738833677367104977)
    ·
      refine ⟨37388427554125258025328733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49851236738833677367104977 37388427554125258025328733)
      ·
        refine ⟨14020660332796971759498275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37388427554125258025328733 14020660332796971759498275)
        ·
          refine ⟨21030990499195457639247413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14020660332796971759498275 21030990499195457639247413)
          ·
            refine ⟨1971655359299574153679445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21030990499195457639247413 1971655359299574153679445)
            ·
              refine ⟨23105336241791884613431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1971655359299574153679445 23105336241791884613431)
              ·
                rfl

theorem cell21_911199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 8].length) (baseStart_911199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911199 prefixEnd_911199 := by exact prefixLift 911199
  have htrace : WordTrace (prefixWord ++ tailWord_911199) baseStart_911199 baseEnd_911199 := by
    simpa [prefixWord, tailWord_911199, baseEnd_911199] using wordTrace_append hprefix tailTrace_911199
  have hstable : (prefixWord ++ tailWord_911199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911199).length < 2 ^ (prefixWord ++ tailWord_911199).sum := by decide
  have hdescent : baseEnd_911199 < baseStart_911199 := by decide
  rcases family_descends (prefixWord ++ tailWord_911199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911202 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_911202 : Nat := 118140960795 + 911202 * 2 ^ 59
def prefixEnd_911202 : Nat := 4983230072969 + 3 ^ 40 * 911202 * 2
def baseEnd_911202 : Nat := 207948710816999622970873

theorem tailTrace_911202 : CollatzResearch.WordTrace tailWord_911202 prefixEnd_911202 207948710816999622970873 := by
  unfold tailWord_911202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8308566811219562439273965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22156178163252166504730573 8308566811219562439273965)
  ·
    refine ⟨3115712554207335914727737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8308566811219562439273965 3115712554207335914727737)
    ·
      refine ⟨2336784415655501936045803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3115712554207335914727737 2336784415655501936045803)
      ·
        refine ⟨3505176623483252904068705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336784415655501936045803 3505176623483252904068705)
        ·
          refine ⟨2628882467612439678051529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3505176623483252904068705 2628882467612439678051529)
          ·
            refine ⟨1971661850709329758538647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2628882467612439678051529 1971661850709329758538647)
            ·
              refine ⟨2957492776063994637807971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971661850709329758538647 2957492776063994637807971)
              ·
                refine ⟨4436239164095991956711957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957492776063994637807971 4436239164095991956711957)
                ·
                  refine ⟨207948710816999622970873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4436239164095991956711957 207948710816999622970873)
                  ·
                    rfl

theorem cell21_911202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_911202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911202 prefixEnd_911202 := by exact prefixLift 911202
  have htrace : WordTrace (prefixWord ++ tailWord_911202) baseStart_911202 baseEnd_911202 := by
    simpa [prefixWord, tailWord_911202, baseEnd_911202] using wordTrace_append hprefix tailTrace_911202
  have hstable : (prefixWord ++ tailWord_911202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911202).length < 2 ^ (prefixWord ++ tailWord_911202).sum := by decide
  have hdescent : baseEnd_911202 < baseStart_911202 := by decide
  rcases family_descends (prefixWord ++ tailWord_911202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911233 : List Nat := [1, 2, 4, 4, 1, 1, 1, 7]
def baseStart_911233 : Nat := 118140960795 + 911233 * 2 ^ 59
def prefixEnd_911233 : Nat := 4983230072969 + 3 ^ 40 * 911233 * 2
def baseEnd_911233 : Nat := 69318595146450152651381

theorem tailTrace_911233 : CollatzResearch.WordTrace tailWord_911233 prefixEnd_911233 69318595146450152651381 := by
  unfold tailWord_911233
  simp only [CollatzResearch.WordTrace]
  refine ⟨33235397907765942051474353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22156931938510628034316235 33235397907765942051474353)
  ·
    refine ⟨24926548430824456538605765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33235397907765942051474353 24926548430824456538605765)
    ·
      refine ⟨4673727830779585600988581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24926548430824456538605765 4673727830779585600988581)
      ·
        refine ⟨876323968271172300185359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4673727830779585600988581 876323968271172300185359)
        ·
          refine ⟨1314485952406758450278039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876323968271172300185359 1314485952406758450278039)
          ·
            refine ⟨1971728928610137675417059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314485952406758450278039 1971728928610137675417059)
            ·
              refine ⟨2957593392915206513125589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971728928610137675417059 2957593392915206513125589)
              ·
                refine ⟨69318595146450152651381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2957593392915206513125589 69318595146450152651381)
                ·
                  rfl

theorem cell21_911233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 7].length) (baseStart_911233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911233 prefixEnd_911233 := by exact prefixLift 911233
  have htrace : WordTrace (prefixWord ++ tailWord_911233) baseStart_911233 baseEnd_911233 := by
    simpa [prefixWord, tailWord_911233, baseEnd_911233] using wordTrace_append hprefix tailTrace_911233
  have hstable : (prefixWord ++ tailWord_911233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911233).length < 2 ^ (prefixWord ++ tailWord_911233).sum := by decide
  have hdescent : baseEnd_911233 < baseStart_911233 := by decide
  rcases family_descends (prefixWord ++ tailWord_911233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911261 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 6]
def baseStart_911261 : Nat := 118140960795 + 911261 * 2 ^ 59
def prefixEnd_911261 : Nat := 4983230072969 + 3 ^ 40 * 911261 * 2
def baseEnd_911261 : Nat := 207962175420828631487419

theorem tailTrace_911261 : CollatzResearch.WordTrace tailWord_911261 prefixEnd_911261 207962175420828631487419 := by
  unfold tailWord_911261
  simp only [CollatzResearch.WordTrace]
  refine ⟨33236419151664502833493637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22157612767776335222329091 33236419151664502833493637)
  ·
    refine ⟨6231828590937094281280057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33236419151664502833493637 6231828590937094281280057)
    ·
      refine ⟨4673871443202820710960043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6231828590937094281280057 4673871443202820710960043)
      ·
        refine ⟨7010807164804231066440065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4673871443202820710960043 7010807164804231066440065)
        ·
          refine ⟨5258105373603173299830049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7010807164804231066440065 5258105373603173299830049)
          ·
            refine ⟨3943579030202379974872537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5258105373603173299830049 3943579030202379974872537)
            ·
              refine ⟨2957684272651784981154403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3943579030202379974872537 2957684272651784981154403)
              ·
                refine ⟨4436526408977677471731605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957684272651784981154403 4436526408977677471731605)
                ·
                  refine ⟨207962175420828631487419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4436526408977677471731605 207962175420828631487419)
                  ·
                    rfl

theorem cell21_911261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_911261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911261 prefixEnd_911261 := by exact prefixLift 911261
  have htrace : WordTrace (prefixWord ++ tailWord_911261) baseStart_911261 baseEnd_911261 := by
    simpa [prefixWord, tailWord_911261, baseEnd_911261] using wordTrace_append hprefix tailTrace_911261
  have hstable : (prefixWord ++ tailWord_911261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911261).length < 2 ^ (prefixWord ++ tailWord_911261).sum := by decide
  have hdescent : baseEnd_911261 < baseStart_911261 := by decide
  rcases family_descends (prefixWord ++ tailWord_911261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911430 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_911430 : Nat := 118140960795 + 911430 * 2 ^ 59
def prefixEnd_911430 : Nat := 4983230072969 + 3 ^ 40 * 911430 * 2
def baseEnd_911430 : Nat := 208000743523321893170407

theorem tailTrace_911430 : CollatzResearch.WordTrace tailWord_911430 prefixEnd_911430 208000743523321893170407 := by
  unfold tailWord_911430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1038830721501632646762367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22161722058701496464263829 1038830721501632646762367)
  ·
    refine ⟨1558246082252448970143551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1038830721501632646762367 1558246082252448970143551)
    ·
      refine ⟨2337369123378673455215327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1558246082252448970143551 2337369123378673455215327)
      ·
        refine ⟨3506053685068010182822991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2337369123378673455215327 3506053685068010182822991)
        ·
          refine ⟨5259080527602015274234487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3506053685068010182822991 5259080527602015274234487)
          ·
            refine ⟨7888620791403022911351731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5259080527602015274234487 7888620791403022911351731)
            ·
              refine ⟨11832931187104534367027597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7888620791403022911351731 11832931187104534367027597)
              ·
                refine ⟨4437349195164200387635349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11832931187104534367027597 4437349195164200387635349)
                ·
                  refine ⟨208000743523321893170407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4437349195164200387635349 208000743523321893170407)
                  ·
                    rfl

theorem cell21_911430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_911430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911430 prefixEnd_911430 := by exact prefixLift 911430
  have htrace : WordTrace (prefixWord ++ tailWord_911430) baseStart_911430 baseEnd_911430 := by
    simpa [prefixWord, tailWord_911430, baseEnd_911430] using wordTrace_append hprefix tailTrace_911430
  have hstable : (prefixWord ++ tailWord_911430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911430).length < 2 ^ (prefixWord ++ tailWord_911430).sum := by decide
  have hdescent : baseEnd_911430 < baseStart_911430 := by decide
  rcases family_descends (prefixWord ++ tailWord_911430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911520 : List Nat := [2, 1, 1, 4, 2, 3, 3, 5]
def baseStart_911520 : Nat := 118140960795 + 911520 * 2 ^ 59
def prefixEnd_911520 : Nat := 4983230072969 + 3 ^ 40 * 911520 * 2
def baseEnd_911520 : Nat := 69340427583167245556741

theorem tailTrace_911520 : CollatzResearch.WordTrace tailWord_911520 prefixEnd_911520 69340427583167245556741 := by
  unfold tailWord_911520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16622932828863095033586007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22163910438484126711448009 16622932828863095033586007)
  ·
    refine ⟨24934399243294642550379011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16622932828863095033586007 24934399243294642550379011)
    ·
      refine ⟨37401598864941963825568517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24934399243294642550379011 37401598864941963825568517)
      ·
        refine ⟨7012799787176618217294097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37401598864941963825568517 7012799787176618217294097)
        ·
          refine ⟨5259599840382463662970573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7012799787176618217294097 5259599840382463662970573)
          ·
            refine ⟨1972349940143423873613965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5259599840382463662970573 1972349940143423873613965)
            ·
              refine ⟨739631227553783952605237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1972349940143423873613965 739631227553783952605237)
              ·
                refine ⟨69340427583167245556741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 739631227553783952605237 69340427583167245556741)
                ·
                  rfl

theorem cell21_911520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_911520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911520 prefixEnd_911520 := by exact prefixLift 911520
  have htrace : WordTrace (prefixWord ++ tailWord_911520) baseStart_911520 baseEnd_911520 := by
    simpa [prefixWord, tailWord_911520, baseEnd_911520] using wordTrace_append hprefix tailTrace_911520
  have hstable : (prefixWord ++ tailWord_911520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911520).length < 2 ^ (prefixWord ++ tailWord_911520).sum := by decide
  have hdescent : baseEnd_911520 < baseStart_911520 := by decide
  rcases family_descends (prefixWord ++ tailWord_911520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911540 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 6]
def baseStart_911540 : Nat := 118140960795 + 911540 * 2 ^ 59
def prefixEnd_911540 : Nat := 4983230072969 + 3 ^ 40 * 911540 * 2
def baseEnd_911540 : Nat := 208025847021986146336849

theorem tailTrace_911540 : CollatzResearch.WordTrace tailWord_911540 prefixEnd_911540 208025847021986146336849 := by
  unfold tailWord_911540
  simp only [CollatzResearch.WordTrace]
  refine ⟨16623297558826866741450037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22164396745102488988600049 16623297558826866741450037)
  ·
    refine ⟨1558434146140018757010941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16623297558826866741450037 1558434146140018757010941)
    ·
      refine ⟨584412804802507033879103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1558434146140018757010941 584412804802507033879103)
      ·
        refine ⟨876619207203760550818655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584412804802507033879103 876619207203760550818655)
        ·
          refine ⟨1314928810805640826227983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876619207203760550818655 1314928810805640826227983)
          ·
            refine ⟨1972393216208461239341975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314928810805640826227983 1972393216208461239341975)
            ·
              refine ⟨2958589824312691859012963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972393216208461239341975 2958589824312691859012963)
              ·
                refine ⟨4437884736469037788519445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958589824312691859012963 4437884736469037788519445)
                ·
                  refine ⟨208025847021986146336849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4437884736469037788519445 208025847021986146336849)
                  ·
                    rfl

theorem cell21_911540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_911540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911540 prefixEnd_911540 := by exact prefixLift 911540
  have htrace : WordTrace (prefixWord ++ tailWord_911540) baseStart_911540 baseEnd_911540 := by
    simpa [prefixWord, tailWord_911540, baseEnd_911540] using wordTrace_append hprefix tailTrace_911540
  have hstable : (prefixWord ++ tailWord_911540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911540).length < 2 ^ (prefixWord ++ tailWord_911540).sum := by decide
  have hdescent : baseEnd_911540 < baseStart_911540 := by decide
  rcases family_descends (prefixWord ++ tailWord_911540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911610 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_911610 : Nat := 118140960795 + 911610 * 2 ^ 59
def prefixEnd_911610 : Nat := 4983230072969 + 3 ^ 40 * 911610 * 2
def baseEnd_911610 : Nat := 208041821975681580170039

theorem tailTrace_911610 : CollatzResearch.WordTrace tailWord_911610 prefixEnd_911610 208041821975681580170039 := by
  unfold tailWord_911610
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312287056850033859487071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22166098818266756958632189 8312287056850033859487071)
  ·
    refine ⟨12468430585275050789230607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8312287056850033859487071 12468430585275050789230607)
    ·
      refine ⟨18702645877912576183845911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12468430585275050789230607 18702645877912576183845911)
      ·
        refine ⟨28053968816868864275768867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18702645877912576183845911 28053968816868864275768867)
        ·
          refine ⟨42080953225303296413653301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28053968816868864275768867 42080953225303296413653301)
          ·
            refine ⟨3945089364872184038779997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42080953225303296413653301 3945089364872184038779997)
            ·
              refine ⟨1479408511827069014542499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3945089364872184038779997 1479408511827069014542499)
              ·
                refine ⟨2219112767740603521813749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479408511827069014542499 2219112767740603521813749)
                ·
                  refine ⟨208041821975681580170039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2219112767740603521813749 208041821975681580170039)
                  ·
                    rfl

theorem cell21_911610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_911610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911610 prefixEnd_911610 := by exact prefixLift 911610
  have htrace : WordTrace (prefixWord ++ tailWord_911610) baseStart_911610 baseEnd_911610 := by
    simpa [prefixWord, tailWord_911610, baseEnd_911610] using wordTrace_append hprefix tailTrace_911610
  have hstable : (prefixWord ++ tailWord_911610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911610).length < 2 ^ (prefixWord ++ tailWord_911610).sum := by decide
  have hdescent : baseEnd_911610 < baseStart_911610 := by decide
  rcases family_descends (prefixWord ++ tailWord_911610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911661 : List Nat := [1, 5, 3, 1, 2, 1, 1, 4, 3]
def baseStart_911661 : Nat := 118140960795 + 911661 * 2 ^ 59
def prefixEnd_911661 : Nat := 4983230072969 + 3 ^ 40 * 911661 * 2
def baseEnd_911661 : Nat := 208053460870516824819935

theorem tailTrace_911661 : CollatzResearch.WordTrace tailWord_911661 prefixEnd_911661 208053460870516824819935 := by
  unfold tailWord_911661
  simp only [CollatzResearch.WordTrace]
  refine ⟨33251008350215371148054837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22167338900143580765369891 33251008350215371148054837)
  ·
    refine ⟨3117282032832691045130141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33251008350215371148054837 3117282032832691045130141)
    ·
      refine ⟨1168980762312259141923803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3117282032832691045130141 1168980762312259141923803)
      ·
        refine ⟨1753471143468388712885705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168980762312259141923803 1753471143468388712885705)
        ·
          refine ⟨1315103357601291534664279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753471143468388712885705 1315103357601291534664279)
          ·
            refine ⟨1972655036401937301996419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315103357601291534664279 1972655036401937301996419)
            ·
              refine ⟨2958982554602905952994629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972655036401937301996419 2958982554602905952994629)
              ·
                refine ⟨554809228988044866186493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2958982554602905952994629 554809228988044866186493)
                ·
                  refine ⟨208053460870516824819935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554809228988044866186493 208053460870516824819935)
                  ·
                    rfl

theorem cell21_911661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_911661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911661 prefixEnd_911661 := by exact prefixLift 911661
  have htrace : WordTrace (prefixWord ++ tailWord_911661) baseStart_911661 baseEnd_911661 := by
    simpa [prefixWord, tailWord_911661, baseEnd_911661] using wordTrace_append hprefix tailTrace_911661
  have hstable : (prefixWord ++ tailWord_911661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911661).length < 2 ^ (prefixWord ++ tailWord_911661).sum := by decide
  have hdescent : baseEnd_911661 < baseStart_911661 := by decide
  rcases family_descends (prefixWord ++ tailWord_911661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911703 : List Nat := [1, 1, 3, 2, 3, 1, 4, 3, 3]
def baseStart_911703 : Nat := 118140960795 + 911703 * 2 ^ 59
def prefixEnd_911703 : Nat := 4983230072969 + 3 ^ 40 * 911703 * 2
def baseEnd_911703 : Nat := 208063045842734085119849

theorem tailTrace_911703 : CollatzResearch.WordTrace tailWord_911703 prefixEnd_911703 208063045842734085119849 := by
  unfold tailWord_911703
  simp only [CollatzResearch.WordTrace]
  refine ⟨33252540216063212321083763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22168360144042141547389175 33252540216063212321083763)
  ·
    refine ⟨49878810324094818481625645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33252540216063212321083763 49878810324094818481625645)
    ·
      refine ⟨18704553871535556930609617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49878810324094818481625645 18704553871535556930609617)
      ·
        refine ⟨14028415403651667697957213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18704553871535556930609617 14028415403651667697957213)
        ·
          refine ⟨5260655776369375386733955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14028415403651667697957213 5260655776369375386733955)
          ·
            refine ⟨7890983664554063080100933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260655776369375386733955 7890983664554063080100933)
            ·
              refine ⟨1479559437103886827518925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7890983664554063080100933 1479559437103886827518925)
              ·
                refine ⟨554834788913957560319597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479559437103886827518925 554834788913957560319597)
                ·
                  refine ⟨208063045842734085119849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554834788913957560319597 208063045842734085119849)
                  ·
                    rfl

theorem cell21_911703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 3].length) (baseStart_911703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911703 prefixEnd_911703 := by exact prefixLift 911703
  have htrace : WordTrace (prefixWord ++ tailWord_911703) baseStart_911703 baseEnd_911703 := by
    simpa [prefixWord, tailWord_911703, baseEnd_911703] using wordTrace_append hprefix tailTrace_911703
  have hstable : (prefixWord ++ tailWord_911703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911703).length < 2 ^ (prefixWord ++ tailWord_911703).sum := by decide
  have hdescent : baseEnd_911703 < baseStart_911703 := by decide
  rcases family_descends (prefixWord ++ tailWord_911703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911717 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 4]
def baseStart_911717 : Nat := 118140960795 + 911717 * 2 ^ 59
def prefixEnd_911717 : Nat := 4983230072969 + 3 ^ 40 * 911717 * 2
def baseEnd_911717 : Nat := 208066240833473171886487

theorem tailTrace_911717 : CollatzResearch.WordTrace tailWord_911717 prefixEnd_911717 208066240833473171886487 := by
  unfold tailWord_911717
  simp only [CollatzResearch.WordTrace]
  refine ⟨33253050838012492712093405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22168700558674995141395603 33253050838012492712093405)
  ·
    refine ⟨12469894064254684767035027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33253050838012492712093405 12469894064254684767035027)
    ·
      refine ⟨18704841096382027150552541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12469894064254684767035027 18704841096382027150552541)
      ·
        refine ⟨7014315411143260181457203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18704841096382027150552541 7014315411143260181457203)
        ·
          refine ⟨10521473116714890272185805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7014315411143260181457203 10521473116714890272185805)
          ·
            refine ⟨3945552418768083852069677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10521473116714890272185805 3945552418768083852069677)
            ·
              refine ⟨1479582157038031444526129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3945552418768083852069677 1479582157038031444526129)
              ·
                refine ⟨1109686617778523583394597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1479582157038031444526129 1109686617778523583394597)
                ·
                  refine ⟨208066240833473171886487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1109686617778523583394597 208066240833473171886487)
                  ·
                    rfl

theorem cell21_911717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_911717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911717 prefixEnd_911717 := by exact prefixLift 911717
  have htrace : WordTrace (prefixWord ++ tailWord_911717) baseStart_911717 baseEnd_911717 := by
    simpa [prefixWord, tailWord_911717, baseEnd_911717] using wordTrace_append hprefix tailTrace_911717
  have hstable : (prefixWord ++ tailWord_911717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911717).length < 2 ^ (prefixWord ++ tailWord_911717).sum := by decide
  have hdescent : baseEnd_911717 < baseStart_911717 := by decide
  rcases family_descends (prefixWord ++ tailWord_911717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911754 : List Nat := [3, 1, 2, 5, 2, 1, 1, 3, 3]
def baseStart_911754 : Nat := 118140960795 + 911754 * 2 ^ 59
def prefixEnd_911754 : Nat := 4983230072969 + 3 ^ 40 * 911754 * 2
def baseEnd_911754 : Nat := 208074684737569329769745

theorem tailTrace_911754 : CollatzResearch.WordTrace tailWord_911754 prefixEnd_911754 208074684737569329769745 := by
  unfold tailWord_911754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8313600084719612007797579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22169600225918965354126877 8313600084719612007797579)
  ·
    refine ⟨12470400127079418011696369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8313600084719612007797579 12470400127079418011696369)
    ·
      refine ⟨9352800095309563508772277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12470400127079418011696369 9352800095309563508772277)
      ·
        refine ⟨876825008935271578947401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9352800095309563508772277 876825008935271578947401)
        ·
          refine ⟨657618756701453684210551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876825008935271578947401 657618756701453684210551)
          ·
            refine ⟨986428135052180526315827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657618756701453684210551 986428135052180526315827)
            ·
              refine ⟨1479642202578270789473741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986428135052180526315827 1479642202578270789473741)
              ·
                refine ⟨554865825966851546052653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479642202578270789473741 554865825966851546052653)
                ·
                  refine ⟨208074684737569329769745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554865825966851546052653 208074684737569329769745)
                  ·
                    rfl

theorem cell21_911754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_911754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911754 prefixEnd_911754 := by exact prefixLift 911754
  have htrace : WordTrace (prefixWord ++ tailWord_911754) baseStart_911754 baseEnd_911754 := by
    simpa [prefixWord, tailWord_911754, baseEnd_911754] using wordTrace_append hprefix tailTrace_911754
  have hstable : (prefixWord ++ tailWord_911754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911754).length < 2 ^ (prefixWord ++ tailWord_911754).sum := by decide
  have hdescent : baseEnd_911754 < baseStart_911754 := by decide
  rcases family_descends (prefixWord ++ tailWord_911754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911776 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_911776 : Nat := 118140960795 + 911776 * 2 ^ 59
def prefixEnd_911776 : Nat := 4983230072969 + 3 ^ 40 * 911776 * 2
def baseEnd_911776 : Nat := 208079705437302180403033

theorem tailTrace_911776 : CollatzResearch.WordTrace tailWord_911776 prefixEnd_911776 208079705437302180403033 := by
  unfold tailWord_911776
  simp only [CollatzResearch.WordTrace]
  refine ⟨16627601372399372894245591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22170135163199163858994121 16627601372399372894245591)
  ·
    refine ⟨24941402058599059341368387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16627601372399372894245591 24941402058599059341368387)
    ·
      refine ⟨37412103087898589012052581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24941402058599059341368387 37412103087898589012052581)
      ·
        refine ⟨7014769328980985439759859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37412103087898589012052581 7014769328980985439759859)
        ·
          refine ⟨10522153993471478159639789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7014769328980985439759859 10522153993471478159639789)
          ·
            refine ⟨3945807747551804309864921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10522153993471478159639789 3945807747551804309864921)
            ·
              refine ⟨2959355810663853232398691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3945807747551804309864921 2959355810663853232398691)
              ·
                refine ⟨4439033715995779848598037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2959355810663853232398691 4439033715995779848598037)
                ·
                  refine ⟨208079705437302180403033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4439033715995779848598037 208079705437302180403033)
                  ·
                    rfl

theorem cell21_911776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_911776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911776 prefixEnd_911776 := by exact prefixLift 911776
  have htrace : WordTrace (prefixWord ++ tailWord_911776) baseStart_911776 baseEnd_911776 := by
    simpa [prefixWord, tailWord_911776, baseEnd_911776] using wordTrace_append hprefix tailTrace_911776
  have hstable : (prefixWord ++ tailWord_911776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911776).length < 2 ^ (prefixWord ++ tailWord_911776).sum := by decide
  have hdescent : baseEnd_911776 < baseStart_911776 := by decide
  rcases family_descends (prefixWord ++ tailWord_911776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911793 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 4]
def baseStart_911793 : Nat := 118140960795 + 911793 * 2 ^ 59
def prefixEnd_911793 : Nat := 4983230072969 + 3 ^ 40 * 911793 * 2
def baseEnd_911793 : Nat := 208083585068913928619665

theorem tailTrace_911793 : CollatzResearch.WordTrace tailWord_911793 prefixEnd_911793 208083585068913928619665 := by
  unfold tailWord_911793
  simp only [CollatzResearch.WordTrace]
  refine ⟨33255822785737157691860033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22170548523824771794573355 33255822785737157691860033)
  ·
    refine ⟨24941867089302868268895025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33255822785737157691860033 24941867089302868268895025)
    ·
      refine ⟨18706400316977151201671269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24941867089302868268895025 18706400316977151201671269)
      ·
        refine ⟨3507450059433215850313363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18706400316977151201671269 3507450059433215850313363)
        ·
          refine ⟨5261175089149823775470045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507450059433215850313363 5261175089149823775470045)
          ·
            refine ⟨1972940658431183915801267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5261175089149823775470045 1972940658431183915801267)
            ·
              refine ⟨2959410987646775873701901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972940658431183915801267 2959410987646775873701901)
              ·
                refine ⟨1109779120367540952638213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2959410987646775873701901 1109779120367540952638213)
                ·
                  refine ⟨208083585068913928619665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1109779120367540952638213 208083585068913928619665)
                  ·
                    rfl

theorem cell21_911793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_911793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911793 prefixEnd_911793 := by exact prefixLift 911793
  have htrace : WordTrace (prefixWord ++ tailWord_911793) baseStart_911793 baseEnd_911793 := by
    simpa [prefixWord, tailWord_911793, baseEnd_911793] using wordTrace_append hprefix tailTrace_911793
  have hstable : (prefixWord ++ tailWord_911793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911793).length < 2 ^ (prefixWord ++ tailWord_911793).sum := by decide
  have hdescent : baseEnd_911793 < baseStart_911793 := by decide
  rcases family_descends (prefixWord ++ tailWord_911793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911852 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 4]
def baseStart_911852 : Nat := 118140960795 + 911852 * 2 ^ 59
def prefixEnd_911852 : Nat := 4983230072969 + 3 ^ 40 * 911852 * 2
def baseEnd_911852 : Nat := 208097049672742937136211

theorem tailTrace_911852 : CollatzResearch.WordTrace tailWord_911852 prefixEnd_911852 208097049672742937136211 := by
  unfold tailWord_911852
  simp only [CollatzResearch.WordTrace]
  refine ⟨16628987346261705384128905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22171983128348940512171873 16628987346261705384128905)
  ·
    refine ⟨12471740509696279038096679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16628987346261705384128905 12471740509696279038096679)
    ·
      refine ⟨18707610764544418557145019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12471740509696279038096679 18707610764544418557145019)
      ·
        refine ⟨28061416146816627835717529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18707610764544418557145019 28061416146816627835717529)
        ·
          refine ⟨21046062110112470876788147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28061416146816627835717529 21046062110112470876788147)
          ·
            refine ⟨31569093165168706315182221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21046062110112470876788147 31569093165168706315182221)
            ·
              refine ⟨11838409936938264868193333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31569093165168706315182221 11838409936938264868193333)
              ·
                refine ⟨1109850931587962331393125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11838409936938264868193333 1109850931587962331393125)
                ·
                  refine ⟨208097049672742937136211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1109850931587962331393125 208097049672742937136211)
                  ·
                    rfl

theorem cell21_911852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_911852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911852 prefixEnd_911852 := by exact prefixLift 911852
  have htrace : WordTrace (prefixWord ++ tailWord_911852) baseStart_911852 baseEnd_911852 := by
    simpa [prefixWord, tailWord_911852, baseEnd_911852] using wordTrace_append hprefix tailTrace_911852
  have hstable : (prefixWord ++ tailWord_911852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911852).length < 2 ^ (prefixWord ++ tailWord_911852).sum := by decide
  have hdescent : baseEnd_911852 < baseStart_911852 := by decide
  rcases family_descends (prefixWord ++ tailWord_911852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911886 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_911886 : Nat := 118140960795 + 911886 * 2 ^ 59
def prefixEnd_911886 : Nat := 4983230072969 + 3 ^ 40 * 911886 * 2
def baseEnd_911886 : Nat := 208104808935966433569475

theorem tailTrace_911886 : CollatzResearch.WordTrace tailWord_911886 prefixEnd_911886 208104808935966433569475 := by
  unfold tailWord_911886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4157401846800029321874439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22172809849600156383330341 4157401846800029321874439)
  ·
    refine ⟨6236102770200043982811659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4157401846800029321874439 6236102770200043982811659)
    ·
      refine ⟨9354154155300065974217489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6236102770200043982811659 9354154155300065974217489)
      ·
        refine ⟨7015615616475049480663117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9354154155300065974217489 7015615616475049480663117)
        ·
          refine ⟨2630855856178143555248669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7015615616475049480663117 2630855856178143555248669)
          ·
            refine ⟨986570946066803833218251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2630855856178143555248669 986570946066803833218251)
            ·
              refine ⟨1479856419100205749827377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986570946066803833218251 1479856419100205749827377)
              ·
                refine ⟨1109892314325154312370533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1479856419100205749827377 1109892314325154312370533)
                ·
                  refine ⟨208104808935966433569475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1109892314325154312370533 208104808935966433569475)
                  ·
                    rfl

theorem cell21_911886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_911886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911886 prefixEnd_911886 := by exact prefixLift 911886
  have htrace : WordTrace (prefixWord ++ tailWord_911886) baseStart_911886 baseEnd_911886 := by
    simpa [prefixWord, tailWord_911886, baseEnd_911886] using wordTrace_append hprefix tailTrace_911886
  have hstable : (prefixWord ++ tailWord_911886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911886).length < 2 ^ (prefixWord ++ tailWord_911886).sum := by decide
  have hdescent : baseEnd_911886 < baseStart_911886 := by decide
  rcases family_descends (prefixWord ++ tailWord_911886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911914 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_911914 : Nat := 118140960795 + 911914 * 2 ^ 59
def prefixEnd_911914 : Nat := 4983230072969 + 3 ^ 40 * 911914 * 2
def baseEnd_911914 : Nat := 208111198917444607102751

theorem tailTrace_911914 : CollatzResearch.WordTrace tailWord_911914 prefixEnd_911914 208111198917444607102751 := by
  unfold tailWord_911914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8315059004574698839253699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22173490678865863571343197 8315059004574698839253699)
  ·
    refine ⟨12472588506862048258880549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8315059004574698839253699 12472588506862048258880549)
    ·
      refine ⟨2338610345036634048540103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12472588506862048258880549 2338610345036634048540103)
      ·
        refine ⟨3507915517554951072810155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2338610345036634048540103 3507915517554951072810155)
        ·
          refine ⟨5261873276332426609215233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507915517554951072810155 5261873276332426609215233)
          ·
            refine ⟨3946404957249319956911425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5261873276332426609215233 3946404957249319956911425)
            ·
              refine ⟨2959803717936989967683569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3946404957249319956911425 2959803717936989967683569)
              ·
                refine ⟨2219852788452742475762677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2959803717936989967683569 2219852788452742475762677)
                ·
                  refine ⟨208111198917444607102751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2219852788452742475762677 208111198917444607102751)
                  ·
                    rfl

theorem cell21_911914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_911914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911914 prefixEnd_911914 := by exact prefixLift 911914
  have htrace : WordTrace (prefixWord ++ tailWord_911914) baseStart_911914 baseEnd_911914 := by
    simpa [prefixWord, tailWord_911914, baseEnd_911914] using wordTrace_append hprefix tailTrace_911914
  have hstable : (prefixWord ++ tailWord_911914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911914).length < 2 ^ (prefixWord ++ tailWord_911914).sum := by decide
  have hdescent : baseEnd_911914 < baseStart_911914 := by decide
  rcases family_descends (prefixWord ++ tailWord_911914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911987 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 6]
def baseStart_911987 : Nat := 118140960795 + 911987 * 2 ^ 59
def prefixEnd_911987 : Nat := 4983230072969 + 3 ^ 40 * 911987 * 2
def baseEnd_911987 : Nat := 208127858512012702385935

theorem tailTrace_911987 : CollatzResearch.WordTrace tailWord_911987 prefixEnd_911987 208127858512012702385935 := by
  unfold tailWord_911987
  simp only [CollatzResearch.WordTrace]
  refine ⟨33262898547034328824422215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22175265698022885882948143 33262898547034328824422215)
  ·
    refine ⟨49894347820551493236633323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33262898547034328824422215 49894347820551493236633323)
    ·
      refine ⟨74841521730827239854949985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49894347820551493236633323 74841521730827239854949985)
      ·
        refine ⟨56131141298120429891212489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74841521730827239854949985 56131141298120429891212489)
        ·
          refine ⟨42098355973590322418409367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56131141298120429891212489 42098355973590322418409367)
          ·
            refine ⟨63147533960385483627614051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42098355973590322418409367 63147533960385483627614051)
            ·
              refine ⟨94721300940578225441421077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63147533960385483627614051 94721300940578225441421077)
              ·
                refine ⟨4440060981589604317566613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94721300940578225441421077 4440060981589604317566613)
                ·
                  refine ⟨208127858512012702385935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4440060981589604317566613 208127858512012702385935)
                  ·
                    rfl

theorem cell21_911987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_911987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_911987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_911987 prefixEnd_911987 := by exact prefixLift 911987
  have htrace : WordTrace (prefixWord ++ tailWord_911987) baseStart_911987 baseEnd_911987 := by
    simpa [prefixWord, tailWord_911987, baseEnd_911987] using wordTrace_append hprefix tailTrace_911987
  have hstable : (prefixWord ++ tailWord_911987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911987).length < 2 ^ (prefixWord ++ tailWord_911987).sum := by decide
  have hdescent : baseEnd_911987 < baseStart_911987 := by decide
  rcases family_descends (prefixWord ++ tailWord_911987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912117 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 5]
def baseStart_912117 : Nat := 118140960795 + 912117 * 2 ^ 59
def prefixEnd_912117 : Nat := 4983230072969 + 3 ^ 40 * 912117 * 2
def baseEnd_912117 : Nat := 208157526283161365219003

theorem tailTrace_912117 : CollatzResearch.WordTrace tailWord_912117 prefixEnd_912117 208157526283161365219003 := by
  unfold tailWord_912117
  simp only [CollatzResearch.WordTrace]
  refine ⟨33267640036563361026654605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22178426691042240684436403 33267640036563361026654605)
  ·
    refine ⟨12475365013711260384995477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33267640036563361026654605 12475365013711260384995477)
    ·
      refine ⟨584782735017715330546663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12475365013711260384995477 584782735017715330546663)
      ·
        refine ⟨877174102526572995819995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584782735017715330546663 877174102526572995819995)
        ·
          refine ⟨1315761153789859493729993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877174102526572995819995 1315761153789859493729993)
          ·
            refine ⟨986820865342394620297495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1315761153789859493729993 986820865342394620297495)
            ·
              refine ⟨1480231298013591930446243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986820865342394620297495 1480231298013591930446243)
              ·
                refine ⟨2220346947020387895669365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480231298013591930446243 2220346947020387895669365)
                ·
                  refine ⟨208157526283161365219003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2220346947020387895669365 208157526283161365219003)
                  ·
                    rfl

theorem cell21_912117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_912117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912117 prefixEnd_912117 := by exact prefixLift 912117
  have htrace : WordTrace (prefixWord ++ tailWord_912117) baseStart_912117 baseEnd_912117 := by
    simpa [prefixWord, tailWord_912117, baseEnd_912117] using wordTrace_append hprefix tailTrace_912117
  have hstable : (prefixWord ++ tailWord_912117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912117).length < 2 ^ (prefixWord ++ tailWord_912117).sum := by decide
  have hdescent : baseEnd_912117 < baseStart_912117 := by decide
  rcases family_descends (prefixWord ++ tailWord_912117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912201 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 5]
def baseStart_912201 : Nat := 118140960795 + 912201 * 2 ^ 59
def prefixEnd_912201 : Nat := 4983230072969 + 3 ^ 40 * 912201 * 2
def baseEnd_912201 : Nat := 208176696227595885818831

theorem tailTrace_912201 : CollatzResearch.WordTrace tailWord_912201 prefixEnd_912201 208176696227595885818831 := by
  unfold tailWord_912201
  simp only [CollatzResearch.WordTrace]
  refine ⟨33270703768259043372712457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22180469178839362248474971 33270703768259043372712457)
  ·
    refine ⟨24953027826194282529534343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33270703768259043372712457 24953027826194282529534343)
    ·
      refine ⟨37429541739291423794301515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24953027826194282529534343 37429541739291423794301515)
      ·
        refine ⟨56144312608937135691452273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37429541739291423794301515 56144312608937135691452273)
        ·
          refine ⟨42108234456702851768589205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56144312608937135691452273 42108234456702851768589205)
          ·
            refine ⟨1973823490157946176652619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42108234456702851768589205 1973823490157946176652619)
            ·
              refine ⟨2960735235236919264978929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973823490157946176652619 2960735235236919264978929)
              ·
                refine ⟨2220551426427689448734197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2960735235236919264978929 2220551426427689448734197)
                ·
                  refine ⟨208176696227595885818831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2220551426427689448734197 208176696227595885818831)
                  ·
                    rfl

theorem cell21_912201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_912201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912201 prefixEnd_912201 := by exact prefixLift 912201
  have htrace : WordTrace (prefixWord ++ tailWord_912201) baseStart_912201 baseEnd_912201 := by
    simpa [prefixWord, tailWord_912201, baseEnd_912201] using wordTrace_append hprefix tailTrace_912201
  have hstable : (prefixWord ++ tailWord_912201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912201).length < 2 ^ (prefixWord ++ tailWord_912201).sum := by decide
  have hdescent : baseEnd_912201 < baseStart_912201 := by decide
  rcases family_descends (prefixWord ++ tailWord_912201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912218 : List Nat := [3, 1, 1, 2, 1, 4, 1, 5, 3]
def baseStart_912218 : Nat := 118140960795 + 912218 * 2 ^ 59
def prefixEnd_912218 : Nat := 4983230072969 + 3 ^ 40 * 912218 * 2
def baseEnd_912218 : Nat := 208180575859207634035463

theorem tailTrace_912218 : CollatzResearch.WordTrace tailWord_912218 prefixEnd_912218 208180575859207634035463 := by
  unfold tailWord_912218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8317830952299363819020327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22180882539464970184054205 8317830952299363819020327)
  ·
    refine ⟨12476746428449045728530491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8317830952299363819020327 12476746428449045728530491)
    ·
      refine ⟨18715119642673568592795737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12476746428449045728530491 18715119642673568592795737)
      ·
        refine ⟨14036339732005176444596803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18715119642673568592795737 14036339732005176444596803)
        ·
          refine ⟨21054509598007764666895205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14036339732005176444596803 21054509598007764666895205)
          ·
            refine ⟨3947720549626455875042851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21054509598007764666895205 3947720549626455875042851)
            ·
              refine ⟨5921580824439683812564277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947720549626455875042851 5921580824439683812564277)
              ·
                refine ⟨555148202291220357427901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5921580824439683812564277 555148202291220357427901)
                ·
                  refine ⟨208180575859207634035463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555148202291220357427901 208180575859207634035463)
                  ·
                    rfl

theorem cell21_912218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_912218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912218 prefixEnd_912218 := by exact prefixLift 912218
  have htrace : WordTrace (prefixWord ++ tailWord_912218) baseStart_912218 baseEnd_912218 := by
    simpa [prefixWord, tailWord_912218, baseEnd_912218] using wordTrace_append hprefix tailTrace_912218
  have hstable : (prefixWord ++ tailWord_912218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912218).length < 2 ^ (prefixWord ++ tailWord_912218).sum := by decide
  have hdescent : baseEnd_912218 < baseStart_912218 := by decide
  rcases family_descends (prefixWord ++ tailWord_912218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912232 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 6]
def baseStart_912232 : Nat := 118140960795 + 912232 * 2 ^ 59
def prefixEnd_912232 : Nat := 4983230072969 + 3 ^ 40 * 912232 * 2
def baseEnd_912232 : Nat := 208183770849946720802101

theorem tailTrace_912232 : CollatzResearch.WordTrace tailWord_912232 prefixEnd_912232 208183770849946720802101 := by
  unfold tailWord_912232
  simp only [CollatzResearch.WordTrace]
  refine ⟨16635917215573367833545475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22181222954097823778060633 16635917215573367833545475)
  ·
    refine ⟨24953875823360051750318213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16635917215573367833545475 24953875823360051750318213)
    ·
      refine ⟨4678851716880009703184665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24953875823360051750318213 4678851716880009703184665)
      ·
        refine ⟨3509138787660007277388499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4678851716880009703184665 3509138787660007277388499)
        ·
          refine ⟨5263708181490010916082749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509138787660007277388499 5263708181490010916082749)
          ·
            refine ⟨1973890568058754093531031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5263708181490010916082749 1973890568058754093531031)
            ·
              refine ⟨2960835852088131140296547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973890568058754093531031 2960835852088131140296547)
              ·
                refine ⟨4441253778132196710444821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960835852088131140296547 4441253778132196710444821)
                ·
                  refine ⟨208183770849946720802101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4441253778132196710444821 208183770849946720802101)
                  ·
                    rfl

theorem cell21_912232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_912232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912232 prefixEnd_912232 := by exact prefixLift 912232
  have htrace : WordTrace (prefixWord ++ tailWord_912232) baseStart_912232 baseEnd_912232 := by
    simpa [prefixWord, tailWord_912232, baseEnd_912232] using wordTrace_append hprefix tailTrace_912232
  have hstable : (prefixWord ++ tailWord_912232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912232).length < 2 ^ (prefixWord ++ tailWord_912232).sum := by decide
  have hdescent : baseEnd_912232 < baseStart_912232 := by decide
  rcases family_descends (prefixWord ++ tailWord_912232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912249 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 4]
def baseStart_912249 : Nat := 118140960795 + 912249 * 2 ^ 59
def prefixEnd_912249 : Nat := 4983230072969 + 3 ^ 40 * 912249 * 2
def baseEnd_912249 : Nat := 208187650481558469018733

theorem tailTrace_912249 : CollatzResearch.WordTrace tailWord_912249 prefixEnd_912249 208187650481558469018733 := by
  unfold tailWord_912249
  simp only [CollatzResearch.WordTrace]
  refine ⟨33272454472085147570459801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22181636314723431713639867 33272454472085147570459801)
  ·
    refine ⟨24954340854063860677844851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33272454472085147570459801 24954340854063860677844851)
    ·
      refine ⟨37431511281095791016767277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24954340854063860677844851 37431511281095791016767277)
      ·
        refine ⟨14036816730410921631287729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37431511281095791016767277 14036816730410921631287729)
        ·
          refine ⟨10527612547808191223465797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14036816730410921631287729 10527612547808191223465797)
          ·
            refine ⟨1973927352714035854399837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10527612547808191223465797 1973927352714035854399837)
            ·
              refine ⟨740222757267763445399939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1973927352714035854399837 740222757267763445399939)
              ·
                refine ⟨1110334135901645168099909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740222757267763445399939 1110334135901645168099909)
                ·
                  refine ⟨208187650481558469018733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110334135901645168099909 208187650481558469018733)
                  ·
                    rfl

theorem cell21_912249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_912249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912249 prefixEnd_912249 := by exact prefixLift 912249
  have htrace : WordTrace (prefixWord ++ tailWord_912249) baseStart_912249 baseEnd_912249 := by
    simpa [prefixWord, tailWord_912249, baseEnd_912249] using wordTrace_append hprefix tailTrace_912249
  have hstable : (prefixWord ++ tailWord_912249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912249).length < 2 ^ (prefixWord ++ tailWord_912249).sum := by decide
  have hdescent : baseEnd_912249 < baseStart_912249 := by decide
  rcases family_descends (prefixWord ++ tailWord_912249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912263 : List Nat := [1, 1, 4, 2, 3, 1, 4, 5]
def baseStart_912263 : Nat := 118140960795 + 912263 * 2 ^ 59
def prefixEnd_912263 : Nat := 4983230072969 + 3 ^ 40 * 912263 * 2
def baseEnd_912263 : Nat := 69396948490765851928457

theorem tailTrace_912263 : CollatzResearch.WordTrace tailWord_912263 prefixEnd_912263 69396948490765851928457 := by
  unfold tailWord_912263
  simp only [CollatzResearch.WordTrace]
  refine ⟨33272965094034427961469443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22181976729356285307646295 33272965094034427961469443)
  ·
    refine ⟨49909447641051641942204165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33272965094034427961469443 49909447641051641942204165)
    ·
      refine ⟨9358021432697182864163281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49909447641051641942204165 9358021432697182864163281)
      ·
        refine ⟨7018516074522887148122461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9358021432697182864163281 7018516074522887148122461)
        ·
          refine ⟨2631943527946082680545923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7018516074522887148122461 2631943527946082680545923)
          ·
            refine ⟨3947915291919124020818885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2631943527946082680545923 3947915291919124020818885)
            ·
              refine ⟨740234117234835753903541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3947915291919124020818885 740234117234835753903541)
              ·
                refine ⟨69396948490765851928457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 740234117234835753903541 69396948490765851928457)
                ·
                  rfl

theorem cell21_912263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 5].length) (baseStart_912263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912263 prefixEnd_912263 := by exact prefixLift 912263
  have htrace : WordTrace (prefixWord ++ tailWord_912263) baseStart_912263 baseEnd_912263 := by
    simpa [prefixWord, tailWord_912263, baseEnd_912263] using wordTrace_append hprefix tailTrace_912263
  have hstable : (prefixWord ++ tailWord_912263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912263).length < 2 ^ (prefixWord ++ tailWord_912263).sum := by decide
  have hdescent : baseEnd_912263 < baseStart_912263 := by decide
  rcases family_descends (prefixWord ++ tailWord_912263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912291 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 6]
def baseStart_912291 : Nat := 118140960795 + 912291 * 2 ^ 59
def prefixEnd_912291 : Nat := 4983230072969 + 3 ^ 40 * 912291 * 2
def baseEnd_912291 : Nat := 208197235453775729318647

theorem tailTrace_912291 : CollatzResearch.WordTrace tailWord_912291 prefixEnd_912291 208197235453775729318647 := by
  unfold tailWord_912291
  simp only [CollatzResearch.WordTrace]
  refine ⟨33273986337932988743488727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22182657558621992495659151 33273986337932988743488727)
  ·
    refine ⟨49910979506899483115233091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33273986337932988743488727 49910979506899483115233091)
    ·
      refine ⟨74866469260349224672849637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49910979506899483115233091 74866469260349224672849637)
      ·
        refine ⟨14037462986315479626159307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74866469260349224672849637 14037462986315479626159307)
        ·
          refine ⟨21056194479473219439238961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14037462986315479626159307 21056194479473219439238961)
          ·
            refine ⟨15792145859604914579429221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21056194479473219439238961 15792145859604914579429221)
            ·
              refine ⟨2961027348675921483642979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15792145859604914579429221 2961027348675921483642979)
              ·
                refine ⟨4441541023013882225464469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961027348675921483642979 4441541023013882225464469)
                ·
                  refine ⟨208197235453775729318647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4441541023013882225464469 208197235453775729318647)
                  ·
                    rfl

theorem cell21_912291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_912291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912291 prefixEnd_912291 := by exact prefixLift 912291
  have htrace : WordTrace (prefixWord ++ tailWord_912291) baseStart_912291 baseEnd_912291 := by
    simpa [prefixWord, tailWord_912291, baseEnd_912291] using wordTrace_append hprefix tailTrace_912291
  have hstable : (prefixWord ++ tailWord_912291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912291).length < 2 ^ (prefixWord ++ tailWord_912291).sum := by decide
  have hdescent : baseEnd_912291 < baseStart_912291 := by decide
  rcases family_descends (prefixWord ++ tailWord_912291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912342 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_912342 : Nat := 118140960795 + 912342 * 2 ^ 59
def prefixEnd_912342 : Nat := 4983230072969 + 3 ^ 40 * 912342 * 2
def baseEnd_912342 : Nat := 208208874348610973968543

theorem tailTrace_912342 : CollatzResearch.WordTrace tailWord_912342 prefixEnd_912342 208208874348610973968543 := by
  unfold tailWord_912342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079740403796764028349705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22183897640498816302396853 2079740403796764028349705)
  ·
    refine ⟨1559805302847573021262279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2079740403796764028349705 1559805302847573021262279)
    ·
      refine ⟨2339707954271359531893419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559805302847573021262279 2339707954271359531893419)
      ·
        refine ⟨3509561931407039297840129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339707954271359531893419 3509561931407039297840129)
        ·
          refine ⟨2632171448555279473380097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3509561931407039297840129 2632171448555279473380097)
          ·
            refine ⟨1974128586416459605035073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2632171448555279473380097 1974128586416459605035073)
            ·
              refine ⟨1480596439812344703776305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1974128586416459605035073 1480596439812344703776305)
              ·
                refine ⟨1110447329859258527832229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480596439812344703776305 1110447329859258527832229)
                ·
                  refine ⟨208208874348610973968543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110447329859258527832229 208208874348610973968543)
                  ·
                    rfl

theorem cell21_912342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_912342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912342 prefixEnd_912342 := by exact prefixLift 912342
  have htrace : WordTrace (prefixWord ++ tailWord_912342) baseStart_912342 baseEnd_912342 := by
    simpa [prefixWord, tailWord_912342, baseEnd_912342] using wordTrace_append hprefix tailTrace_912342
  have hstable : (prefixWord ++ tailWord_912342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912342).length < 2 ^ (prefixWord ++ tailWord_912342).sum := by decide
  have hdescent : baseEnd_912342 < baseStart_912342 := by decide
  rcases family_descends (prefixWord ++ tailWord_912342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912373 : List Nat := [1, 3, 5, 2, 1, 1, 3, 5]
def baseStart_912373 : Nat := 118140960795 + 912373 * 2 ^ 59
def prefixEnd_912373 : Nat := 4983230072969 + 3 ^ 40 * 912373 * 2
def baseEnd_912373 : Nat := 69405316323653936317271

theorem tailTrace_912373 : CollatzResearch.WordTrace tailWord_912373 prefixEnd_912373 69405316323653936317271 := by
  unfold tailWord_912373
  simp only [CollatzResearch.WordTrace]
  refine ⟨33276977123635916747973773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22184651415757277831982515 33276977123635916747973773)
  ·
    refine ⟨12478866421363468780490165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33276977123635916747973773 12478866421363468780490165)
    ·
      refine ⟨1169893727002825198170953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12478866421363468780490165 1169893727002825198170953)
      ·
        refine ⟨877420295252118898628215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1169893727002825198170953 877420295252118898628215)
        ·
          refine ⟨1316130442878178347942323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877420295252118898628215 1316130442878178347942323)
          ·
            refine ⟨1974195664317267521913485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316130442878178347942323 1974195664317267521913485)
            ·
              refine ⟨740323374118975320717557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1974195664317267521913485 740323374118975320717557)
              ·
                refine ⟨69405316323653936317271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 740323374118975320717557 69405316323653936317271)
                ·
                  rfl

theorem cell21_912373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 5].length) (baseStart_912373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912373 prefixEnd_912373 := by exact prefixLift 912373
  have htrace : WordTrace (prefixWord ++ tailWord_912373) baseStart_912373 baseEnd_912373 := by
    simpa [prefixWord, tailWord_912373, baseEnd_912373] using wordTrace_append hprefix tailTrace_912373
  have hstable : (prefixWord ++ tailWord_912373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912373).length < 2 ^ (prefixWord ++ tailWord_912373).sum := by decide
  have hdescent : baseEnd_912373 < baseStart_912373 := by decide
  rcases family_descends (prefixWord ++ tailWord_912373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912398 : List Nat := [4, 1, 1, 2, 2, 3, 8]
def baseStart_912398 : Nat := 118140960795 + 912398 * 2 ^ 59
def prefixEnd_912398 : Nat := 4983230072969 + 3 ^ 40 * 912398 * 2
def baseEnd_912398 : Nat := 23135739367951924559455

theorem tailTrace_912398 : CollatzResearch.WordTrace tailWord_912398 prefixEnd_912398 23135739367951924559455 := by
  unfold tailWord_912398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4159736118568168252204231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22185259299030230678422565 4159736118568168252204231)
  ·
    refine ⟨6239604177852252378306347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4159736118568168252204231 6239604177852252378306347)
    ·
      refine ⟨9359406266778378567459521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6239604177852252378306347 9359406266778378567459521)
      ·
        refine ⟨7019554700083783925594641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9359406266778378567459521 7019554700083783925594641)
        ·
          refine ⟨5264666025062837944195981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7019554700083783925594641 5264666025062837944195981)
          ·
            refine ⟨1974249759398564229073493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5264666025062837944195981 1974249759398564229073493)
            ·
              refine ⟨23135739367951924559455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1974249759398564229073493 23135739367951924559455)
              ·
                rfl

theorem cell21_912398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 8].length) (baseStart_912398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912398 prefixEnd_912398 := by exact prefixLift 912398
  have htrace : WordTrace (prefixWord ++ tailWord_912398) baseStart_912398 baseEnd_912398 := by
    simpa [prefixWord, tailWord_912398, baseEnd_912398] using wordTrace_append hprefix tailTrace_912398
  have hstable : (prefixWord ++ tailWord_912398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912398).length < 2 ^ (prefixWord ++ tailWord_912398).sum := by decide
  have hdescent : baseEnd_912398 < baseStart_912398 := by decide
  rcases family_descends (prefixWord ++ tailWord_912398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912522 : List Nat := [3, 1, 2, 3, 1, 1, 3, 4, 3]
def baseStart_912522 : Nat := 118140960795 + 912522 * 2 ^ 59
def prefixEnd_912522 : Nat := 4983230072969 + 3 ^ 40 * 912522 * 2
def baseEnd_912522 : Nat := 208249952800970660968175

theorem tailTrace_912522 : CollatzResearch.WordTrace tailWord_912522 prefixEnd_912522 208249952800970660968175 := by
  unfold tailWord_912522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8320602900024028798786955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22188274400064076796765213 8320602900024028798786955)
  ·
    refine ⟨12480904350036043198180433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8320602900024028798786955 12480904350036043198180433)
    ·
      refine ⟨9360678262527032398635325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12480904350036043198180433 9360678262527032398635325)
      ·
        refine ⟨3510254348447637149488247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9360678262527032398635325 3510254348447637149488247)
        ·
          refine ⟨5265381522671455724232371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3510254348447637149488247 5265381522671455724232371)
          ·
            refine ⟨7898072284007183586348557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265381522671455724232371 7898072284007183586348557)
            ·
              refine ⟨2961777106502693844880709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7898072284007183586348557 2961777106502693844880709)
              ·
                refine ⟨555333207469255095915133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2961777106502693844880709 555333207469255095915133)
                ·
                  refine ⟨208249952800970660968175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555333207469255095915133 208249952800970660968175)
                  ·
                    rfl

theorem cell21_912522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_912522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912522 prefixEnd_912522 := by exact prefixLift 912522
  have htrace : WordTrace (prefixWord ++ tailWord_912522) baseStart_912522 baseEnd_912522 := by
    simpa [prefixWord, tailWord_912522, baseEnd_912522] using wordTrace_append hprefix tailTrace_912522
  have hstable : (prefixWord ++ tailWord_912522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912522).length < 2 ^ (prefixWord ++ tailWord_912522).sum := by decide
  have hdescent : baseEnd_912522 < baseStart_912522 := by decide
  rcases family_descends (prefixWord ++ tailWord_912522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912533 : List Nat := [1, 3, 2, 1, 1, 1, 2, 10]
def baseStart_912533 : Nat := 118140960795 + 912533 * 2 ^ 59
def prefixEnd_912533 : Nat := 4983230072969 + 3 ^ 40 * 912533 * 2
def baseEnd_912533 : Nat := 69417487716945695428273

theorem tailTrace_912533 : CollatzResearch.WordTrace tailWord_912533 prefixEnd_912533 69417487716945695428273 := by
  unfold tailWord_912533
  simp only [CollatzResearch.WordTrace]
  refine ⟨33282812803056264073798253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22188541868704176049198835 33282812803056264073798253)
  ·
    refine ⟨12481054801146099027674345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33282812803056264073798253 12481054801146099027674345)
    ·
      refine ⟨9360791100859574270755759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12481054801146099027674345 9360791100859574270755759)
      ·
        refine ⟨14041186651289361406133639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9360791100859574270755759 14041186651289361406133639)
        ·
          refine ⟨21061779976934042109200459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14041186651289361406133639 21061779976934042109200459)
          ·
            refine ⟨31592669965401063163800689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21061779976934042109200459 31592669965401063163800689)
            ·
              refine ⟨23694502474050797372850517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31592669965401063163800689 23694502474050797372850517)
              ·
                refine ⟨69417487716945695428273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23694502474050797372850517 69417487716945695428273)
                ·
                  rfl

theorem cell21_912533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 10].length) (baseStart_912533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912533 prefixEnd_912533 := by exact prefixLift 912533
  have htrace : WordTrace (prefixWord ++ tailWord_912533) baseStart_912533 baseEnd_912533 := by
    simpa [prefixWord, tailWord_912533, baseEnd_912533] using wordTrace_append hprefix tailTrace_912533
  have hstable : (prefixWord ++ tailWord_912533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912533).length < 2 ^ (prefixWord ++ tailWord_912533).sum := by decide
  have hdescent : baseEnd_912533 < baseStart_912533 := by decide
  rcases family_descends (prefixWord ++ tailWord_912533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912536 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 4]
def baseStart_912536 : Nat := 118140960795 + 912536 * 2 ^ 59
def prefixEnd_912536 : Nat := 4983230072969 + 3 ^ 40 * 912536 * 2
def baseEnd_912536 : Nat := 208253147791709747734813

theorem tailTrace_912536 : CollatzResearch.WordTrace tailWord_912536 prefixEnd_912536 208253147791709747734813 := by
  unfold tailWord_912536
  simp only [CollatzResearch.WordTrace]
  refine ⟨16641461111022697793078731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22188614814696930390771641 16641461111022697793078731)
  ·
    refine ⟨24962191666534046689618097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16641461111022697793078731 24962191666534046689618097)
    ·
      refine ⟨18721643749900535017213573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24962191666534046689618097 18721643749900535017213573)
      ·
        refine ⟨3510308203106350315727545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18721643749900535017213573 3510308203106350315727545)
        ·
          refine ⟨2632731152329762736795659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3510308203106350315727545 2632731152329762736795659)
          ·
            refine ⟨3949096728494644105193489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632731152329762736795659 3949096728494644105193489)
            ·
              refine ⟨2961822546370983078895117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949096728494644105193489 2961822546370983078895117)
              ·
                refine ⟨1110683454889118654585669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2961822546370983078895117 1110683454889118654585669)
                ·
                  refine ⟨208253147791709747734813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110683454889118654585669 208253147791709747734813)
                  ·
                    rfl

theorem cell21_912536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_912536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912536 prefixEnd_912536 := by exact prefixLift 912536
  have htrace : WordTrace (prefixWord ++ tailWord_912536) baseStart_912536 baseEnd_912536 := by
    simpa [prefixWord, tailWord_912536, baseEnd_912536] using wordTrace_append hprefix tailTrace_912536
  have hstable : (prefixWord ++ tailWord_912536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912536).length < 2 ^ (prefixWord ++ tailWord_912536).sum := by decide
  have hdescent : baseEnd_912536 < baseStart_912536 := by decide
  rcases family_descends (prefixWord ++ tailWord_912536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912691 : List Nat := [1, 1, 1, 2, 5, 4, 2, 2, 3]
def baseStart_912691 : Nat := 118140960795 + 912691 * 2 ^ 59
def prefixEnd_912691 : Nat := 4983230072969 + 3 ^ 40 * 912691 * 2
def baseEnd_912691 : Nat := 208288520903463922651163

theorem tailTrace_912691 : CollatzResearch.WordTrace tailWord_912691 prefixEnd_912691 208288520903463922651163 := by
  unfold tailWord_912691
  simp only [CollatzResearch.WordTrace]
  refine ⟨33288575536483857058049927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22192383690989238038699951 33288575536483857058049927)
  ·
    refine ⟨49932863304725785587074891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33288575536483857058049927 49932863304725785587074891)
    ·
      refine ⟨74899294957088678380612337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49932863304725785587074891 74899294957088678380612337)
      ·
        refine ⟨56174471217816508785459253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74899294957088678380612337 56174471217816508785459253)
        ·
          refine ⟨5266356676670297698636805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56174471217816508785459253 5266356676670297698636805)
          ·
            refine ⟨987441876875680818494401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5266356676670297698636805 987441876875680818494401)
            ·
              refine ⟨740581407656760613870801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987441876875680818494401 740581407656760613870801)
              ·
                refine ⟨555436055742570460403101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740581407656760613870801 555436055742570460403101)
                ·
                  refine ⟨208288520903463922651163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555436055742570460403101 208288520903463922651163)
                  ·
                    rfl

theorem cell21_912691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 3].length) (baseStart_912691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912691 prefixEnd_912691 := by exact prefixLift 912691
  have htrace : WordTrace (prefixWord ++ tailWord_912691) baseStart_912691 baseEnd_912691 := by
    simpa [prefixWord, tailWord_912691, baseEnd_912691] using wordTrace_append hprefix tailTrace_912691
  have hstable : (prefixWord ++ tailWord_912691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912691).length < 2 ^ (prefixWord ++ tailWord_912691).sum := by decide
  have hdescent : baseEnd_912691 < baseStart_912691 := by decide
  rcases family_descends (prefixWord ++ tailWord_912691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912716 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_912716 : Nat := 118140960795 + 912716 * 2 ^ 59
def prefixEnd_912716 : Nat := 4983230072969 + 3 ^ 40 * 912716 * 2
def baseEnd_912716 : Nat := 208294226244069434734445

theorem tailTrace_912716 : CollatzResearch.WordTrace tailWord_912716 prefixEnd_912716 208294226244069434734445 := by
  unfold tailWord_912716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16644743680696643163855001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22192991574262190885140001 16644743680696643163855001)
  ·
    refine ⟨12483557760522482372891251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16644743680696643163855001 12483557760522482372891251)
    ·
      refine ⟨18725336640783723559336877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12483557760522482372891251 18725336640783723559336877)
      ·
        refine ⟨7022001240293896334751329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18725336640783723559336877 7022001240293896334751329)
        ·
          refine ⟨5266500930220422251063497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7022001240293896334751329 5266500930220422251063497)
          ·
            refine ⟨3949875697665316688297623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5266500930220422251063497 3949875697665316688297623)
            ·
              refine ⟨5924813546497975032446435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949875697665316688297623 5924813546497975032446435)
              ·
                refine ⟨8887220319746962548669653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5924813546497975032446435 8887220319746962548669653)
                ·
                  refine ⟨208294226244069434734445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8887220319746962548669653 208294226244069434734445)
                  ·
                    rfl

theorem cell21_912716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_912716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912716 prefixEnd_912716 := by exact prefixLift 912716
  have htrace : WordTrace (prefixWord ++ tailWord_912716) baseStart_912716 baseEnd_912716 := by
    simpa [prefixWord, tailWord_912716, baseEnd_912716] using wordTrace_append hprefix tailTrace_912716
  have hstable : (prefixWord ++ tailWord_912716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912716).length < 2 ^ (prefixWord ++ tailWord_912716).sum := by decide
  have hdescent : baseEnd_912716 < baseStart_912716 := by decide
  rcases family_descends (prefixWord ++ tailWord_912716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912764 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 4]
def baseStart_912764 : Nat := 118140960795 + 912764 * 2 ^ 59
def prefixEnd_912764 : Nat := 4983230072969 + 3 ^ 40 * 912764 * 2
def baseEnd_912764 : Nat := 208305180498032017934347

theorem tailTrace_912764 : CollatzResearch.WordTrace tailWord_912764 prefixEnd_912764 208305180498032017934347 := by
  unfold tailWord_912764
  simp only [CollatzResearch.WordTrace]
  refine ⟨16645619032609695262728673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22194158710146260350304897 16645619032609695262728673)
  ·
    refine ⟨12484214274457271447046505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16645619032609695262728673 12484214274457271447046505)
    ·
      refine ⟨9363160705842953585284879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12484214274457271447046505 9363160705842953585284879)
      ·
        refine ⟨14044741058764430377927319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9363160705842953585284879 14044741058764430377927319)
        ·
          refine ⟨21067111588146645566890979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14044741058764430377927319 21067111588146645566890979)
          ·
            refine ⟨31600667382219968350336469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21067111588146645566890979 31600667382219968350336469)
            ·
              refine ⟨740640641770780508211011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31600667382219968350336469 740640641770780508211011)
              ·
                refine ⟨1110960962656170762316517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740640641770780508211011 1110960962656170762316517)
                ·
                  refine ⟨208305180498032017934347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110960962656170762316517 208305180498032017934347)
                  ·
                    rfl

theorem cell21_912764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_912764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912764 prefixEnd_912764 := by exact prefixLift 912764
  have htrace : WordTrace (prefixWord ++ tailWord_912764) baseStart_912764 baseEnd_912764 := by
    simpa [prefixWord, tailWord_912764, baseEnd_912764] using wordTrace_append hprefix tailTrace_912764
  have hstable : (prefixWord ++ tailWord_912764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912764).length < 2 ^ (prefixWord ++ tailWord_912764).sum := by decide
  have hdescent : baseEnd_912764 < baseStart_912764 := by decide
  rcases family_descends (prefixWord ++ tailWord_912764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912823 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 4]
def baseStart_912823 : Nat := 118140960795 + 912823 * 2 ^ 59
def prefixEnd_912823 : Nat := 4983230072969 + 3 ^ 40 * 912823 * 2
def baseEnd_912823 : Nat := 208318645101861026450893

theorem tailTrace_912823 : CollatzResearch.WordTrace tailWord_912823 prefixEnd_912823 208318645101861026450893 := by
  unfold tailWord_912823
  simp only [CollatzResearch.WordTrace]
  refine ⟨33293389972005643601855123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22195593314670429067903415 33293389972005643601855123)
  ·
    refine ⟨49940084958008465402782685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33293389972005643601855123 49940084958008465402782685)
    ·
      refine ⟨18727531859253174526043507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49940084958008465402782685 18727531859253174526043507)
      ·
        refine ⟨28091297788879761789065261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18727531859253174526043507 28091297788879761789065261)
        ·
          refine ⟨10534236670829910670899473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28091297788879761789065261 10534236670829910670899473)
          ·
            refine ⟨7900677503122433003174605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10534236670829910670899473 7900677503122433003174605)
            ·
              refine ⟨2962754063670912376190477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7900677503122433003174605 2962754063670912376190477)
              ·
                refine ⟨1111032773876592141071429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2962754063670912376190477 1111032773876592141071429)
                ·
                  refine ⟨208318645101861026450893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1111032773876592141071429 208318645101861026450893)
                  ·
                    rfl

theorem cell21_912823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 4].length) (baseStart_912823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912823 prefixEnd_912823 := by exact prefixLift 912823
  have htrace : WordTrace (prefixWord ++ tailWord_912823) baseStart_912823 baseEnd_912823 := by
    simpa [prefixWord, tailWord_912823, baseEnd_912823] using wordTrace_append hprefix tailTrace_912823
  have hstable : (prefixWord ++ tailWord_912823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912823).length < 2 ^ (prefixWord ++ tailWord_912823).sum := by decide
  have hdescent : baseEnd_912823 < baseStart_912823 := by decide
  rcases family_descends (prefixWord ++ tailWord_912823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912854 : List Nat := [5, 2, 1, 1, 1, 11]
def baseStart_912854 : Nat := 118140960795 + 912854 * 2 ^ 59
def prefixEnd_912854 : Nat := 4983230072969 + 3 ^ 40 * 912854 * 2
def baseEnd_912854 : Nat := 7715767397193031904969

theorem tailTrace_912854 : CollatzResearch.WordTrace tailWord_912854 prefixEnd_912854 7715767397193031904969 := by
  unfold tailWord_912854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080907539680833493514601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22196347089928890597489077 2080907539680833493514601)
  ·
    refine ⟨1560680654760625120135951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2080907539680833493514601 1560680654760625120135951)
    ·
      refine ⟨2341020982140937680203927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1560680654760625120135951 2341020982140937680203927)
      ·
        refine ⟨3511531473211406520305891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2341020982140937680203927 3511531473211406520305891)
        ·
          refine ⟨5267297209817109780458837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511531473211406520305891 5267297209817109780458837)
          ·
            refine ⟨7715767397193031904969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5267297209817109780458837 7715767397193031904969)
            ·
              rfl

theorem cell21_912854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 11].length) (baseStart_912854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912854 prefixEnd_912854 := by exact prefixLift 912854
  have htrace : WordTrace (prefixWord ++ tailWord_912854) baseStart_912854 baseEnd_912854 := by
    simpa [prefixWord, tailWord_912854, baseEnd_912854] using wordTrace_append hprefix tailTrace_912854
  have hstable : (prefixWord ++ tailWord_912854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912854).length < 2 ^ (prefixWord ++ tailWord_912854).sum := by decide
  have hdescent : baseEnd_912854 < baseStart_912854 := by decide
  rcases family_descends (prefixWord ++ tailWord_912854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912885 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 7]
def baseStart_912885 : Nat := 118140960795 + 912885 * 2 ^ 59
def prefixEnd_912885 : Nat := 4983230072969 + 3 ^ 40 * 912885 * 2
def baseEnd_912885 : Nat := 208332794346562696417433

theorem tailTrace_912885 : CollatzResearch.WordTrace tailWord_912885 prefixEnd_912885 208332794346562696417433 := by
  unfold tailWord_912885
  simp only [CollatzResearch.WordTrace]
  refine ⟨33295651297781028190612109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22197100865187352127074739 33295651297781028190612109)
  ·
    refine ⟨12485869236667885571479541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33295651297781028190612109 12485869236667885571479541)
    ·
      refine ⟨1170550240937614272326207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12485869236667885571479541 1170550240937614272326207)
      ·
        refine ⟨1755825361406421408489311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170550240937614272326207 1755825361406421408489311)
        ·
          refine ⟨2633738042109632112733967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755825361406421408489311 2633738042109632112733967)
          ·
            refine ⟨3950607063164448169100951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633738042109632112733967 3950607063164448169100951)
            ·
              refine ⟨5925910594746672253651427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3950607063164448169100951 5925910594746672253651427)
              ·
                refine ⟨8888865892120008380477141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925910594746672253651427 8888865892120008380477141)
                ·
                  refine ⟨208332794346562696417433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8888865892120008380477141 208332794346562696417433)
                  ·
                    rfl

theorem cell21_912885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_912885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_912885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_912885 prefixEnd_912885 := by exact prefixLift 912885
  have htrace : WordTrace (prefixWord ++ tailWord_912885) baseStart_912885 baseEnd_912885 := by
    simpa [prefixWord, tailWord_912885, baseEnd_912885] using wordTrace_append hprefix tailTrace_912885
  have hstable : (prefixWord ++ tailWord_912885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912885).length < 2 ^ (prefixWord ++ tailWord_912885).sum := by decide
  have hdescent : baseEnd_912885 < baseStart_912885 := by decide
  rcases family_descends (prefixWord ++ tailWord_912885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913096 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 5]
def baseStart_913096 : Nat := 118140960795 + 913096 * 2 ^ 59
def prefixEnd_913096 : Nat := 4983230072969 + 3 ^ 40 * 913096 * 2
def baseEnd_913096 : Nat := 208380947421273218400335

theorem tailTrace_913096 : CollatzResearch.WordTrace tailWord_913096 prefixEnd_913096 208380947421273218400335 := by
  unfold tailWord_913096
  simp only [CollatzResearch.WordTrace]
  refine ⟨16651673550008305613271571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22202231400011074151028761 16651673550008305613271571)
  ·
    refine ⟨24977510325012458419907357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16651673550008305613271571 24977510325012458419907357)
    ·
      refine ⟨9366566371879671907465259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24977510325012458419907357 9366566371879671907465259)
      ·
        refine ⟨14049849557819507861197889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9366566371879671907465259 14049849557819507861197889)
        ·
          refine ⟨10537387168364630895898417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14049849557819507861197889 10537387168364630895898417)
          ·
            refine ⟨7903040376273473171923813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10537387168364630895898417 7903040376273473171923813)
            ·
              refine ⟨1481820070551276219735715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7903040376273473171923813 1481820070551276219735715)
              ·
                refine ⟨2222730105826914329603573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481820070551276219735715 2222730105826914329603573)
                ·
                  refine ⟨208380947421273218400335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2222730105826914329603573 208380947421273218400335)
                  ·
                    rfl

theorem cell21_913096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_913096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913096 prefixEnd_913096 := by exact prefixLift 913096
  have htrace : WordTrace (prefixWord ++ tailWord_913096) baseStart_913096 baseEnd_913096 := by
    simpa [prefixWord, tailWord_913096, baseEnd_913096] using wordTrace_append hprefix tailTrace_913096
  have hstable : (prefixWord ++ tailWord_913096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913096).length < 2 ^ (prefixWord ++ tailWord_913096).sum := by decide
  have hdescent : baseEnd_913096 < baseStart_913096 := by decide
  rcases family_descends (prefixWord ++ tailWord_913096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913116 : List Nat := [2, 2, 5, 1, 2, 2, 2, 5]
def baseStart_913116 : Nat := 118140960795 + 913116 * 2 ^ 59
def prefixEnd_913116 : Nat := 4983230072969 + 3 ^ 40 * 913116 * 2
def baseEnd_913116 : Nat := 69461837231252542688987

theorem tailTrace_913116 : CollatzResearch.WordTrace tailWord_913116 prefixEnd_913116 69461837231252542688987 := by
  unfold tailWord_913116
  simp only [CollatzResearch.WordTrace]
  refine ⟨16652038279972077321135601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22202717706629436428180801 16652038279972077321135601)
  ·
    refine ⟨12489028709979057990851701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16652038279972077321135601 12489028709979057990851701)
    ·
      refine ⟨1170846441560536686642347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12489028709979057990851701 1170846441560536686642347)
      ·
        refine ⟨1756269662340805029963521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170846441560536686642347 1756269662340805029963521)
        ·
          refine ⟨1317202246755603772472641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756269662340805029963521 1317202246755603772472641)
          ·
            refine ⟨987901685066702829354481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317202246755603772472641 987901685066702829354481)
            ·
              refine ⟨740926263800027122015861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987901685066702829354481 740926263800027122015861)
              ·
                refine ⟨69461837231252542688987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 740926263800027122015861 69461837231252542688987)
                ·
                  rfl

theorem cell21_913116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_913116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913116 prefixEnd_913116 := by exact prefixLift 913116
  have htrace : WordTrace (prefixWord ++ tailWord_913116) baseStart_913116 baseEnd_913116 := by
    simpa [prefixWord, tailWord_913116, baseEnd_913116] using wordTrace_append hprefix tailTrace_913116
  have hstable : (prefixWord ++ tailWord_913116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913116).length < 2 ^ (prefixWord ++ tailWord_913116).sum := by decide
  have hdescent : baseEnd_913116 < baseStart_913116 := by decide
  rcases family_descends (prefixWord ++ tailWord_913116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913234 : List Nat := [3, 2, 2, 1, 1, 4, 3, 5]
def baseStart_913234 : Nat := 118140960795 + 913234 * 2 ^ 59
def prefixEnd_913234 : Nat := 4983230072969 + 3 ^ 40 * 913234 * 2
def baseEnd_913234 : Nat := 69470813633805215033351

theorem tailTrace_913234 : CollatzResearch.WordTrace tailWord_913234 prefixEnd_913234 69470813633805215033351 := by
  unfold tailWord_913234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8327095093379165198766689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22205586915677773863377837 8327095093379165198766689)
  ·
    refine ⟨6245321320034373899075017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8327095093379165198766689 6245321320034373899075017)
    ·
      refine ⟨4683990990025780424306263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6245321320034373899075017 4683990990025780424306263)
      ·
        refine ⟨7025986485038670636459395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4683990990025780424306263 7025986485038670636459395)
        ·
          refine ⟨10538979727558005954689093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7025986485038670636459395 10538979727558005954689093)
          ·
            refine ⟨1976058698917126116504205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10538979727558005954689093 1976058698917126116504205)
            ·
              refine ⟨741022012093922293689077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1976058698917126116504205 741022012093922293689077)
              ·
                refine ⟨69470813633805215033351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 741022012093922293689077 69470813633805215033351)
                ·
                  rfl

theorem cell21_913234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_913234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913234 prefixEnd_913234 := by exact prefixLift 913234
  have htrace : WordTrace (prefixWord ++ tailWord_913234) baseStart_913234 baseEnd_913234 := by
    simpa [prefixWord, tailWord_913234, baseEnd_913234] using wordTrace_append hprefix tailTrace_913234
  have hstable : (prefixWord ++ tailWord_913234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913234).length < 2 ^ (prefixWord ++ tailWord_913234).sum := by decide
  have hdescent : baseEnd_913234 < baseStart_913234 := by decide
  rcases family_descends (prefixWord ++ tailWord_913234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913369 : List Nat := [1, 2, 1, 2, 7, 8]
def baseStart_913369 : Nat := 118140960795 + 913369 * 2 ^ 59
def prefixEnd_913369 : Nat := 4983230072969 + 3 ^ 40 * 913369 * 2
def baseEnd_913369 : Nat := 7720120360766126309251

theorem tailTrace_913369 : CollatzResearch.WordTrace tailWord_913369 prefixEnd_913369 7720120360766126309251 := by
  unfold tailWord_913369
  simp only [CollatzResearch.WordTrace]
  refine ⟨33313304228027578851231161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22208869485351719234154107 33313304228027578851231161)
  ·
    refine ⟨24984978171020684138423371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33313304228027578851231161 24984978171020684138423371)
    ·
      refine ⟨37477467256531026207635057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24984978171020684138423371 37477467256531026207635057)
      ·
        refine ⟨28108100442398269655726293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37477467256531026207635057 28108100442398269655726293)
        ·
          refine ⟨658783604118709445056085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 28108100442398269655726293 658783604118709445056085)
          ·
            refine ⟨7720120360766126309251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 658783604118709445056085 7720120360766126309251)
            ·
              rfl

theorem cell21_913369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 8].length) (baseStart_913369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913369 prefixEnd_913369 := by exact prefixLift 913369
  have htrace : WordTrace (prefixWord ++ tailWord_913369) baseStart_913369 baseEnd_913369 := by
    simpa [prefixWord, tailWord_913369, baseEnd_913369] using wordTrace_append hprefix tailTrace_913369
  have hstable : (prefixWord ++ tailWord_913369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913369).length < 2 ^ (prefixWord ++ tailWord_913369).sum := by decide
  have hdescent : baseEnd_913369 < baseStart_913369 := by decide
  rcases family_descends (prefixWord ++ tailWord_913369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913431 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 6]
def baseStart_913431 : Nat := 118140960795 + 913431 * 2 ^ 59
def prefixEnd_913431 : Nat := 4983230072969 + 3 ^ 40 * 913431 * 2
def baseEnd_913431 : Nat := 208457398985387080316317

theorem tailTrace_913431 : CollatzResearch.WordTrace tailWord_913431 prefixEnd_913431 208457398985387080316317 := by
  unfold tailWord_913431
  simp only [CollatzResearch.WordTrace]
  refine ⟨33315565553802963439988147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22210377035868642293325431 33315565553802963439988147)
  ·
    refine ⟨49973348330704445159982221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33315565553802963439988147 49973348330704445159982221)
    ·
      refine ⟨18740005624014166934993333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49973348330704445159982221 18740005624014166934993333)
      ·
        refine ⟨1756875527251328150155625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18740005624014166934993333 1756875527251328150155625)
        ·
          refine ⟨1317656645438496112616719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756875527251328150155625 1317656645438496112616719)
          ·
            refine ⟨1976484968157744168925079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317656645438496112616719 1976484968157744168925079)
            ·
              refine ⟨2964727452236616253387619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976484968157744168925079 2964727452236616253387619)
              ·
                refine ⟨4447091178354924380081429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964727452236616253387619 4447091178354924380081429)
                ·
                  refine ⟨208457398985387080316317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4447091178354924380081429 208457398985387080316317)
                  ·
                    rfl

theorem cell21_913431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 6].length) (baseStart_913431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913431 prefixEnd_913431 := by exact prefixLift 913431
  have htrace : WordTrace (prefixWord ++ tailWord_913431) baseStart_913431 baseEnd_913431 := by
    simpa [prefixWord, tailWord_913431, baseEnd_913431] using wordTrace_append hprefix tailTrace_913431
  have hstable : (prefixWord ++ tailWord_913431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913431).length < 2 ^ (prefixWord ++ tailWord_913431).sum := by decide
  have hdescent : baseEnd_913431 < baseStart_913431 := by decide
  rcases family_descends (prefixWord ++ tailWord_913431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913459 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 5]
def baseStart_913459 : Nat := 118140960795 + 913459 * 2 ^ 59
def prefixEnd_913459 : Nat := 4983230072969 + 3 ^ 40 * 913459 * 2
def baseEnd_913459 : Nat := 208463788966865253849593

theorem tailTrace_913459 : CollatzResearch.WordTrace tailWord_913459 prefixEnd_913459 208463788966865253849593 := by
  unfold tailWord_913459
  simp only [CollatzResearch.WordTrace]
  refine ⟨33316586797701524222007431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22211057865134349481338287 33316586797701524222007431)
  ·
    refine ⟨49974880196552286333011147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33316586797701524222007431 49974880196552286333011147)
    ·
      refine ⟨74962320294828429499516721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49974880196552286333011147 74962320294828429499516721)
      ·
        refine ⟨56221740221121322124637541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74962320294828429499516721 56221740221121322124637541)
        ·
          refine ⟨10541576291460247898369539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56221740221121322124637541 10541576291460247898369539)
          ·
            refine ⟨15812364437190371847554309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10541576291460247898369539 15812364437190371847554309)
            ·
              refine ⟨2964818331973194721416433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15812364437190371847554309 2964818331973194721416433)
              ·
                refine ⟨2223613748979896041062325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2964818331973194721416433 2223613748979896041062325)
                ·
                  refine ⟨208463788966865253849593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2223613748979896041062325 208463788966865253849593)
                  ·
                    rfl

theorem cell21_913459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_913459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913459 prefixEnd_913459 := by exact prefixLift 913459
  have htrace : WordTrace (prefixWord ++ tailWord_913459) baseStart_913459 baseEnd_913459 := by
    simpa [prefixWord, tailWord_913459, baseEnd_913459] using wordTrace_append hprefix tailTrace_913459
  have hstable : (prefixWord ++ tailWord_913459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913459).length < 2 ^ (prefixWord ++ tailWord_913459).sum := by decide
  have hdescent : baseEnd_913459 < baseStart_913459 := by decide
  rcases family_descends (prefixWord ++ tailWord_913459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913504 : List Nat := [2, 1, 1, 3, 2, 3, 1, 8]
def baseStart_913504 : Nat := 118140960795 + 913504 * 2 ^ 59
def prefixEnd_913504 : Nat := 4983230072969 + 3 ^ 40 * 913504 * 2
def baseEnd_913504 : Nat := 69491352859985058533167

theorem tailTrace_913504 : CollatzResearch.WordTrace tailWord_913504 prefixEnd_913504 69491352859985058533167 := by
  unfold tailWord_913504
  simp only [CollatzResearch.WordTrace]
  refine ⟨16659114041269248453697783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22212152055025664604930377 16659114041269248453697783)
  ·
    refine ⟨24988671061903872680546675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16659114041269248453697783 24988671061903872680546675)
    ·
      refine ⟨37483006592855809020820013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24988671061903872680546675 37483006592855809020820013)
      ·
        refine ⟨14056127472320928382807505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37483006592855809020820013 14056127472320928382807505)
        ·
          refine ⟨10542095604240696287105629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14056127472320928382807505 10542095604240696287105629)
          ·
            refine ⟨3953285851590261107664611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10542095604240696287105629 3953285851590261107664611)
            ·
              refine ⟨5929928777385391661496917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3953285851590261107664611 5929928777385391661496917)
              ·
                refine ⟨69491352859985058533167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5929928777385391661496917 69491352859985058533167)
                ·
                  rfl

theorem cell21_913504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_913504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913504 prefixEnd_913504 := by exact prefixLift 913504
  have htrace : WordTrace (prefixWord ++ tailWord_913504) baseStart_913504 baseEnd_913504 := by
    simpa [prefixWord, tailWord_913504, baseEnd_913504] using wordTrace_append hprefix tailTrace_913504
  have hstable : (prefixWord ++ tailWord_913504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913504).length < 2 ^ (prefixWord ++ tailWord_913504).sum := by decide
  have hdescent : baseEnd_913504 < baseStart_913504 := by decide
  rcases family_descends (prefixWord ++ tailWord_913504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913507 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 4]
def baseStart_913507 : Nat := 118140960795 + 913507 * 2 ^ 59
def prefixEnd_913507 : Nat := 4983230072969 + 3 ^ 40 * 913507 * 2
def baseEnd_913507 : Nat := 208474743220827837049495

theorem tailTrace_913507 : CollatzResearch.WordTrace tailWord_913507 prefixEnd_913507 208474743220827837049495 := by
  unfold tailWord_913507
  simp only [CollatzResearch.WordTrace]
  refine ⟨33318337501527628419754775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22212225001018418946503183 33318337501527628419754775)
  ·
    refine ⟨49977506252291442629632163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33318337501527628419754775 49977506252291442629632163)
    ·
      refine ⟨74966259378437163944448245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49977506252291442629632163 74966259378437163944448245)
      ·
        refine ⟨7028086816728484119792023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74966259378437163944448245 7028086816728484119792023)
        ·
          refine ⟨10542130225092726179688035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7028086816728484119792023 10542130225092726179688035)
          ·
            refine ⟨15813195337639089269532053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10542130225092726179688035 15813195337639089269532053)
            ·
              refine ⟨741243531451832309509315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15813195337639089269532053 741243531451832309509315)
              ·
                refine ⟨1111865297177748464263973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741243531451832309509315 1111865297177748464263973)
                ·
                  refine ⟨208474743220827837049495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1111865297177748464263973 208474743220827837049495)
                  ·
                    rfl

theorem cell21_913507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 4].length) (baseStart_913507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913507 prefixEnd_913507 := by exact prefixLift 913507
  have htrace : WordTrace (prefixWord ++ tailWord_913507) baseStart_913507 baseEnd_913507 := by
    simpa [prefixWord, tailWord_913507, baseEnd_913507] using wordTrace_append hprefix tailTrace_913507
  have hstable : (prefixWord ++ tailWord_913507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913507).length < 2 ^ (prefixWord ++ tailWord_913507).sum := by decide
  have hdescent : baseEnd_913507 < baseStart_913507 := by decide
  rcases family_descends (prefixWord ++ tailWord_913507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913552 : List Nat := [2, 1, 1, 1, 1, 1, 7, 4, 3]
def baseStart_913552 : Nat := 118140960795 + 913552 * 2 ^ 59
def prefixEnd_913552 : Nat := 4983230072969 + 3 ^ 40 * 913552 * 2
def baseEnd_913552 : Nat := 208485012833917758799403

theorem tailTrace_913552 : CollatzResearch.WordTrace tailWord_913552 prefixEnd_913552 208485012833917758799403 := by
  unfold tailWord_913552
  simp only [CollatzResearch.WordTrace]
  refine ⟨16659989393182300552571455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22213319190909734070095273 16659989393182300552571455)
  ·
    refine ⟨24989984089773450828857183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16659989393182300552571455 24989984089773450828857183)
    ·
      refine ⟨37484976134660176243285775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24989984089773450828857183 37484976134660176243285775)
      ·
        refine ⟨56227464201990264364928663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37484976134660176243285775 56227464201990264364928663)
        ·
          refine ⟨84341196302985396547392995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56227464201990264364928663 84341196302985396547392995)
          ·
            refine ⟨126511794454478094821089493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84341196302985396547392995 126511794454478094821089493)
            ·
              refine ⟨2965120182526830347369285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 126511794454478094821089493 2965120182526830347369285)
              ·
                refine ⟨555960034223780690131741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2965120182526830347369285 555960034223780690131741)
                ·
                  refine ⟨208485012833917758799403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555960034223780690131741 208485012833917758799403)
                  ·
                    rfl

theorem cell21_913552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 3].length) (baseStart_913552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913552 prefixEnd_913552 := by exact prefixLift 913552
  have htrace : WordTrace (prefixWord ++ tailWord_913552) baseStart_913552 baseEnd_913552 := by
    simpa [prefixWord, tailWord_913552, baseEnd_913552] using wordTrace_append hprefix tailTrace_913552
  have hstable : (prefixWord ++ tailWord_913552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913552).length < 2 ^ (prefixWord ++ tailWord_913552).sum := by decide
  have hdescent : baseEnd_913552 < baseStart_913552 := by decide
  rcases family_descends (prefixWord ++ tailWord_913552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913611 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 5]
def baseStart_913611 : Nat := 118140960795 + 913611 * 2 ^ 59
def prefixEnd_913611 : Nat := 4983230072969 + 3 ^ 40 * 913611 * 2
def baseEnd_913611 : Nat := 208498477437746767315949

theorem tailTrace_913611 : CollatzResearch.WordTrace tailWord_913611 prefixEnd_913611 208498477437746767315949 := by
  unfold tailWord_913611
  simp only [CollatzResearch.WordTrace]
  refine ⟨33322130693150854181540687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22214753795433902787693791 33322130693150854181540687)
  ·
    refine ⟨49983196039726281272311031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33322130693150854181540687 49983196039726281272311031)
    ·
      refine ⟨74974794059589421908466547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49983196039726281272311031 74974794059589421908466547)
      ·
        refine ⟨112462191089384132862699821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74974794059589421908466547 112462191089384132862699821)
        ·
          refine ⟨42173321658519049823512433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112462191089384132862699821 42173321658519049823512433)
          ·
            refine ⟨31629991243889287367634325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42173321658519049823512433 31629991243889287367634325)
            ·
              refine ⟨1482655839557310345357859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31629991243889287367634325 1482655839557310345357859)
              ·
                refine ⟨2223983759335965518036789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482655839557310345357859 2223983759335965518036789)
                ·
                  refine ⟨208498477437746767315949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2223983759335965518036789 208498477437746767315949)
                  ·
                    rfl

theorem cell21_913611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 5].length) (baseStart_913611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913611 prefixEnd_913611 := by exact prefixLift 913611
  have htrace : WordTrace (prefixWord ++ tailWord_913611) baseStart_913611 baseEnd_913611 := by
    simpa [prefixWord, tailWord_913611, baseEnd_913611] using wordTrace_append hprefix tailTrace_913611
  have hstable : (prefixWord ++ tailWord_913611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913611).length < 2 ^ (prefixWord ++ tailWord_913611).sum := by decide
  have hdescent : baseEnd_913611 < baseStart_913611 := by decide
  rcases family_descends (prefixWord ++ tailWord_913611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913662 : List Nat := [4, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_913662 : Nat := 118140960795 + 913662 * 2 ^ 59
def prefixEnd_913662 : Nat := 4983230072969 + 3 ^ 40 * 913662 * 2
def baseEnd_913662 : Nat := 208510116332582011965845

theorem tailTrace_913662 : CollatzResearch.WordTrace tailWord_913662 prefixEnd_913662 208510116332582011965845 := by
  unfold tailWord_913662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4165498851995761236455905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22215993877310726594431493 4165498851995761236455905)
  ·
    refine ⟨3124124138996820927341929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4165498851995761236455905 3124124138996820927341929)
    ·
      refine ⟨2343093104247615695506447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3124124138996820927341929 2343093104247615695506447)
      ·
        refine ⟨3514639656371423543259671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343093104247615695506447 3514639656371423543259671)
        ·
          refine ⟨5271959484557135314889507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3514639656371423543259671 5271959484557135314889507)
          ·
            refine ⟨7907939226835702972334261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271959484557135314889507 7907939226835702972334261)
            ·
              refine ⟨741369302515847153656337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7907939226835702972334261 741369302515847153656337)
              ·
                refine ⟨556026976886885365242253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741369302515847153656337 556026976886885365242253)
                ·
                  refine ⟨208510116332582011965845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556026976886885365242253 208510116332582011965845)
                  ·
                    rfl

theorem cell21_913662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_913662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913662 prefixEnd_913662 := by exact prefixLift 913662
  have htrace : WordTrace (prefixWord ++ tailWord_913662) baseStart_913662 baseEnd_913662 := by
    simpa [prefixWord, tailWord_913662, baseEnd_913662] using wordTrace_append hprefix tailTrace_913662
  have hstable : (prefixWord ++ tailWord_913662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913662).length < 2 ^ (prefixWord ++ tailWord_913662).sum := by decide
  have hdescent : baseEnd_913662 < baseStart_913662 := by decide
  rcases family_descends (prefixWord ++ tailWord_913662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913721 : List Nat := [1, 2, 1, 6, 1, 2, 1, 4, 3]
def baseStart_913721 : Nat := 118140960795 + 913721 * 2 ^ 59
def prefixEnd_913721 : Nat := 4983230072969 + 3 ^ 40 * 913721 * 2
def baseEnd_913721 : Nat := 208523580936411020482391

theorem tailTrace_913721 : CollatzResearch.WordTrace tailWord_913721 prefixEnd_913721 208523580936411020482391 := by
  unfold tailWord_913721
  simp only [CollatzResearch.WordTrace]
  refine ⟨33326142722752342968045017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22217428481834895312030011 33326142722752342968045017)
  ·
    refine ⟨24994607042064257226033763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33326142722752342968045017 24994607042064257226033763)
    ·
      refine ⟨37491910563096385839050645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24994607042064257226033763 37491910563096385839050645)
      ·
        refine ⟨1757433307645143086205499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37491910563096385839050645 1757433307645143086205499)
        ·
          refine ⟨2636149961467714629308249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757433307645143086205499 2636149961467714629308249)
          ·
            refine ⟨1977112471100785971981187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2636149961467714629308249 1977112471100785971981187)
            ·
              refine ⟨2965668706651178957971781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977112471100785971981187 2965668706651178957971781)
              ·
                refine ⟨556062882497096054619709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2965668706651178957971781 556062882497096054619709)
                ·
                  refine ⟨208523580936411020482391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556062882497096054619709 208523580936411020482391)
                  ·
                    rfl

theorem cell21_913721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 3].length) (baseStart_913721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913721 prefixEnd_913721 := by exact prefixLift 913721
  have htrace : WordTrace (prefixWord ++ tailWord_913721) baseStart_913721 baseEnd_913721 := by
    simpa [prefixWord, tailWord_913721, baseEnd_913721] using wordTrace_append hprefix tailTrace_913721
  have hstable : (prefixWord ++ tailWord_913721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913721).length < 2 ^ (prefixWord ++ tailWord_913721).sum := by decide
  have hdescent : baseEnd_913721 < baseStart_913721 := by decide
  rcases family_descends (prefixWord ++ tailWord_913721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913845 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 4]
def baseStart_913845 : Nat := 118140960795 + 913845 * 2 ^ 59
def prefixEnd_913845 : Nat := 4983230072969 + 3 ^ 40 * 913845 * 2
def baseEnd_913845 : Nat := 208551879425814360415471

theorem tailTrace_913845 : CollatzResearch.WordTrace tailWord_913845 prefixEnd_913845 208551879425814360415471 := by
  unfold tailWord_913845
  simp only [CollatzResearch.WordTrace]
  refine ⟨33330665374303112145558989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22220443582868741430372659 33330665374303112145558989)
  ·
    refine ⟨12498999515363667054584621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33330665374303112145558989 12498999515363667054584621)
    ·
      refine ⟨4687124818261375145469233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12498999515363667054584621 4687124818261375145469233)
      ·
        refine ⟨3515343613696031359101925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4687124818261375145469233 3515343613696031359101925)
        ·
          refine ⟨659126927568005879831611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3515343613696031359101925 659126927568005879831611)
          ·
            refine ⟨988690391352008819747417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659126927568005879831611 988690391352008819747417)
            ·
              refine ⟨741517793514006614810563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988690391352008819747417 741517793514006614810563)
              ·
                refine ⟨1112276690271009922215845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741517793514006614810563 1112276690271009922215845)
                ·
                  refine ⟨208551879425814360415471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1112276690271009922215845 208551879425814360415471)
                  ·
                    rfl

theorem cell21_913845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_913845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913845 prefixEnd_913845 := by exact prefixLift 913845
  have htrace : WordTrace (prefixWord ++ tailWord_913845) baseStart_913845 baseEnd_913845 := by
    simpa [prefixWord, tailWord_913845, baseEnd_913845] using wordTrace_append hprefix tailTrace_913845
  have hstable : (prefixWord ++ tailWord_913845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913845).length < 2 ^ (prefixWord ++ tailWord_913845).sum := by decide
  have hdescent : baseEnd_913845 < baseStart_913845 := by decide
  rcases family_descends (prefixWord ++ tailWord_913845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913901 : List Nat := [1, 5, 1, 3, 1, 1, 3, 6]
def baseStart_913901 : Nat := 118140960795 + 913901 * 2 ^ 59
def prefixEnd_913901 : Nat := 4983230072969 + 3 ^ 40 * 913901 * 2
def baseEnd_913901 : Nat := 69521553129590235827341

theorem tailTrace_913901 : CollatzResearch.WordTrace tailWord_913901 prefixEnd_913901 69521553129590235827341 := by
  unfold tailWord_913901
  simp only [CollatzResearch.WordTrace]
  refine ⟨33332707862100233709597557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22221805241400155806398371 33332707862100233709597557)
  ·
    refine ⟨3124941362071896910274771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33332707862100233709597557 3124941362071896910274771)
    ·
      refine ⟨4687412043107845365412157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3124941362071896910274771 4687412043107845365412157)
      ·
        refine ⟨1757779516165442012029559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4687412043107845365412157 1757779516165442012029559)
        ·
          refine ⟨2636669274248163018044339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757779516165442012029559 2636669274248163018044339)
          ·
            refine ⟨3955003911372244527066509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636669274248163018044339 3955003911372244527066509)
            ·
              refine ⟨1483126466764591697649941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3955003911372244527066509 1483126466764591697649941)
              ·
                refine ⟨69521553129590235827341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1483126466764591697649941 69521553129590235827341)
                ·
                  rfl

theorem cell21_913901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 6].length) (baseStart_913901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913901 prefixEnd_913901 := by exact prefixLift 913901
  have htrace : WordTrace (prefixWord ++ tailWord_913901) baseStart_913901 baseEnd_913901 := by
    simpa [prefixWord, tailWord_913901, baseEnd_913901] using wordTrace_append hprefix tailTrace_913901
  have hstable : (prefixWord ++ tailWord_913901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913901).length < 2 ^ (prefixWord ++ tailWord_913901).sum := by decide
  have hdescent : baseEnd_913901 < baseStart_913901 := by decide
  rcases family_descends (prefixWord ++ tailWord_913901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913932 : List Nat := [2, 2, 1, 2, 4, 1, 1, 5, 3]
def baseStart_913932 : Nat := 118140960795 + 913932 * 2 ^ 59
def prefixEnd_913932 : Nat := 4983230072969 + 3 ^ 40 * 913932 * 2
def baseEnd_913932 : Nat := 208571734011121542465293

theorem tailTrace_913932 : CollatzResearch.WordTrace tailWord_913932 prefixEnd_913932 208571734011121542465293 := by
  unfold tailWord_913932
  simp only [CollatzResearch.WordTrace]
  refine ⟨16666919262493963001988025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22222559016658617335984033 16666919262493963001988025)
  ·
    refine ⟨12500189446870472251491019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16666919262493963001988025 12500189446870472251491019)
    ·
      refine ⟨18750284170305708377236529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12500189446870472251491019 18750284170305708377236529)
      ·
        refine ⟨14062713127729281282927397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18750284170305708377236529 14062713127729281282927397)
        ·
          refine ⟨2636758711449240240548887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14062713127729281282927397 2636758711449240240548887)
          ·
            refine ⟨3955138067173860360823331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636758711449240240548887 3955138067173860360823331)
            ·
              refine ⟨5932707100760790541234997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955138067173860360823331 5932707100760790541234997)
              ·
                refine ⟨556191290696324113240781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5932707100760790541234997 556191290696324113240781)
                ·
                  refine ⟨208571734011121542465293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556191290696324113240781 208571734011121542465293)
                  ·
                    rfl

theorem cell21_913932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_913932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913932 prefixEnd_913932 := by exact prefixLift 913932
  have htrace : WordTrace (prefixWord ++ tailWord_913932) baseStart_913932 baseEnd_913932 := by
    simpa [prefixWord, tailWord_913932, baseEnd_913932] using wordTrace_append hprefix tailTrace_913932
  have hstable : (prefixWord ++ tailWord_913932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913932).length < 2 ^ (prefixWord ++ tailWord_913932).sum := by decide
  have hdescent : baseEnd_913932 < baseStart_913932 := by decide
  rcases family_descends (prefixWord ++ tailWord_913932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913946 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_913946 : Nat := 118140960795 + 913946 * 2 ^ 59
def prefixEnd_913946 : Nat := 4983230072969 + 3 ^ 40 * 913946 * 2
def baseEnd_913946 : Nat := 208574929001860629231931

theorem tailTrace_913946 : CollatzResearch.WordTrace tailWord_913946 prefixEnd_913946 208574929001860629231931 := by
  unfold tailWord_913946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8333587286734301598746423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22222899431291470929990461 8333587286734301598746423)
  ·
    refine ⟨12500380930101452398119635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8333587286734301598746423 12500380930101452398119635)
    ·
      refine ⟨18750571395152178597179453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12500380930101452398119635 18750571395152178597179453)
      ·
        refine ⟨7031464273182066973942295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18750571395152178597179453 7031464273182066973942295)
        ·
          refine ⟨10547196409773100460913443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7031464273182066973942295 10547196409773100460913443)
          ·
            refine ⟨15820794614659650691370165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10547196409773100460913443 15820794614659650691370165)
            ·
              refine ⟨1483199495124342252315953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15820794614659650691370165 1483199495124342252315953)
              ·
                refine ⟨1112399621343256689236965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483199495124342252315953 1112399621343256689236965)
                ·
                  refine ⟨208574929001860629231931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1112399621343256689236965 208574929001860629231931)
                  ·
                    rfl

theorem cell21_913946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_913946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_913946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_913946 prefixEnd_913946 := by exact prefixLift 913946
  have htrace : WordTrace (prefixWord ++ tailWord_913946) baseStart_913946 baseEnd_913946 := by
    simpa [prefixWord, tailWord_913946, baseEnd_913946] using wordTrace_append hprefix tailTrace_913946
  have hstable : (prefixWord ++ tailWord_913946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913946).length < 2 ^ (prefixWord ++ tailWord_913946).sum := by decide
  have hdescent : baseEnd_913946 < baseStart_913946 := by decide
  rcases family_descends (prefixWord ++ tailWord_913946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914005 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 6]
def baseStart_914005 : Nat := 118140960795 + 914005 * 2 ^ 59
def prefixEnd_914005 : Nat := 4983230072969 + 3 ^ 40 * 914005 * 2
def baseEnd_914005 : Nat := 208588393605689637748477

theorem tailTrace_914005 : CollatzResearch.WordTrace tailWord_914005 prefixEnd_914005 208588393605689637748477 := by
  unfold tailWord_914005
  simp only [CollatzResearch.WordTrace]
  refine ⟨33336501053723459471383469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22224334035815639647588979 33336501053723459471383469)
  ·
    refine ⟨12501187895146297301768801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33336501053723459471383469 12501187895146297301768801)
    ·
      refine ⟨9375890921359722976326601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12501187895146297301768801 9375890921359722976326601)
      ·
        refine ⟨7031918191019792232244951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9375890921359722976326601 7031918191019792232244951)
        ·
          refine ⟨10547877286529688348367427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7031918191019792232244951 10547877286529688348367427)
          ·
            refine ⟨15821815929794532522551141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10547877286529688348367427 15821815929794532522551141)
            ·
              refine ⟨2966590486836474847978339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15821815929794532522551141 2966590486836474847978339)
              ·
                refine ⟨4449885730254712271967509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966590486836474847978339 4449885730254712271967509)
                ·
                  refine ⟨208588393605689637748477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4449885730254712271967509 208588393605689637748477)
                  ·
                    rfl

theorem cell21_914005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_914005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914005 prefixEnd_914005 := by exact prefixLift 914005
  have htrace : WordTrace (prefixWord ++ tailWord_914005) baseStart_914005 baseEnd_914005 := by
    simpa [prefixWord, tailWord_914005, baseEnd_914005] using wordTrace_append hprefix tailTrace_914005
  have hstable : (prefixWord ++ tailWord_914005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914005).length < 2 ^ (prefixWord ++ tailWord_914005).sum := by decide
  have hdescent : baseEnd_914005 < baseStart_914005 := by decide
  rcases family_descends (prefixWord ++ tailWord_914005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914067 : List Nat := [1, 1, 1, 2, 1, 2, 2, 8, 3]
def baseStart_914067 : Nat := 118140960795 + 914067 * 2 ^ 59
def prefixEnd_914067 : Nat := 4983230072969 + 3 ^ 40 * 914067 * 2
def baseEnd_914067 : Nat := 208602542850391307715017

theorem tailTrace_914067 : CollatzResearch.WordTrace tailWord_914067 prefixEnd_914067 208602542850391307715017 := by
  unfold tailWord_914067
  simp only [CollatzResearch.WordTrace]
  refine ⟨33338762379498844060140455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22225841586332562706760303 33338762379498844060140455)
  ·
    refine ⟨50008143569248266090210683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33338762379498844060140455 50008143569248266090210683)
    ·
      refine ⟨75012215353872399135316025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50008143569248266090210683 75012215353872399135316025)
      ·
        refine ⟨56259161515404299351487019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75012215353872399135316025 56259161515404299351487019)
        ·
          refine ⟨84388742273106449027230529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56259161515404299351487019 84388742273106449027230529)
          ·
            refine ⟨63291556704829836770422897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84388742273106449027230529 63291556704829836770422897)
            ·
              refine ⟨47468667528622377577817173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63291556704829836770422897 47468667528622377577817173)
              ·
                refine ⟨556273447601043487240045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 47468667528622377577817173 556273447601043487240045)
                ·
                  refine ⟨208602542850391307715017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556273447601043487240045 208602542850391307715017)
                  ·
                    rfl

theorem cell21_914067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 3].length) (baseStart_914067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914067 prefixEnd_914067 := by exact prefixLift 914067
  have htrace : WordTrace (prefixWord ++ tailWord_914067) baseStart_914067 baseEnd_914067 := by
    simpa [prefixWord, tailWord_914067, baseEnd_914067] using wordTrace_append hprefix tailTrace_914067
  have hstable : (prefixWord ++ tailWord_914067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914067).length < 2 ^ (prefixWord ++ tailWord_914067).sum := by decide
  have hdescent : baseEnd_914067 < baseStart_914067 := by decide
  rcases family_descends (prefixWord ++ tailWord_914067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914101 : List Nat := [1, 3, 3, 3, 1, 2, 2, 3, 3]
def baseStart_914101 : Nat := 118140960795 + 914101 * 2 ^ 59
def prefixEnd_914101 : Nat := 4983230072969 + 3 ^ 40 * 914101 * 2
def baseEnd_914101 : Nat := 208610302113614804148281

theorem tailTrace_914101 : CollatzResearch.WordTrace tailWord_914101 prefixEnd_914101 208610302113614804148281 := by
  unfold tailWord_914101
  simp only [CollatzResearch.WordTrace]
  refine ⟨33340002461375667866878157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22226668307583778577918771 33340002461375667866878157)
  ·
    refine ⟨12502500923015875450079309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33340002461375667866878157 12502500923015875450079309)
    ·
      refine ⟨4688437846130953293779741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12502500923015875450079309 4688437846130953293779741)
      ·
        refine ⟨1758164192299107485167403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4688437846130953293779741 1758164192299107485167403)
        ·
          refine ⟨2637246288448661227751105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758164192299107485167403 2637246288448661227751105)
          ·
            refine ⟨1977934716336495920813329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2637246288448661227751105 1977934716336495920813329)
            ·
              refine ⟨1483451037252371940609997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1977934716336495920813329 1483451037252371940609997)
              ·
                refine ⟨556294138969639477728749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1483451037252371940609997 556294138969639477728749)
                ·
                  refine ⟨208610302113614804148281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556294138969639477728749 208610302113614804148281)
                  ·
                    rfl

theorem cell21_914101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_914101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914101 prefixEnd_914101 := by exact prefixLift 914101
  have htrace : WordTrace (prefixWord ++ tailWord_914101) baseStart_914101 baseEnd_914101 := by
    simpa [prefixWord, tailWord_914101, baseEnd_914101] using wordTrace_append hprefix tailTrace_914101
  have hstable : (prefixWord ++ tailWord_914101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914101).length < 2 ^ (prefixWord ++ tailWord_914101).sum := by decide
  have hdescent : baseEnd_914101 < baseStart_914101 := by decide
  rcases family_descends (prefixWord ++ tailWord_914101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914118 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_914118 : Nat := 118140960795 + 914118 * 2 ^ 59
def prefixEnd_914118 : Nat := 4983230072969 + 3 ^ 40 * 914118 * 2
def baseEnd_914118 : Nat := 208614181745226552364913

theorem tailTrace_914118 : CollatzResearch.WordTrace tailWord_914118 prefixEnd_914118 208614181745226552364913 := by
  unfold tailWord_914118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041894453197314992820219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22227081668209386513498005 1041894453197314992820219)
  ·
    refine ⟨1562841679795972489230329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1041894453197314992820219 1562841679795972489230329)
    ·
      refine ⟨1172131259846979366922747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1562841679795972489230329 1172131259846979366922747)
      ·
        refine ⟨1758196889770469050384121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172131259846979366922747 1758196889770469050384121)
        ·
          refine ⟨1318647667327851787788091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1758196889770469050384121 1318647667327851787788091)
          ·
            refine ⟨1977971500991777681682137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318647667327851787788091 1977971500991777681682137)
            ·
              refine ⟨1483478625743833261261603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1977971500991777681682137 1483478625743833261261603)
              ·
                refine ⟨2225217938615749891892405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483478625743833261261603 2225217938615749891892405)
                ·
                  refine ⟨208614181745226552364913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2225217938615749891892405 208614181745226552364913)
                  ·
                    rfl

theorem cell21_914118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_914118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914118 prefixEnd_914118 := by exact prefixLift 914118
  have htrace : WordTrace (prefixWord ++ tailWord_914118) baseStart_914118 baseEnd_914118 := by
    simpa [prefixWord, tailWord_914118, baseEnd_914118] using wordTrace_append hprefix tailTrace_914118
  have hstable : (prefixWord ++ tailWord_914118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914118).length < 2 ^ (prefixWord ++ tailWord_914118).sum := by decide
  have hdescent : baseEnd_914118 < baseStart_914118 := by decide
  rcases family_descends (prefixWord ++ tailWord_914118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914132 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 4]
def baseStart_914132 : Nat := 118140960795 + 914132 * 2 ^ 59
def prefixEnd_914132 : Nat := 4983230072969 + 3 ^ 40 * 914132 * 2
def baseEnd_914132 : Nat := 208617376735965639131551

theorem tailTrace_914132 : CollatzResearch.WordTrace tailWord_914132 prefixEnd_914132 208617376735965639131551 := by
  unfold tailWord_914132
  simp only [CollatzResearch.WordTrace]
  refine ⟨16670566562131680080628325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22227422082842240107504433 16670566562131680080628325)
  ·
    refine ⟨3125731230399690015117811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16670566562131680080628325 3125731230399690015117811)
    ·
      refine ⟨4688596845599535022676717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3125731230399690015117811 4688596845599535022676717)
      ·
        refine ⟨1758223817099825633503769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4688596845599535022676717 1758223817099825633503769)
        ·
          refine ⟨1318667862824869225127827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1758223817099825633503769 1318667862824869225127827)
          ·
            refine ⟨1978001794237303837691741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318667862824869225127827 1978001794237303837691741)
            ·
              refine ⟨741750672838988939134403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1978001794237303837691741 741750672838988939134403)
              ·
                refine ⟨1112626009258483408701605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741750672838988939134403 1112626009258483408701605)
                ·
                  refine ⟨208617376735965639131551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1112626009258483408701605 208617376735965639131551)
                  ·
                    rfl

theorem cell21_914132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_914132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914132 prefixEnd_914132 := by exact prefixLift 914132
  have htrace : WordTrace (prefixWord ++ tailWord_914132) baseStart_914132 baseEnd_914132 := by
    simpa [prefixWord, tailWord_914132, baseEnd_914132] using wordTrace_append hprefix tailTrace_914132
  have hstable : (prefixWord ++ tailWord_914132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914132).length < 2 ^ (prefixWord ++ tailWord_914132).sum := by decide
  have hdescent : baseEnd_914132 < baseStart_914132 := by decide
  rcases family_descends (prefixWord ++ tailWord_914132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914157 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 8]
def baseStart_914157 : Nat := 118140960795 + 914157 * 2 ^ 59
def prefixEnd_914157 : Nat := 4983230072969 + 3 ^ 40 * 914157 * 2
def baseEnd_914157 : Nat := 208623082076571151214833

theorem tailTrace_914157 : CollatzResearch.WordTrace tailWord_914157 prefixEnd_914157 208623082076571151214833 := by
  unfold tailWord_914157
  simp only [CollatzResearch.WordTrace]
  refine ⟨33342044949172789430916725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22228029966115192953944483 33342044949172789430916725)
  ·
    refine ⟨3125816713984949009148443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33342044949172789430916725 3125816713984949009148443)
    ·
      refine ⟨4688725070977423513722665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3125816713984949009148443 4688725070977423513722665)
      ·
        refine ⟨3516543803233067635291999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4688725070977423513722665 3516543803233067635291999)
        ·
          refine ⟨5274815704849601452937999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3516543803233067635291999 5274815704849601452937999)
          ·
            refine ⟨7912223557274402179406999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5274815704849601452937999 7912223557274402179406999)
            ·
              refine ⟨11868335335911603269110499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7912223557274402179406999 11868335335911603269110499)
              ·
                refine ⟨17802503003867404903665749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11868335335911603269110499 17802503003867404903665749)
                ·
                  refine ⟨208623082076571151214833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17802503003867404903665749 208623082076571151214833)
                  ·
                    rfl

theorem cell21_914157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_914157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914157 prefixEnd_914157 := by exact prefixLift 914157
  have htrace : WordTrace (prefixWord ++ tailWord_914157) baseStart_914157 baseEnd_914157 := by
    simpa [prefixWord, tailWord_914157, baseEnd_914157] using wordTrace_append hprefix tailTrace_914157
  have hstable : (prefixWord ++ tailWord_914157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914157).length < 2 ^ (prefixWord ++ tailWord_914157).sum := by decide
  have hdescent : baseEnd_914157 < baseStart_914157 := by decide
  rcases family_descends (prefixWord ++ tailWord_914157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914174 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_914174 : Nat := 118140960795 + 914174 * 2 ^ 59
def prefixEnd_914174 : Nat := 4983230072969 + 3 ^ 40 * 914174 * 2
def baseEnd_914174 : Nat := 208626961708182899431465

theorem tailTrace_914174 : CollatzResearch.WordTrace tailWord_914174 prefixEnd_914174 208626961708182899431465 := by
  unfold tailWord_914174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4167833123763900166785697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22228443326740800889523717 4167833123763900166785697)
  ·
    refine ⟨3125874842822925125089273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4167833123763900166785697 3125874842822925125089273)
    ·
      refine ⟨2344406132117193843816955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3125874842822925125089273 2344406132117193843816955)
      ·
        refine ⟨3516609198175790765725433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344406132117193843816955 3516609198175790765725433)
        ·
          refine ⟨2637456898631843074294075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3516609198175790765725433 2637456898631843074294075)
          ·
            refine ⟨3956185347947764611441113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637456898631843074294075 3956185347947764611441113)
            ·
              refine ⟨2967139010960823458580835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3956185347947764611441113 2967139010960823458580835)
              ·
                refine ⟨4450708516441235187871253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967139010960823458580835 4450708516441235187871253)
                ·
                  refine ⟨208626961708182899431465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4450708516441235187871253 208626961708182899431465)
                  ·
                    rfl

theorem cell21_914174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_914174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914174 prefixEnd_914174 := by exact prefixLift 914174
  have htrace : WordTrace (prefixWord ++ tailWord_914174) baseStart_914174 baseEnd_914174 := by
    simpa [prefixWord, tailWord_914174, baseEnd_914174] using wordTrace_append hprefix tailTrace_914174
  have hstable : (prefixWord ++ tailWord_914174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914174).length < 2 ^ (prefixWord ++ tailWord_914174).sum := by decide
  have hdescent : baseEnd_914174 < baseStart_914174 := by decide
  rcases family_descends (prefixWord ++ tailWord_914174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914202 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_914202 : Nat := 118140960795 + 914202 * 2 ^ 59
def prefixEnd_914202 : Nat := 4983230072969 + 3 ^ 40 * 914202 * 2
def baseEnd_914202 : Nat := 208633351689661072964741

theorem tailTrace_914202 : CollatzResearch.WordTrace tailWord_914202 prefixEnd_914202 208633351689661072964741 := by
  unfold tailWord_914202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8335921558502440529076215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22229124156006508077536573 8335921558502440529076215)
  ·
    refine ⟨12503882337753660793614323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8335921558502440529076215 12503882337753660793614323)
    ·
      refine ⟨18755823506630491190421485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12503882337753660793614323 18755823506630491190421485)
      ·
        refine ⟨7033433814986434196408057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18755823506630491190421485 7033433814986434196408057)
        ·
          refine ⟨5275075361239825647306043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7033433814986434196408057 5275075361239825647306043)
          ·
            refine ⟨7912613041859738470959065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275075361239825647306043 7912613041859738470959065)
            ·
              refine ⟨5934459781394803853219299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7912613041859738470959065 5934459781394803853219299)
              ·
                refine ⟨8901689672092205779828949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5934459781394803853219299 8901689672092205779828949)
                ·
                  refine ⟨208633351689661072964741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8901689672092205779828949 208633351689661072964741)
                  ·
                    rfl

theorem cell21_914202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_914202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914202 prefixEnd_914202 := by exact prefixLift 914202
  have htrace : WordTrace (prefixWord ++ tailWord_914202) baseStart_914202 baseEnd_914202 := by
    simpa [prefixWord, tailWord_914202, baseEnd_914202] using wordTrace_append hprefix tailTrace_914202
  have hstable : (prefixWord ++ tailWord_914202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914202).length < 2 ^ (prefixWord ++ tailWord_914202).sum := by decide
  have hdescent : baseEnd_914202 < baseStart_914202 := by decide
  rcases family_descends (prefixWord ++ tailWord_914202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914399 : List Nat := [1, 1, 2, 3, 5, 9]
def baseStart_914399 : Nat := 118140960795 + 914399 * 2 ^ 59
def prefixEnd_914399 : Nat := 4983230072969 + 3 ^ 40 * 914399 * 2
def baseEnd_914399 : Nat := 7728826287912315117815

theorem tailTrace_914399 : CollatzResearch.WordTrace tailWord_914399 prefixEnd_914399 7728826287912315117815 := by
  unfold tailWord_914399
  simp only [CollatzResearch.WordTrace]
  refine ⟨33350871414296064761226251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22233914276197376507484167 33350871414296064761226251)
  ·
    refine ⟨50026307121444097141839377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33350871414296064761226251 50026307121444097141839377)
    ·
      refine ⟨37519730341083072856379533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50026307121444097141839377 37519730341083072856379533)
      ·
        refine ⟨14069898877906152321142325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37519730341083072856379533 14069898877906152321142325)
        ·
          refine ⟨1319053019803701780107093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14069898877906152321142325 1319053019803701780107093)
          ·
            refine ⟨7728826287912315117815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1319053019803701780107093 7728826287912315117815)
            ·
              rfl

theorem cell21_914399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 9].length) (baseStart_914399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914399 prefixEnd_914399 := by exact prefixLift 914399
  have htrace : WordTrace (prefixWord ++ tailWord_914399) baseStart_914399 baseEnd_914399 := by
    simpa [prefixWord, tailWord_914399, baseEnd_914399] using wordTrace_append hprefix tailTrace_914399
  have hstable : (prefixWord ++ tailWord_914399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914399).length < 2 ^ (prefixWord ++ tailWord_914399).sum := by decide
  have hdescent : baseEnd_914399 < baseStart_914399 := by decide
  rcases family_descends (prefixWord ++ tailWord_914399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914405 : List Nat := [1, 3, 1, 6, 1, 1, 1, 4, 3]
def baseStart_914405 : Nat := 118140960795 + 914405 * 2 ^ 59
def prefixEnd_914405 : Nat := 4983230072969 + 3 ^ 40 * 914405 * 2
def baseEnd_914405 : Nat := 208679679055377831080993

theorem tailTrace_914405 : CollatzResearch.WordTrace tailWord_914405 prefixEnd_914405 208679679055377831080993 := by
  unfold tailWord_914405
  simp only [CollatzResearch.WordTrace]
  refine ⟨33351090252274327785944669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22234060168182885190629779 33351090252274327785944669)
  ·
    refine ⟨12506658844602872919729251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33351090252274327785944669 12506658844602872919729251)
    ·
      refine ⟨18759988266904309379593877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12506658844602872919729251 18759988266904309379593877)
      ·
        refine ⟨879374450011139502168463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18759988266904309379593877 879374450011139502168463)
        ·
          refine ⟨1319061675016709253252695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879374450011139502168463 1319061675016709253252695)
          ·
            refine ⟨1978592512525063879879043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319061675016709253252695 1978592512525063879879043)
            ·
              refine ⟨2967888768787595819818565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978592512525063879879043 2967888768787595819818565)
              ·
                refine ⟨556479144147674216215981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2967888768787595819818565 556479144147674216215981)
                ·
                  refine ⟨208679679055377831080993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556479144147674216215981 208679679055377831080993)
                  ·
                    rfl

theorem cell21_914405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_914405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914405 prefixEnd_914405 := by exact prefixLift 914405
  have htrace : WordTrace (prefixWord ++ tailWord_914405) baseStart_914405 baseEnd_914405 := by
    simpa [prefixWord, tailWord_914405, baseEnd_914405] using wordTrace_append hprefix tailTrace_914405
  have hstable : (prefixWord ++ tailWord_914405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914405).length < 2 ^ (prefixWord ++ tailWord_914405).sum := by decide
  have hdescent : baseEnd_914405 < baseStart_914405 := by decide
  rcases family_descends (prefixWord ++ tailWord_914405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914450 : List Nat := [3, 2, 5, 1, 1, 1, 8]
def baseStart_914450 : Nat := 118140960795 + 914450 * 2 ^ 59
def prefixEnd_914450 : Nat := 4983230072969 + 3 ^ 40 * 914450 * 2
def baseEnd_914450 : Nat := 23187772074274194758989

theorem tailTrace_914450 : CollatzResearch.WordTrace tailWord_914450 prefixEnd_914450 23187772074274194758989 := by
  unfold tailWord_914450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8338182884277825117833201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22235154358074200314221869 8338182884277825117833201)
  ·
    refine ⟨6253637163208368838374901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8338182884277825117833201 6253637163208368838374901)
    ·
      refine ⟨586278484050784578597647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6253637163208368838374901 586278484050784578597647)
      ·
        refine ⟨879417726076176867896471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586278484050784578597647 879417726076176867896471)
        ·
          refine ⟨1319126589114265301844707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879417726076176867896471 1319126589114265301844707)
          ·
            refine ⟨1978689883671397952767061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319126589114265301844707 1978689883671397952767061)
            ·
              refine ⟨23187772074274194758989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1978689883671397952767061 23187772074274194758989)
              ·
                rfl

theorem cell21_914450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 8].length) (baseStart_914450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914450 prefixEnd_914450 := by exact prefixLift 914450
  have htrace : WordTrace (prefixWord ++ tailWord_914450) baseStart_914450 baseEnd_914450 := by
    simpa [prefixWord, tailWord_914450, baseEnd_914450] using wordTrace_append hprefix tailTrace_914450
  have hstable : (prefixWord ++ tailWord_914450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914450).length < 2 ^ (prefixWord ++ tailWord_914450).sum := by decide
  have hdescent : baseEnd_914450 < baseStart_914450 := by decide
  rcases family_descends (prefixWord ++ tailWord_914450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914464 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 5]
def baseStart_914464 : Nat := 118140960795 + 914464 * 2 ^ 59
def prefixEnd_914464 : Nat := 4983230072969 + 3 ^ 40 * 914464 * 2
def baseEnd_914464 : Nat := 208693143659206839597539

theorem tailTrace_914464 : CollatzResearch.WordTrace tailWord_914464 prefixEnd_914464 208693143659206839597539 := by
  unfold tailWord_914464
  simp only [CollatzResearch.WordTrace]
  refine ⟨16676621079530290431171223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22235494772707053908228297 16676621079530290431171223)
  ·
    refine ⟨25014931619295435646756835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16676621079530290431171223 25014931619295435646756835)
    ·
      refine ⟨37522397428943153470135253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25014931619295435646756835 37522397428943153470135253)
      ·
        refine ⟨879431189740855159456295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37522397428943153470135253 879431189740855159456295)
        ·
          refine ⟨1319146784611282739184443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879431189740855159456295 1319146784611282739184443)
          ·
            refine ⟨1978720176916924108776665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319146784611282739184443 1978720176916924108776665)
            ·
              refine ⟨1484040132687693081582499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978720176916924108776665 1484040132687693081582499)
              ·
                refine ⟨2226060199031539622373749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484040132687693081582499 2226060199031539622373749)
                ·
                  refine ⟨208693143659206839597539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2226060199031539622373749 208693143659206839597539)
                  ·
                    rfl

theorem cell21_914464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_914464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914464 prefixEnd_914464 := by exact prefixLift 914464
  have htrace : WordTrace (prefixWord ++ tailWord_914464) baseStart_914464 baseEnd_914464 := by
    simpa [prefixWord, tailWord_914464, baseEnd_914464] using wordTrace_append hprefix tailTrace_914464
  have hstable : (prefixWord ++ tailWord_914464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914464).length < 2 ^ (prefixWord ++ tailWord_914464).sum := by decide
  have hdescent : baseEnd_914464 < baseStart_914464 := by decide
  rcases family_descends (prefixWord ++ tailWord_914464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914492 : List Nat := [2, 2, 2, 2, 2, 2, 4, 5]
def baseStart_914492 : Nat := 118140960795 + 914492 * 2 ^ 59
def prefixEnd_914492 : Nat := 4983230072969 + 3 ^ 40 * 914492 * 2
def baseEnd_914492 : Nat := 69566511213561671043605

theorem tailTrace_914492 : CollatzResearch.WordTrace tailWord_914492 prefixEnd_914492 69566511213561671043605 := by
  unfold tailWord_914492
  simp only [CollatzResearch.WordTrace]
  refine ⟨16677131701479570822180865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22236175601972761096241153 16677131701479570822180865)
  ·
    refine ⟨12507848776109678116635649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16677131701479570822180865 12507848776109678116635649)
    ·
      refine ⟨9380886582082258587476737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12507848776109678116635649 9380886582082258587476737)
      ·
        refine ⟨7035664936561693940607553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9380886582082258587476737 7035664936561693940607553)
        ·
          refine ⟨5276748702421270455455665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7035664936561693940607553 5276748702421270455455665)
          ·
            refine ⟨3957561526815952841591749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5276748702421270455455665 3957561526815952841591749)
            ·
              refine ⟨742042786277991157798453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3957561526815952841591749 742042786277991157798453)
              ·
                refine ⟨69566511213561671043605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 742042786277991157798453 69566511213561671043605)
                ·
                  rfl

theorem cell21_914492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_914492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914492 prefixEnd_914492 := by exact prefixLift 914492
  have htrace : WordTrace (prefixWord ++ tailWord_914492) baseStart_914492 baseEnd_914492 := by
    simpa [prefixWord, tailWord_914492, baseEnd_914492] using wordTrace_append hprefix tailTrace_914492
  have hstable : (prefixWord ++ tailWord_914492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914492).length < 2 ^ (prefixWord ++ tailWord_914492).sum := by decide
  have hdescent : baseEnd_914492 < baseStart_914492 := by decide
  rcases family_descends (prefixWord ++ tailWord_914492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914520 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_914520 : Nat := 118140960795 + 914520 * 2 ^ 59
def prefixEnd_914520 : Nat := 4983230072969 + 3 ^ 40 * 914520 * 2
def baseEnd_914520 : Nat := 208705923622163186664091

theorem tailTrace_914520 : CollatzResearch.WordTrace tailWord_914520 prefixEnd_914520 208705923622163186664091 := by
  unfold tailWord_914520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16677642323428851213190507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22236856431238468284254009 16677642323428851213190507)
  ·
    refine ⟨25016463485143276819785761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16677642323428851213190507 25016463485143276819785761)
    ·
      refine ⟨18762347613857457614839321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25016463485143276819785761 18762347613857457614839321)
      ·
        refine ⟨14071760710393093211129491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18762347613857457614839321 14071760710393093211129491)
        ·
          refine ⟨21107641065589639816694237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14071760710393093211129491 21107641065589639816694237)
          ·
            refine ⟨7915365399596114931260339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21107641065589639816694237 7915365399596114931260339)
            ·
              refine ⟨11873048099394172396890509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915365399596114931260339 11873048099394172396890509)
              ·
                refine ⟨4452393037272814648833941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11873048099394172396890509 4452393037272814648833941)
                ·
                  refine ⟨208705923622163186664091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4452393037272814648833941 208705923622163186664091)
                  ·
                    rfl

theorem cell21_914520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_914520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914520 prefixEnd_914520 := by exact prefixLift 914520
  have htrace : WordTrace (prefixWord ++ tailWord_914520) baseStart_914520 baseEnd_914520 := by
    simpa [prefixWord, tailWord_914520, baseEnd_914520] using wordTrace_append hprefix tailTrace_914520
  have hstable : (prefixWord ++ tailWord_914520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914520).length < 2 ^ (prefixWord ++ tailWord_914520).sum := by decide
  have hdescent : baseEnd_914520 < baseStart_914520 := by decide
  rcases family_descends (prefixWord ++ tailWord_914520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914526 : List Nat := [4, 4, 1, 1, 1, 2, 2, 6]
def baseStart_914526 : Nat := 118140960795 + 914526 * 2 ^ 59
def prefixEnd_914526 : Nat := 4983230072969 + 3 ^ 40 * 914526 * 2
def baseEnd_914526 : Nat := 69569097634636169854693

theorem tailTrace_914526 : CollatzResearch.WordTrace tailWord_914526 prefixEnd_914526 69569097634636169854693 := by
  unfold tailWord_914526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4169437935604495681387429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22237002323223976967399621 4169437935604495681387429)
  ·
    refine ⟨781769612925842940260143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4169437935604495681387429 781769612925842940260143)
    ·
      refine ⟨1172654419388764410390215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781769612925842940260143 1172654419388764410390215)
      ·
        refine ⟨1758981629083146615585323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172654419388764410390215 1758981629083146615585323)
        ·
          refine ⟨2638472443624719923377985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758981629083146615585323 2638472443624719923377985)
          ·
            refine ⟨1978854332718539942533489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2638472443624719923377985 1978854332718539942533489)
            ·
              refine ⟨1484140749538904956900117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978854332718539942533489 1484140749538904956900117)
              ·
                refine ⟨69569097634636169854693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1484140749538904956900117 69569097634636169854693)
                ·
                  rfl

theorem cell21_914526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_914526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914526 prefixEnd_914526 := by exact prefixLift 914526
  have htrace : WordTrace (prefixWord ++ tailWord_914526) baseStart_914526 baseEnd_914526 := by
    simpa [prefixWord, tailWord_914526, baseEnd_914526] using wordTrace_append hprefix tailTrace_914526
  have hstable : (prefixWord ++ tailWord_914526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914526).length < 2 ^ (prefixWord ++ tailWord_914526).sum := by decide
  have hdescent : baseEnd_914526 < baseStart_914526 := by decide
  rcases family_descends (prefixWord ++ tailWord_914526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914537 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 4]
def baseStart_914537 : Nat := 118140960795 + 914537 * 2 ^ 59
def prefixEnd_914537 : Nat := 4983230072969 + 3 ^ 40 * 914537 * 2
def baseEnd_914537 : Nat := 208709803253774934880723

theorem tailTrace_914537 : CollatzResearch.WordTrace tailWord_914537 prefixEnd_914537 208709803253774934880723 := by
  unfold tailWord_914537
  simp only [CollatzResearch.WordTrace]
  refine ⟨33355904687796114329749865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22237269791864076219833243 33355904687796114329749865)
  ·
    refine ⟨25016928515847085747312399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33355904687796114329749865 25016928515847085747312399)
    ·
      refine ⟨37525392773770628620968599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25016928515847085747312399 37525392773770628620968599)
      ·
        refine ⟨56288089160655942931452899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37525392773770628620968599 56288089160655942931452899)
        ·
          refine ⟨84432133740983914397179349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56288089160655942931452899 84432133740983914397179349)
          ·
            refine ⟨1978878134554310493683891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 84432133740983914397179349 1978878134554310493683891)
            ·
              refine ⟨2968317201831465740525837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978878134554310493683891 2968317201831465740525837)
              ·
                refine ⟨1113118950686799652697189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2968317201831465740525837 1113118950686799652697189)
                ·
                  refine ⟨208709803253774934880723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1113118950686799652697189 208709803253774934880723)
                  ·
                    rfl

theorem cell21_914537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_914537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914537 prefixEnd_914537 := by exact prefixLift 914537
  have htrace : WordTrace (prefixWord ++ tailWord_914537) baseStart_914537 baseEnd_914537 := by
    simpa [prefixWord, tailWord_914537, baseEnd_914537] using wordTrace_append hprefix tailTrace_914537
  have hstable : (prefixWord ++ tailWord_914537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914537).length < 2 ^ (prefixWord ++ tailWord_914537).sum := by decide
  have hdescent : baseEnd_914537 < baseStart_914537 := by decide
  rcases family_descends (prefixWord ++ tailWord_914537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914568 : List Nat := [2, 1, 3, 4, 3, 8]
def baseStart_914568 : Nat := 118140960795 + 914568 * 2 ^ 59
def prefixEnd_914568 : Nat := 4983230072969 + 3 ^ 40 * 914568 * 2
def baseEnd_914568 : Nat := 7730254736152806291259

theorem tailTrace_914568 : CollatzResearch.WordTrace tailWord_914568 prefixEnd_914568 7730254736152806291259 := by
  unfold tailWord_914568
  simp only [CollatzResearch.WordTrace]
  refine ⟨16678517675341903312064179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22238023567122537749418905 16678517675341903312064179)
  ·
    refine ⟨25017776513012854968096269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16678517675341903312064179 25017776513012854968096269)
    ·
      refine ⟨9381666192379820613036101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25017776513012854968096269 9381666192379820613036101)
      ·
        refine ⟨1759062411071216364944269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9381666192379820613036101 1759062411071216364944269)
        ·
          refine ⟨659648404151706136854101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1759062411071216364944269 659648404151706136854101)
          ·
            refine ⟨7730254736152806291259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 659648404151706136854101 7730254736152806291259)
            ·
              rfl

theorem cell21_914568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 8].length) (baseStart_914568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914568 prefixEnd_914568 := by exact prefixLift 914568
  have htrace : WordTrace (prefixWord ++ tailWord_914568) baseStart_914568 baseEnd_914568 := by
    simpa [prefixWord, tailWord_914568, baseEnd_914568] using wordTrace_append hprefix tailTrace_914568
  have hstable : (prefixWord ++ tailWord_914568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914568).length < 2 ^ (prefixWord ++ tailWord_914568).sum := by decide
  have hdescent : baseEnd_914568 < baseStart_914568 := by decide
  rcases family_descends (prefixWord ++ tailWord_914568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914599 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 5]
def baseStart_914599 : Nat := 118140960795 + 914599 * 2 ^ 59
def prefixEnd_914599 : Nat := 4983230072969 + 3 ^ 40 * 914599 * 2
def baseEnd_914599 : Nat := 208723952498476604847263

theorem tailTrace_914599 : CollatzResearch.WordTrace tailWord_914599 prefixEnd_914599 208723952498476604847263 := by
  unfold tailWord_914599
  simp only [CollatzResearch.WordTrace]
  refine ⟨33358166013571498918506851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22238777342380999279004567 33358166013571498918506851)
  ·
    refine ⟨50037249020357248377760277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33358166013571498918506851 50037249020357248377760277)
    ·
      refine ⟨2345496047829246017707513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50037249020357248377760277 2345496047829246017707513)
      ·
        refine ⟨1759122035871934513280635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2345496047829246017707513 1759122035871934513280635)
        ·
          refine ⟨2638683053807901769920953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759122035871934513280635 2638683053807901769920953)
          ·
            refine ⟨1979012290355926327440715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2638683053807901769920953 1979012290355926327440715)
            ·
              refine ⟨2968518435533889491161073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979012290355926327440715 2968518435533889491161073)
              ·
                refine ⟨2226388826650417118370805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2968518435533889491161073 2226388826650417118370805)
                ·
                  refine ⟨208723952498476604847263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2226388826650417118370805 208723952498476604847263)
                  ·
                    rfl

theorem cell21_914599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 5].length) (baseStart_914599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914599 prefixEnd_914599 := by exact prefixLift 914599
  have htrace : WordTrace (prefixWord ++ tailWord_914599) baseStart_914599 baseEnd_914599 := by
    simpa [prefixWord, tailWord_914599, baseEnd_914599] using wordTrace_append hprefix tailTrace_914599
  have hstable : (prefixWord ++ tailWord_914599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914599).length < 2 ^ (prefixWord ++ tailWord_914599).sum := by decide
  have hdescent : baseEnd_914599 < baseStart_914599 := by decide
  rcases family_descends (prefixWord ++ tailWord_914599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914661 : List Nat := [1, 3, 1, 4, 3, 2, 2, 5]
def baseStart_914661 : Nat := 118140960795 + 914661 * 2 ^ 59
def prefixEnd_914661 : Nat := 4983230072969 + 3 ^ 40 * 914661 * 2
def baseEnd_914661 : Nat := 69579367247726091604601

theorem tailTrace_914661 : CollatzResearch.WordTrace tailWord_914661 prefixEnd_914661 69579367247726091604601 := by
  unfold tailWord_914661
  simp only [CollatzResearch.WordTrace]
  refine ⟨33360427339346883507263837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22240284892897922338175891 33360427339346883507263837)
  ·
    refine ⟨12510160252255081315223939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33360427339346883507263837 12510160252255081315223939)
    ·
      refine ⟨18765240378382621972835909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12510160252255081315223939 18765240378382621972835909)
      ·
        refine ⟨3518482570946741619906733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18765240378382621972835909 3518482570946741619906733)
        ·
          refine ⟨1319430964105028107465025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3518482570946741619906733 1319430964105028107465025)
          ·
            refine ⟨989573223078771080598769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1319430964105028107465025 989573223078771080598769)
            ·
              refine ⟨742179917309078310449077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989573223078771080598769 742179917309078310449077)
              ·
                refine ⟨69579367247726091604601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 742179917309078310449077 69579367247726091604601)
                ·
                  rfl

theorem cell21_914661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 5].length) (baseStart_914661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914661 prefixEnd_914661 := by exact prefixLift 914661
  have htrace : WordTrace (prefixWord ++ tailWord_914661) baseStart_914661 baseEnd_914661 := by
    simpa [prefixWord, tailWord_914661, baseEnd_914661] using wordTrace_append hprefix tailTrace_914661
  have hstable : (prefixWord ++ tailWord_914661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914661).length < 2 ^ (prefixWord ++ tailWord_914661).sum := by decide
  have hdescent : baseEnd_914661 < baseStart_914661 := by decide
  rcases family_descends (prefixWord ++ tailWord_914661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914675 : List Nat := [1, 1, 1, 2, 2, 5, 3, 3, 3]
def baseStart_914675 : Nat := 118140960795 + 914675 * 2 ^ 59
def prefixEnd_914675 : Nat := 4983230072969 + 3 ^ 40 * 914675 * 2
def baseEnd_914675 : Nat := 208741296733917361580441

theorem tailTrace_914675 : CollatzResearch.WordTrace tailWord_914675 prefixEnd_914675 208741296733917361580441 := by
  unfold tailWord_914675
  simp only [CollatzResearch.WordTrace]
  refine ⟨33360937961296163898273479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22240625307530775932182319 33360937961296163898273479)
  ·
    refine ⟨50041406941944245847410219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33360937961296163898273479 50041406941944245847410219)
    ·
      refine ⟨75062110412916368771115329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50041406941944245847410219 75062110412916368771115329)
      ·
        refine ⟨56296582809687276578336497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75062110412916368771115329 56296582809687276578336497)
        ·
          refine ⟨42222437107265457433752373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56296582809687276578336497 42222437107265457433752373)
          ·
            refine ⟨3958353478806136634414285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42222437107265457433752373 3958353478806136634414285)
            ·
              refine ⟨1484382554552301237905357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3958353478806136634414285 1484382554552301237905357)
              ·
                refine ⟨556643457957112964214509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1484382554552301237905357 556643457957112964214509)
                ·
                  refine ⟨208741296733917361580441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556643457957112964214509 208741296733917361580441)
                  ·
                    rfl

theorem cell21_914675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 3].length) (baseStart_914675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914675 prefixEnd_914675 := by exact prefixLift 914675
  have htrace : WordTrace (prefixWord ++ tailWord_914675) baseStart_914675 baseEnd_914675 := by
    simpa [prefixWord, tailWord_914675, baseEnd_914675] using wordTrace_append hprefix tailTrace_914675
  have hstable : (prefixWord ++ tailWord_914675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914675).length < 2 ^ (prefixWord ++ tailWord_914675).sum := by decide
  have hdescent : baseEnd_914675 < baseStart_914675 := by decide
  rcases family_descends (prefixWord ++ tailWord_914675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914751 : List Nat := [1, 1, 2, 2, 4, 3, 1, 4, 3]
def baseStart_914751 : Nat := 118140960795 + 914751 * 2 ^ 59
def prefixEnd_914751 : Nat := 4983230072969 + 3 ^ 40 * 914751 * 2
def baseEnd_914751 : Nat := 208758640969358118313619

theorem tailTrace_914751 : CollatzResearch.WordTrace tailWord_914751 prefixEnd_914751 208758640969358118313619 := by
  unfold tailWord_914751
  simp only [CollatzResearch.WordTrace]
  refine ⟨33363709909020828878040107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22242473272680552585360071 33363709909020828878040107)
  ·
    refine ⟨50045564863531243317060161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33363709909020828878040107 50045564863531243317060161)
    ·
      refine ⟨37534173647648432487795121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50045564863531243317060161 37534173647648432487795121)
      ·
        refine ⟨28150630235736324365846341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37534173647648432487795121 28150630235736324365846341)
        ·
          refine ⟨5278243169200560818596189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28150630235736324365846341 5278243169200560818596189)
          ·
            refine ⟨1979341188450210306973571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5278243169200560818596189 1979341188450210306973571)
            ·
              refine ⟨2969011782675315460460357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979341188450210306973571 2969011782675315460460357)
              ·
                refine ⟨556689709251621648836317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2969011782675315460460357 556689709251621648836317)
                ·
                  refine ⟨208758640969358118313619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556689709251621648836317 208758640969358118313619)
                  ·
                    rfl

theorem cell21_914751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 3].length) (baseStart_914751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914751 prefixEnd_914751 := by exact prefixLift 914751
  have htrace : WordTrace (prefixWord ++ tailWord_914751) baseStart_914751 baseEnd_914751 := by
    simpa [prefixWord, tailWord_914751, baseEnd_914751] using wordTrace_append hprefix tailTrace_914751
  have hstable : (prefixWord ++ tailWord_914751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914751).length < 2 ^ (prefixWord ++ tailWord_914751).sum := by decide
  have hdescent : baseEnd_914751 < baseStart_914751 := by decide
  rcases family_descends (prefixWord ++ tailWord_914751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914830 : List Nat := [4, 1, 1, 4, 3, 1, 2, 5]
def baseStart_914830 : Nat := 118140960795 + 914830 * 2 ^ 59
def prefixEnd_914830 : Nat := 4983230072969 + 3 ^ 40 * 914830 * 2
def baseEnd_914830 : Nat := 69592223281890512165597

theorem tailTrace_914830 : CollatzResearch.WordTrace tailWord_914830 prefixEnd_914830 69592223281890512165597 := by
  unfold tailWord_914830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4170823909466828171270743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22244394183823083580110629 4170823909466828171270743)
  ·
    refine ⟨6256235864200242256906115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4170823909466828171270743 6256235864200242256906115)
    ·
      refine ⟨9384353796300363385359173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6256235864200242256906115 9384353796300363385359173)
      ·
        refine ⟨1759566336806318134754845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9384353796300363385359173 1759566336806318134754845)
        ·
          refine ⟨659837376302369300533067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1759566336806318134754845 659837376302369300533067)
          ·
            refine ⟨989756064453553950799601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659837376302369300533067 989756064453553950799601)
            ·
              refine ⟨742317048340165463099701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989756064453553950799601 742317048340165463099701)
              ·
                refine ⟨69592223281890512165597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 742317048340165463099701 69592223281890512165597)
                ·
                  rfl

theorem cell21_914830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_914830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914830 prefixEnd_914830 := by exact prefixLift 914830
  have htrace : WordTrace (prefixWord ++ tailWord_914830) baseStart_914830 baseEnd_914830 := by
    simpa [prefixWord, tailWord_914830, baseEnd_914830] using wordTrace_append hprefix tailTrace_914830
  have hstable : (prefixWord ++ tailWord_914830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914830).length < 2 ^ (prefixWord ++ tailWord_914830).sum := by decide
  have hdescent : baseEnd_914830 < baseStart_914830 := by decide
  rcases family_descends (prefixWord ++ tailWord_914830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914861 : List Nat := [1, 5, 2, 2, 1, 2, 3, 2, 3]
def baseStart_914861 : Nat := 118140960795 + 914861 * 2 ^ 59
def prefixEnd_914861 : Nat := 4983230072969 + 3 ^ 40 * 914861 * 2
def baseEnd_914861 : Nat := 208783744468022371480061

theorem tailTrace_914861 : CollatzResearch.WordTrace tailWord_914861 prefixEnd_914861 208783744468022371480061 := by
  unfold tailWord_914861
  simp only [CollatzResearch.WordTrace]
  refine ⟨33367721938622317664544437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22245147959081545109696291 33367721938622317664544437)
  ·
    refine ⟨3128223931745842281051041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33367721938622317664544437 3128223931745842281051041)
    ·
      refine ⟨2346167948809381710788281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3128223931745842281051041 2346167948809381710788281)
      ·
        refine ⟨1759625961607036283091211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2346167948809381710788281 1759625961607036283091211)
        ·
          refine ⟨2639438942410554424636817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759625961607036283091211 2639438942410554424636817)
          ·
            refine ⟨1979579206807915818477613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2639438942410554424636817 1979579206807915818477613)
            ·
              refine ⟨742342202552968431929105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1979579206807915818477613 742342202552968431929105)
              ·
                refine ⟨556756651914726323946829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742342202552968431929105 556756651914726323946829)
                ·
                  refine ⟨208783744468022371480061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556756651914726323946829 208783744468022371480061)
                  ·
                    rfl

theorem cell21_914861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_914861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914861 prefixEnd_914861 := by exact prefixLift 914861
  have htrace : WordTrace (prefixWord ++ tailWord_914861) baseStart_914861 baseEnd_914861 := by
    simpa [prefixWord, tailWord_914861, baseEnd_914861] using wordTrace_append hprefix tailTrace_914861
  have hstable : (prefixWord ++ tailWord_914861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914861).length < 2 ^ (prefixWord ++ tailWord_914861).sum := by decide
  have hdescent : baseEnd_914861 < baseStart_914861 := by decide
  rcases family_descends (prefixWord ++ tailWord_914861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914917 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 4]
def baseStart_914917 : Nat := 118140960795 + 914917 * 2 ^ 59
def prefixEnd_914917 : Nat := 4983230072969 + 3 ^ 40 * 914917 * 2
def baseEnd_914917 : Nat := 208796524430978718546613

theorem tailTrace_914917 : CollatzResearch.WordTrace tailWord_914917 prefixEnd_914917 208796524430978718546613 := by
  unfold tailWord_914917
  simp only [CollatzResearch.WordTrace]
  refine ⟨33369764426419439228583005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22246509617612959485722003 33369764426419439228583005)
  ·
    refine ⟨12513661659907289710718627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33369764426419439228583005 12513661659907289710718627)
    ·
      refine ⟨18770492489860934566077941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12513661659907289710718627 18770492489860934566077941)
      ·
        refine ⟨1759733670924462615569807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18770492489860934566077941 1759733670924462615569807)
        ·
          refine ⟨2639600506386693923354711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759733670924462615569807 2639600506386693923354711)
          ·
            refine ⟨3959400759580040885032067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639600506386693923354711 3959400759580040885032067)
            ·
              refine ⟨5939101139370061327548101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959400759580040885032067 5939101139370061327548101)
              ·
                refine ⟨1113581463631886498915269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5939101139370061327548101 1113581463631886498915269)
                ·
                  refine ⟨208796524430978718546613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1113581463631886498915269 208796524430978718546613)
                  ·
                    rfl

theorem cell21_914917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_914917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_914917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_914917 prefixEnd_914917 := by exact prefixLift 914917
  have htrace : WordTrace (prefixWord ++ tailWord_914917) baseStart_914917 baseEnd_914917 := by
    simpa [prefixWord, tailWord_914917, baseEnd_914917] using wordTrace_append hprefix tailTrace_914917
  have hstable : (prefixWord ++ tailWord_914917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914917).length < 2 ^ (prefixWord ++ tailWord_914917).sum := by decide
  have hdescent : baseEnd_914917 < baseStart_914917 := by decide
  rcases family_descends (prefixWord ++ tailWord_914917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915007 : List Nat := [1, 1, 2, 2, 3, 3, 4, 5]
def baseStart_915007 : Nat := 118140960795 + 915007 * 2 ^ 59
def prefixEnd_915007 : Nat := 4983230072969 + 3 ^ 40 * 915007 * 2
def baseEnd_915007 : Nat := 69605687885719520682143

theorem tailTrace_915007 : CollatzResearch.WordTrace tailWord_915007 prefixEnd_915007 69605687885719520682143 := by
  unfold tailWord_915007
  simp only [CollatzResearch.WordTrace]
  refine ⟨33373046996093384599359275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22248697997395589732906183 33373046996093384599359275)
  ·
    refine ⟨50059570494140076899038913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33373046996093384599359275 50059570494140076899038913)
    ·
      refine ⟨37544677870605057674279185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50059570494140076899038913 37544677870605057674279185)
      ·
        refine ⟨28158508402953793255709389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37544677870605057674279185 28158508402953793255709389)
        ·
          refine ⟨10559440651107672470891021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28158508402953793255709389 10559440651107672470891021)
          ·
            refine ⟨3959790244165377176584133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10559440651107672470891021 3959790244165377176584133)
            ·
              refine ⟨742460670781008220609525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3959790244165377176584133 742460670781008220609525)
              ·
                refine ⟨69605687885719520682143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 742460670781008220609525 69605687885719520682143)
                ·
                  rfl

theorem cell21_915007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5].length) (baseStart_915007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915007 prefixEnd_915007 := by exact prefixLift 915007
  have htrace : WordTrace (prefixWord ++ tailWord_915007) baseStart_915007 baseEnd_915007 := by
    simpa [prefixWord, tailWord_915007, baseEnd_915007] using wordTrace_append hprefix tailTrace_915007
  have hstable : (prefixWord ++ tailWord_915007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915007).length < 2 ^ (prefixWord ++ tailWord_915007).sum := by decide
  have hdescent : baseEnd_915007 < baseStart_915007 := by decide
  rcases family_descends (prefixWord ++ tailWord_915007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915030 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_915030 : Nat := 118140960795 + 915030 * 2 ^ 59
def prefixEnd_915030 : Nat := 4983230072969 + 3 ^ 40 * 915030 * 2
def baseEnd_915030 : Nat := 208822312570515633163049

theorem tailTrace_915030 : CollatzResearch.WordTrace tailWord_915030 prefixEnd_915030 208822312570515633163049 := by
  unfold tailWord_915030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2085867867188128720465409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22249257250006706351631029 2085867867188128720465409)
  ·
    refine ⟨1564400900391096540349057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2085867867188128720465409 1564400900391096540349057)
    ·
      refine ⟨1173300675293322405261793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1564400900391096540349057 1173300675293322405261793)
      ·
        refine ⟨879975506469991803946345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1173300675293322405261793 879975506469991803946345)
        ·
          refine ⟨659981629852493852959759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 879975506469991803946345 659981629852493852959759)
          ·
            refine ⟨989972444778740779439639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659981629852493852959759 989972444778740779439639)
            ·
              refine ⟨1484958667168111169159459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989972444778740779439639 1484958667168111169159459)
              ·
                refine ⟨2227438000752166753739189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484958667168111169159459 2227438000752166753739189)
                ·
                  refine ⟨208822312570515633163049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2227438000752166753739189 208822312570515633163049)
                  ·
                    rfl

theorem cell21_915030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_915030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915030 prefixEnd_915030 := by exact prefixLift 915030
  have htrace : WordTrace (prefixWord ++ tailWord_915030) baseStart_915030 baseEnd_915030 := by
    simpa [prefixWord, tailWord_915030, baseEnd_915030] using wordTrace_append hprefix tailTrace_915030
  have hstable : (prefixWord ++ tailWord_915030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915030).length < 2 ^ (prefixWord ++ tailWord_915030).sum := by decide
  have hdescent : baseEnd_915030 < baseStart_915030 := by decide
  rcases family_descends (prefixWord ++ tailWord_915030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915100 : List Nat := [2, 2, 3, 2, 3, 2, 1, 6]
def baseStart_915100 : Nat := 118140960795 + 915100 * 2 ^ 59
def prefixEnd_915100 : Nat := 4983230072969 + 3 ^ 40 * 915100 * 2
def baseEnd_915100 : Nat := 69612762508070355665413

theorem tailTrace_915100 : CollatzResearch.WordTrace tailWord_915100 prefixEnd_915100 69612762508070355665413 := by
  unfold tailWord_915100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16688219492378230741247377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22250959323170974321663169 16688219492378230741247377)
  ·
    refine ⟨12516164619283673055935533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16688219492378230741247377 12516164619283673055935533)
    ·
      refine ⟨4693561732231377395975825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12516164619283673055935533 4693561732231377395975825)
      ·
        refine ⟨3520171299173533046981869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4693561732231377395975825 3520171299173533046981869)
        ·
          refine ⟨1320064237190074892618201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3520171299173533046981869 1320064237190074892618201)
          ·
            refine ⟨990048177892556169463651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320064237190074892618201 990048177892556169463651)
            ·
              refine ⟨1485072266838834254195477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990048177892556169463651 1485072266838834254195477)
              ·
                refine ⟨69612762508070355665413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1485072266838834254195477 69612762508070355665413)
                ·
                  rfl

theorem cell21_915100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_915100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915100 prefixEnd_915100 := by exact prefixLift 915100
  have htrace : WordTrace (prefixWord ++ tailWord_915100) baseStart_915100 baseEnd_915100 := by
    simpa [prefixWord, tailWord_915100, baseEnd_915100] using wordTrace_append hprefix tailTrace_915100
  have hstable : (prefixWord ++ tailWord_915100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915100).length < 2 ^ (prefixWord ++ tailWord_915100).sum := by decide
  have hdescent : baseEnd_915100 < baseStart_915100 := by decide
  rcases family_descends (prefixWord ++ tailWord_915100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915173 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 5]
def baseStart_915173 : Nat := 118140960795 + 915173 * 2 ^ 59
def prefixEnd_915173 : Nat := 4983230072969 + 3 ^ 40 * 915173 * 2
def baseEnd_915173 : Nat := 208854947118779162279423

theorem tailTrace_915173 : CollatzResearch.WordTrace tailWord_915173 prefixEnd_915173 208854947118779162279423 := by
  unfold tailWord_915173
  simp only [CollatzResearch.WordTrace]
  refine ⟨33379101513491994949902173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22252734342327996633268115 33379101513491994949902173)
  ·
    refine ⟨12517163067559498106213315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33379101513491994949902173 12517163067559498106213315)
    ·
      refine ⟨18775744601339247159319973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12517163067559498106213315 18775744601339247159319973)
      ·
        refine ⟨3520452112751108842372495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18775744601339247159319973 3520452112751108842372495)
        ·
          refine ⟨5280678169126663263558743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520452112751108842372495 5280678169126663263558743)
          ·
            refine ⟨7921017253689994895338115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280678169126663263558743 7921017253689994895338115)
            ·
              refine ⟨11881525880534992343007173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7921017253689994895338115 11881525880534992343007173)
              ·
                refine ⟨2227786102600311064313845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11881525880534992343007173 2227786102600311064313845)
                ·
                  refine ⟨208854947118779162279423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2227786102600311064313845 208854947118779162279423)
                  ·
                    rfl

theorem cell21_915173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_915173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915173 prefixEnd_915173 := by exact prefixLift 915173
  have htrace : WordTrace (prefixWord ++ tailWord_915173) baseStart_915173 baseEnd_915173 := by
    simpa [prefixWord, tailWord_915173, baseEnd_915173] using wordTrace_append hprefix tailTrace_915173
  have hstable : (prefixWord ++ tailWord_915173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915173).length < 2 ^ (prefixWord ++ tailWord_915173).sum := by decide
  have hdescent : baseEnd_915173 < baseStart_915173 := by decide
  rcases family_descends (prefixWord ++ tailWord_915173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915176 : List Nat := [2, 1, 4, 1, 3, 3, 2, 5]
def baseStart_915176 : Nat := 118140960795 + 915176 * 2 ^ 59
def prefixEnd_915176 : Nat := 4983230072969 + 3 ^ 40 * 915176 * 2
def baseEnd_915176 : Nat := 69618543919883941243139

theorem tailTrace_915176 : CollatzResearch.WordTrace tailWord_915176 prefixEnd_915176 69618543919883941243139 := by
  unfold tailWord_915176
  simp only [CollatzResearch.WordTrace]
  refine ⟨16689605466240563231130691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22252807288320750974840921 16689605466240563231130691)
  ·
    refine ⟨25034408199360844846696037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16689605466240563231130691 25034408199360844846696037)
    ·
      refine ⟨4693951537380158408755507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25034408199360844846696037 4693951537380158408755507)
      ·
        refine ⟨7040927306070237613133261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4693951537380158408755507 7040927306070237613133261)
        ·
          refine ⟨2640347739776339104924973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7040927306070237613133261 2640347739776339104924973)
          ·
            refine ⟨990130402416127164346865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2640347739776339104924973 990130402416127164346865)
            ·
              refine ⟨742597801812095373260149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990130402416127164346865 742597801812095373260149)
              ·
                refine ⟨69618543919883941243139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 742597801812095373260149 69618543919883941243139)
                ·
                  rfl

theorem cell21_915176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_915176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915176 prefixEnd_915176 := by exact prefixLift 915176
  have htrace : WordTrace (prefixWord ++ tailWord_915176) baseStart_915176 baseEnd_915176 := by
    simpa [prefixWord, tailWord_915176, baseEnd_915176] using wordTrace_append hprefix tailTrace_915176
  have hstable : (prefixWord ++ tailWord_915176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915176).length < 2 ^ (prefixWord ++ tailWord_915176).sum := by decide
  have hdescent : baseEnd_915176 < baseStart_915176 := by decide
  rcases family_descends (prefixWord ++ tailWord_915176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915187 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 6]
def baseStart_915187 : Nat := 118140960795 + 915187 * 2 ^ 59
def prefixEnd_915187 : Nat := 4983230072969 + 3 ^ 40 * 915187 * 2
def baseEnd_915187 : Nat := 208858142109518249046061

theorem tailTrace_915187 : CollatzResearch.WordTrace tailWord_915187 prefixEnd_915187 208858142109518249046061 := by
  unfold tailWord_915187
  simp only [CollatzResearch.WordTrace]
  refine ⟨33379612135441275340911815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22253074756960850227274543 33379612135441275340911815)
  ·
    refine ⟨50069418203161913011367723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33379612135441275340911815 50069418203161913011367723)
    ·
      refine ⟨75104127304742869517051585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50069418203161913011367723 75104127304742869517051585)
      ·
        refine ⟨56328095478557152137788689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75104127304742869517051585 56328095478557152137788689)
        ·
          refine ⟨42246071608917864103341517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56328095478557152137788689 42246071608917864103341517)
          ·
            refine ⟨15842276853344199038753069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42246071608917864103341517 15842276853344199038753069)
            ·
              refine ⟨5940853820004074639532401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15842276853344199038753069 5940853820004074639532401)
              ·
                refine ⟨4455640365003055979649301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5940853820004074639532401 4455640365003055979649301)
                ·
                  refine ⟨208858142109518249046061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4455640365003055979649301 208858142109518249046061)
                  ·
                    rfl

theorem cell21_915187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_915187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915187 prefixEnd_915187 := by exact prefixLift 915187
  have htrace : WordTrace (prefixWord ++ tailWord_915187) baseStart_915187 baseEnd_915187 := by
    simpa [prefixWord, tailWord_915187, baseEnd_915187] using wordTrace_append hprefix tailTrace_915187
  have hstable : (prefixWord ++ tailWord_915187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915187).length < 2 ^ (prefixWord ++ tailWord_915187).sum := by decide
  have hdescent : baseEnd_915187 < baseStart_915187 := by decide
  rcases family_descends (prefixWord ++ tailWord_915187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915204 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_915204 : Nat := 118140960795 + 915204 * 2 ^ 59
def prefixEnd_915204 : Nat := 4983230072969 + 3 ^ 40 * 915204 * 2
def baseEnd_915204 : Nat := 208862021741129997262693

theorem tailTrace_915204 : CollatzResearch.WordTrace tailWord_915204 prefixEnd_915204 208862021741129997262693 := by
  unfold tailWord_915204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16690116088189843622140333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22253488117586458162853777 16690116088189843622140333)
  ·
    refine ⟨6258793533071191358302625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16690116088189843622140333 6258793533071191358302625)
    ·
      refine ⟨4694095149803393518726969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6258793533071191358302625 4694095149803393518726969)
      ·
        refine ⟨3520571362352545139045227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4694095149803393518726969 3520571362352545139045227)
        ·
          refine ⟨5280857043528817708567841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520571362352545139045227 5280857043528817708567841)
          ·
            refine ⟨3960642782646613281425881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5280857043528817708567841 3960642782646613281425881)
            ·
              refine ⟨2970482086984959961069411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960642782646613281425881 2970482086984959961069411)
              ·
                refine ⟨4455723130477439941604117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970482086984959961069411 4455723130477439941604117)
                ·
                  refine ⟨208862021741129997262693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4455723130477439941604117 208862021741129997262693)
                  ·
                    rfl

theorem cell21_915204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_915204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915204 prefixEnd_915204 := by exact prefixLift 915204
  have htrace : WordTrace (prefixWord ++ tailWord_915204) baseStart_915204 baseEnd_915204 := by
    simpa [prefixWord, tailWord_915204, baseEnd_915204] using wordTrace_append hprefix tailTrace_915204
  have hstable : (prefixWord ++ tailWord_915204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915204).length < 2 ^ (prefixWord ++ tailWord_915204).sum := by decide
  have hdescent : baseEnd_915204 < baseStart_915204 := by decide
  rcases family_descends (prefixWord ++ tailWord_915204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915207 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 5]
def baseStart_915207 : Nat := 118140960795 + 915207 * 2 ^ 59
def prefixEnd_915207 : Nat := 4983230072969 + 3 ^ 40 * 915207 * 2
def baseEnd_915207 : Nat := 208862706382002658712687

theorem tailTrace_915207 : CollatzResearch.WordTrace tailWord_915207 prefixEnd_915207 208862706382002658712687 := by
  unfold tailWord_915207
  simp only [CollatzResearch.WordTrace]
  refine ⟨33380341595368818756639875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22253561063579212504426583 33380341595368818756639875)
  ·
    refine ⟨50070512393053228134959813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33380341595368818756639875 50070512393053228134959813)
    ·
      refine ⟨9388221073697480275304965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50070512393053228134959813 9388221073697480275304965)
      ·
        refine ⟨1760291451318277551619681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9388221073697480275304965 1760291451318277551619681)
        ·
          refine ⟨1320218588488708163714761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1760291451318277551619681 1320218588488708163714761)
          ·
            refine ⟨990163941366531122786071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320218588488708163714761 990163941366531122786071)
            ·
              refine ⟨1485245912049796684179107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990163941366531122786071 1485245912049796684179107)
              ·
                refine ⟨2227868868074695026268661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485245912049796684179107 2227868868074695026268661)
                ·
                  refine ⟨208862706382002658712687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2227868868074695026268661 208862706382002658712687)
                  ·
                    rfl

theorem cell21_915207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 5].length) (baseStart_915207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915207 prefixEnd_915207 := by exact prefixLift 915207
  have htrace : WordTrace (prefixWord ++ tailWord_915207) baseStart_915207 baseEnd_915207 := by
    simpa [prefixWord, tailWord_915207, baseEnd_915207] using wordTrace_append hprefix tailTrace_915207
  have hstable : (prefixWord ++ tailWord_915207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915207).length < 2 ^ (prefixWord ++ tailWord_915207).sum := by decide
  have hdescent : baseEnd_915207 < baseStart_915207 := by decide
  rcases family_descends (prefixWord ++ tailWord_915207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915221 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 4]
def baseStart_915221 : Nat := 118140960795 + 915221 * 2 ^ 59
def prefixEnd_915221 : Nat := 4983230072969 + 3 ^ 40 * 915221 * 2
def baseEnd_915221 : Nat := 208865901372741745479325

theorem tailTrace_915221 : CollatzResearch.WordTrace tailWord_915221 prefixEnd_915221 208865901372741745479325 := by
  unfold tailWord_915221
  simp only [CollatzResearch.WordTrace]
  refine ⟨33380852217318099147649517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22253901478212066098433011 33380852217318099147649517)
  ·
    refine ⟨12517819581494287180368569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33380852217318099147649517 12517819581494287180368569)
    ·
      refine ⟨9388364686120715385276427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12517819581494287180368569 9388364686120715385276427)
      ·
        refine ⟨14082547029181073077914641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9388364686120715385276427 14082547029181073077914641)
        ·
          refine ⟨10561910271885804808435981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14082547029181073077914641 10561910271885804808435981)
          ·
            refine ⟨3960716351957176803163493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10561910271885804808435981 3960716351957176803163493)
            ·
              refine ⟨742634315991970650593155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3960716351957176803163493 742634315991970650593155)
              ·
                refine ⟨1113951473987955975889733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742634315991970650593155 1113951473987955975889733)
                ·
                  refine ⟨208865901372741745479325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1113951473987955975889733 208865901372741745479325)
                  ·
                    rfl

theorem cell21_915221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_915221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915221 prefixEnd_915221 := by exact prefixLift 915221
  have htrace : WordTrace (prefixWord ++ tailWord_915221) baseStart_915221 baseEnd_915221 := by
    simpa [prefixWord, tailWord_915221, baseEnd_915221] using wordTrace_append hprefix tailTrace_915221
  have hstable : (prefixWord ++ tailWord_915221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915221).length < 2 ^ (prefixWord ++ tailWord_915221).sum := by decide
  have hdescent : baseEnd_915221 < baseStart_915221 := by decide
  rcases family_descends (prefixWord ++ tailWord_915221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915356 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 6]
def baseStart_915356 : Nat := 118140960795 + 915356 * 2 ^ 59
def prefixEnd_915356 : Nat := 4983230072969 + 3 ^ 40 * 915356 * 2
def baseEnd_915356 : Nat := 208896710212011510729049

theorem tailTrace_915356 : CollatzResearch.WordTrace tailWord_915356 prefixEnd_915356 208896710212011510729049 := by
  unfold tailWord_915356
  simp only [CollatzResearch.WordTrace]
  refine ⟨16692888035914508601906961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22257184047886011469209281 16692888035914508601906961)
  ·
    refine ⟨12519666026935881451430221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16692888035914508601906961 12519666026935881451430221)
    ·
      refine ⟨4694874760100955544286333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12519666026935881451430221 4694874760100955544286333)
      ·
        refine ⟨1760578035037858329107375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4694874760100955544286333 1760578035037858329107375)
        ·
          refine ⟨2640867052556787493661063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760578035037858329107375 2640867052556787493661063)
          ·
            refine ⟨3961300578835181240491595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640867052556787493661063 3961300578835181240491595)
            ·
              refine ⟨5941950868252771860737393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961300578835181240491595 5941950868252771860737393)
              ·
                refine ⟨4456463151189578895553045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5941950868252771860737393 4456463151189578895553045)
                ·
                  refine ⟨208896710212011510729049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4456463151189578895553045 208896710212011510729049)
                  ·
                    rfl

theorem cell21_915356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_915356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915356 prefixEnd_915356 := by exact prefixLift 915356
  have htrace : WordTrace (prefixWord ++ tailWord_915356) baseStart_915356 baseEnd_915356 := by
    simpa [prefixWord, tailWord_915356, baseEnd_915356] using wordTrace_append hprefix tailTrace_915356
  have hstable : (prefixWord ++ tailWord_915356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915356).length < 2 ^ (prefixWord ++ tailWord_915356).sum := by decide
  have hdescent : baseEnd_915356 < baseStart_915356 := by decide
  rcases family_descends (prefixWord ++ tailWord_915356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915390 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_915390 : Nat := 118140960795 + 915390 * 2 ^ 59
def prefixEnd_915390 : Nat := 4983230072969 + 3 ^ 40 * 915390 * 2
def baseEnd_915390 : Nat := 208904469475235007162313

theorem tailTrace_915390 : CollatzResearch.WordTrace tailWord_915390 prefixEnd_915390 208904469475235007162313 := by
  unfold tailWord_915390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4173377019213230126318953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22258010769137227340367749 4173377019213230126318953)
  ·
    refine ⟨3130032764409922594739215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4173377019213230126318953 3130032764409922594739215)
    ·
      refine ⟨4695049146614883892108823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3130032764409922594739215 4695049146614883892108823)
      ·
        refine ⟨7042573719922325838163235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4695049146614883892108823 7042573719922325838163235)
        ·
          refine ⟨10563860579883488757244853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7042573719922325838163235 10563860579883488757244853)
          ·
            refine ⟨990361929364077070991705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10563860579883488757244853 990361929364077070991705)
            ·
              refine ⟨742771447023057803243779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990361929364077070991705 742771447023057803243779)
              ·
                refine ⟨1114157170534586704865669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742771447023057803243779 1114157170534586704865669)
                ·
                  refine ⟨208904469475235007162313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114157170534586704865669 208904469475235007162313)
                  ·
                    rfl

theorem cell21_915390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_915390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915390 prefixEnd_915390 := by exact prefixLift 915390
  have htrace : WordTrace (prefixWord ++ tailWord_915390) baseStart_915390 baseEnd_915390 := by
    simpa [prefixWord, tailWord_915390, baseEnd_915390] using wordTrace_append hprefix tailTrace_915390
  have hstable : (prefixWord ++ tailWord_915390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915390).length < 2 ^ (prefixWord ++ tailWord_915390).sum := by decide
  have hdescent : baseEnd_915390 < baseStart_915390 := by decide
  rcases family_descends (prefixWord ++ tailWord_915390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915429 : List Nat := [1, 3, 1, 16]
def baseStart_915429 : Nat := 118140960795 + 915429 * 2 ^ 59
def prefixEnd_915429 : Nat := 4983230072969 + 3 ^ 40 * 915429 * 2
def baseEnd_915429 : Nat := 859725801673167102931

theorem tailTrace_915429 : CollatzResearch.WordTrace tailWord_915429 prefixEnd_915429 859725801673167102931 := by
  unfold tailWord_915429
  simp only [CollatzResearch.WordTrace]
  refine ⟨33388438600564550671221341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22258959067043033780814227 33388438600564550671221341)
  ·
    refine ⟨12520664475211706501708003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33388438600564550671221341 12520664475211706501708003)
    ·
      refine ⟨18780996712817559752562005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12520664475211706501708003 18780996712817559752562005)
      ·
        refine ⟨859725801673167102931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 18780996712817559752562005 859725801673167102931)
        ·
          rfl

theorem cell21_915429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 16].length) (baseStart_915429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915429 prefixEnd_915429 := by exact prefixLift 915429
  have htrace : WordTrace (prefixWord ++ tailWord_915429) baseStart_915429 baseEnd_915429 := by
    simpa [prefixWord, tailWord_915429, baseEnd_915429] using wordTrace_append hprefix tailTrace_915429
  have hstable : (prefixWord ++ tailWord_915429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915429).length < 2 ^ (prefixWord ++ tailWord_915429).sum := by decide
  have hdescent : baseEnd_915429 < baseStart_915429 := by decide
  rcases family_descends (prefixWord ++ tailWord_915429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915463 : List Nat := [1, 1, 4, 3, 1, 3, 3, 5]
def baseStart_915463 : Nat := 118140960795 + 915463 * 2 ^ 59
def prefixEnd_915463 : Nat := 4983230072969 + 3 ^ 40 * 915463 * 2
def baseEnd_915463 : Nat := 69640376356601034148499

theorem tailTrace_915463 : CollatzResearch.WordTrace tailWord_915463 prefixEnd_915463 69640376356601034148499 := by
  unfold tailWord_915463
  simp only [CollatzResearch.WordTrace]
  refine ⟨33389678682441374477959043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22259785788294249651972695 33389678682441374477959043)
  ·
    refine ⟨50084518023662061716938565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33389678682441374477959043 50084518023662061716938565)
    ·
      refine ⟨9390847129436636571925981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50084518023662061716938565 9390847129436636571925981)
      ·
        refine ⟨3521567673538738714472243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9390847129436636571925981 3521567673538738714472243)
        ·
          refine ⟨5282351510308108071708365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3521567673538738714472243 5282351510308108071708365)
          ·
            refine ⟨1980881816365540526890637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5282351510308108071708365 1980881816365540526890637)
            ·
              refine ⟨742830681137077697583989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1980881816365540526890637 742830681137077697583989)
              ·
                refine ⟨69640376356601034148499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 742830681137077697583989 69640376356601034148499)
                ·
                  rfl

theorem cell21_915463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 5].length) (baseStart_915463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915463 prefixEnd_915463 := by exact prefixLift 915463
  have htrace : WordTrace (prefixWord ++ tailWord_915463) baseStart_915463 baseEnd_915463 := by
    simpa [prefixWord, tailWord_915463, baseEnd_915463] using wordTrace_append hprefix tailTrace_915463
  have hstable : (prefixWord ++ tailWord_915463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915463).length < 2 ^ (prefixWord ++ tailWord_915463).sum := by decide
  have hdescent : baseEnd_915463 < baseStart_915463 := by decide
  rcases family_descends (prefixWord ++ tailWord_915463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915491 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 6]
def baseStart_915491 : Nat := 118140960795 + 915491 * 2 ^ 59
def prefixEnd_915491 : Nat := 4983230072969 + 3 ^ 40 * 915491 * 2
def baseEnd_915491 : Nat := 208927519051281275978773

theorem tailTrace_915491 : CollatzResearch.WordTrace tailWord_915491 prefixEnd_915491 208927519051281275978773 := by
  unfold tailWord_915491
  simp only [CollatzResearch.WordTrace]
  refine ⟨33390699926339935259978327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22260466617559956839985551 33390699926339935259978327)
  ·
    refine ⟨50086049889509902889967491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33390699926339935259978327 50086049889509902889967491)
    ·
      refine ⟨75129074834264854334951237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50086049889509902889967491 75129074834264854334951237)
      ·
        refine ⟨14086701531424660187803357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75129074834264854334951237 14086701531424660187803357)
        ·
          refine ⟨5282513074284247570426259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14086701531424660187803357 5282513074284247570426259)
          ·
            refine ⟨7923769611426371355639389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5282513074284247570426259 7923769611426371355639389)
            ·
              refine ⟨2971413604284889258364771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7923769611426371355639389 2971413604284889258364771)
              ·
                refine ⟨4457120406427333887547157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971413604284889258364771 4457120406427333887547157)
                ·
                  refine ⟨208927519051281275978773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4457120406427333887547157 208927519051281275978773)
                  ·
                    rfl

theorem cell21_915491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_915491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915491 prefixEnd_915491 := by exact prefixLift 915491
  have htrace : WordTrace (prefixWord ++ tailWord_915491) baseStart_915491 baseEnd_915491 := by
    simpa [prefixWord, tailWord_915491, baseEnd_915491] using wordTrace_append hprefix tailTrace_915491
  have hstable : (prefixWord ++ tailWord_915491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915491).length < 2 ^ (prefixWord ++ tailWord_915491).sum := by decide
  have hdescent : baseEnd_915491 < baseStart_915491 := by decide
  rcases family_descends (prefixWord ++ tailWord_915491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915598 : List Nat := [4, 1, 1, 3, 3, 9]
def baseStart_915598 : Nat := 118140960795 + 915598 * 2 ^ 59
def prefixEnd_915598 : Nat := 4983230072969 + 3 ^ 40 * 915598 * 2
def baseEnd_915598 : Nat := 7738960663298995099823

theorem tailTrace_915598 : CollatzResearch.WordTrace tailWord_915598 prefixEnd_915598 7738960663298995099823 := by
  unfold tailWord_915598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4174325317119036566765431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22263068357968195022748965 4174325317119036566765431)
  ·
    refine ⟨6261487975678554850148147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4174325317119036566765431 6261487975678554850148147)
    ·
      refine ⟨9392231963517832275222221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6261487975678554850148147 9392231963517832275222221)
      ·
        refine ⟨3522086986319187103208333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9392231963517832275222221 3522086986319187103208333)
        ·
          refine ⟨1320782619869695163703125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3522086986319187103208333 1320782619869695163703125)
          ·
            refine ⟨7738960663298995099823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1320782619869695163703125 7738960663298995099823)
            ·
              rfl

theorem cell21_915598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 9].length) (baseStart_915598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915598 prefixEnd_915598 := by exact prefixLift 915598
  have htrace : WordTrace (prefixWord ++ tailWord_915598) baseStart_915598 baseEnd_915598 := by
    simpa [prefixWord, tailWord_915598, baseEnd_915598] using wordTrace_append hprefix tailTrace_915598
  have hstable : (prefixWord ++ tailWord_915598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915598).length < 2 ^ (prefixWord ++ tailWord_915598).sum := by decide
  have hdescent : baseEnd_915598 < baseStart_915598 := by decide
  rcases family_descends (prefixWord ++ tailWord_915598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915604 : List Nat := [2, 4, 2, 3, 1, 1, 1, 4, 3]
def baseStart_915604 : Nat := 118140960795 + 915604 * 2 ^ 59
def prefixEnd_915604 : Nat := 4983230072969 + 3 ^ 40 * 915604 * 2
def baseEnd_915604 : Nat := 208953307190818190595209

theorem tailTrace_915604 : CollatzResearch.WordTrace tailWord_915604 prefixEnd_915604 208953307190818190595209 := by
  unfold tailWord_915604
  simp only [CollatzResearch.WordTrace]
  refine ⟨16697410687465277779420933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22263214249953703705894577 16697410687465277779420933)
  ·
    refine ⟨3130764503899739583641425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16697410687465277779420933 3130764503899739583641425)
    ·
      refine ⟨2348073377924804687731069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3130764503899739583641425 2348073377924804687731069)
      ·
        refine ⟨880527516721801757899151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2348073377924804687731069 880527516721801757899151)
        ·
          refine ⟨1320791275082702636848727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880527516721801757899151 1320791275082702636848727)
          ·
            refine ⟨1981186912624053955273091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320791275082702636848727 1981186912624053955273091)
            ·
              refine ⟨2971780368936080932909637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981186912624053955273091 2971780368936080932909637)
              ·
                refine ⟨557208819175515174920557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2971780368936080932909637 557208819175515174920557)
                ·
                  refine ⟨208953307190818190595209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557208819175515174920557 208953307190818190595209)
                  ·
                    rfl

theorem cell21_915604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_915604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915604 prefixEnd_915604 := by exact prefixLift 915604
  have htrace : WordTrace (prefixWord ++ tailWord_915604) baseStart_915604 baseEnd_915604 := by
    simpa [prefixWord, tailWord_915604, baseEnd_915604] using wordTrace_append hprefix tailTrace_915604
  have hstable : (prefixWord ++ tailWord_915604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915604).length < 2 ^ (prefixWord ++ tailWord_915604).sum := by decide
  have hdescent : baseEnd_915604 < baseStart_915604 := by decide
  rcases family_descends (prefixWord ++ tailWord_915604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915615 : List Nat := [1, 1, 2, 6, 1, 3, 1, 6]
def baseStart_915615 : Nat := 118140960795 + 915615 * 2 ^ 59
def prefixEnd_915615 : Nat := 4983230072969 + 3 ^ 40 * 915615 * 2
def baseEnd_915615 : Nat := 69651939180228205303951

theorem tailTrace_915615 : CollatzResearch.WordTrace tailWord_915615 prefixEnd_915615 69651939180228205303951 := by
  unfold tailWord_915615
  simp only [CollatzResearch.WordTrace]
  refine ⟨33395222577890704437492299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22263481718593802958328199 33395222577890704437492299)
  ·
    refine ⟨50092833866836056656238449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33395222577890704437492299 50092833866836056656238449)
    ·
      refine ⟨37569625400127042492178837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50092833866836056656238449 37569625400127042492178837)
      ·
        refine ⟨1761076190630955116820883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37569625400127042492178837 1761076190630955116820883)
        ·
          refine ⟨2641614285946432675231325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761076190630955116820883 2641614285946432675231325)
          ·
            refine ⟨990605357229912253211747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2641614285946432675231325 990605357229912253211747)
            ·
              refine ⟨1485908035844868379817621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990605357229912253211747 1485908035844868379817621)
              ·
                refine ⟨69651939180228205303951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1485908035844868379817621 69651939180228205303951)
                ·
                  rfl

theorem cell21_915615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 6].length) (baseStart_915615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915615 prefixEnd_915615 := by exact prefixLift 915615
  have htrace : WordTrace (prefixWord ++ tailWord_915615) baseStart_915615 baseEnd_915615 := by
    simpa [prefixWord, tailWord_915615, baseEnd_915615] using wordTrace_append hprefix tailTrace_915615
  have hstable : (prefixWord ++ tailWord_915615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915615).length < 2 ^ (prefixWord ++ tailWord_915615).sum := by decide
  have hdescent : baseEnd_915615 < baseStart_915615 := by decide
  rcases family_descends (prefixWord ++ tailWord_915615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915629 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 7]
def baseStart_915629 : Nat := 118140960795 + 915629 * 2 ^ 59
def prefixEnd_915629 : Nat := 4983230072969 + 3 ^ 40 * 915629 * 2
def baseEnd_915629 : Nat := 208959012531423702678491

theorem tailTrace_915629 : CollatzResearch.WordTrace tailWord_915629 prefixEnd_915629 208959012531423702678491 := by
  unfold tailWord_915629
  simp only [CollatzResearch.WordTrace]
  refine ⟨33395733199839984828501941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22263822133226656552334627 33395733199839984828501941)
  ·
    refine ⟨3130849987484998577672057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33395733199839984828501941 3130849987484998577672057)
    ·
      refine ⟨2348137490613748933254043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3130849987484998577672057 2348137490613748933254043)
      ·
        refine ⟨3522206235920623399881065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2348137490613748933254043 3522206235920623399881065)
        ·
          refine ⟨2641654676940467549910799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3522206235920623399881065 2641654676940467549910799)
          ·
            refine ⟨3962482015410701324866199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2641654676940467549910799 3962482015410701324866199)
            ·
              refine ⟨5943723023116051987299299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3962482015410701324866199 5943723023116051987299299)
              ·
                refine ⟨8915584534674077980948949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5943723023116051987299299 8915584534674077980948949)
                ·
                  refine ⟨208959012531423702678491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8915584534674077980948949 208959012531423702678491)
                  ·
                    rfl

theorem cell21_915629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_915629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915629 prefixEnd_915629 := by exact prefixLift 915629
  have htrace : WordTrace (prefixWord ++ tailWord_915629) baseStart_915629 baseEnd_915629 := by
    simpa [prefixWord, tailWord_915629, baseEnd_915629] using wordTrace_append hprefix tailTrace_915629
  have hstable : (prefixWord ++ tailWord_915629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915629).length < 2 ^ (prefixWord ++ tailWord_915629).sum := by decide
  have hdescent : baseEnd_915629 < baseStart_915629 := by decide
  rcases family_descends (prefixWord ++ tailWord_915629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915705 : List Nat := [1, 2, 1, 3, 1, 1, 2, 7, 3]
def baseStart_915705 : Nat := 118140960795 + 915705 * 2 ^ 59
def prefixEnd_915705 : Nat := 4983230072969 + 3 ^ 40 * 915705 * 2
def baseEnd_915705 : Nat := 208976356766864459411669

theorem tailTrace_915705 : CollatzResearch.WordTrace tailWord_915705 prefixEnd_915705 208976356766864459411669 := by
  unfold tailWord_915705
  simp only [CollatzResearch.WordTrace]
  refine ⟨33398505147564649808268569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22265670098376433205512379 33398505147564649808268569)
  ·
    refine ⟨25048878860673487356201427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33398505147564649808268569 25048878860673487356201427)
    ·
      refine ⟨37573318291010231034302141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25048878860673487356201427 37573318291010231034302141)
      ·
        refine ⟨14089994359128836637863303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37573318291010231034302141 14089994359128836637863303)
        ·
          refine ⟨21134991538693254956794955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14089994359128836637863303 21134991538693254956794955)
          ·
            refine ⟨31702487308039882435192433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21134991538693254956794955 31702487308039882435192433)
            ·
              refine ⟨23776865481029911826394325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31702487308039882435192433 23776865481029911826394325)
              ·
                refine ⟨557270284711638558431117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23776865481029911826394325 557270284711638558431117)
                ·
                  refine ⟨208976356766864459411669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557270284711638558431117 208976356766864459411669)
                  ·
                    rfl

theorem cell21_915705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 3].length) (baseStart_915705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915705 prefixEnd_915705 := by exact prefixLift 915705
  have htrace : WordTrace (prefixWord ++ tailWord_915705) baseStart_915705 baseEnd_915705 := by
    simpa [prefixWord, tailWord_915705, baseEnd_915705] using wordTrace_append hprefix tailTrace_915705
  have hstable : (prefixWord ++ tailWord_915705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915705).length < 2 ^ (prefixWord ++ tailWord_915705).sum := by decide
  have hdescent : baseEnd_915705 < baseStart_915705 := by decide
  rcases family_descends (prefixWord ++ tailWord_915705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915733 : List Nat := [1, 3, 2, 1, 2, 1, 3, 8]
def baseStart_915733 : Nat := 118140960795 + 915733 * 2 ^ 59
def prefixEnd_915733 : Nat := 4983230072969 + 3 ^ 40 * 915733 * 2
def baseEnd_915733 : Nat := 69660915582780877648315

theorem tailTrace_915733 : CollatzResearch.WordTrace tailWord_915733 prefixEnd_915733 69660915582780877648315 := by
  unfold tailWord_915733
  simp only [CollatzResearch.WordTrace]
  refine ⟨33399526391463210590287853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22266350927642140393525235 33399526391463210590287853)
  ·
    refine ⟨12524822396798703971357945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33399526391463210590287853 12524822396798703971357945)
    ·
      refine ⟨9393616797599027978518459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12524822396798703971357945 9393616797599027978518459)
      ·
        refine ⟨14090425196398541967777689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9393616797599027978518459 14090425196398541967777689)
        ·
          refine ⟨10567818897298906475833267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14090425196398541967777689 10567818897298906475833267)
          ·
            refine ⟨15851728345948359713749901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10567818897298906475833267 15851728345948359713749901)
            ·
              refine ⟨5944398129730634892656213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15851728345948359713749901 5944398129730634892656213)
              ·
                refine ⟨69660915582780877648315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5944398129730634892656213 69660915582780877648315)
                ·
                  rfl

theorem cell21_915733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 8].length) (baseStart_915733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915733 prefixEnd_915733 := by exact prefixLift 915733
  have htrace : WordTrace (prefixWord ++ tailWord_915733) baseStart_915733 baseEnd_915733 := by
    simpa [prefixWord, tailWord_915733, baseEnd_915733] using wordTrace_append hprefix tailTrace_915733
  have hstable : (prefixWord ++ tailWord_915733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915733).length < 2 ^ (prefixWord ++ tailWord_915733).sum := by decide
  have hdescent : baseEnd_915733 < baseStart_915733 := by decide
  rcases family_descends (prefixWord ++ tailWord_915733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915829 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 4]
def baseStart_915829 : Nat := 118140960795 + 915829 * 2 ^ 59
def prefixEnd_915829 : Nat := 4983230072969 + 3 ^ 40 * 915829 * 2
def baseEnd_915829 : Nat := 209004655256267799344749

theorem tailTrace_915829 : CollatzResearch.WordTrace tailWord_915829 prefixEnd_915829 209004655256267799344749 := by
  unfold tailWord_915829
  simp only [CollatzResearch.WordTrace]
  refine ⟨33403027799115418985782541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22268685199410279323855027 33403027799115418985782541)
  ·
    refine ⟨12526135424668282119668453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33403027799115418985782541 12526135424668282119668453)
    ·
      refine ⟨2348650392125302897437835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12526135424668282119668453 2348650392125302897437835)
      ·
        refine ⟨3522975588187954346156753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2348650392125302897437835 3522975588187954346156753)
        ·
          refine ⟨2642231691140965759617565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3522975588187954346156753 2642231691140965759617565)
          ·
            refine ⟨990836884177862159856587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2642231691140965759617565 990836884177862159856587)
            ·
              refine ⟨1486255326266793239784881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990836884177862159856587 1486255326266793239784881)
              ·
                refine ⟨1114691494700094929838661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486255326266793239784881 1114691494700094929838661)
                ·
                  refine ⟨209004655256267799344749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114691494700094929838661 209004655256267799344749)
                  ·
                    rfl

theorem cell21_915829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_915829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915829 prefixEnd_915829 := by exact prefixLift 915829
  have htrace : WordTrace (prefixWord ++ tailWord_915829) baseStart_915829 baseEnd_915829 := by
    simpa [prefixWord, tailWord_915829, baseEnd_915829] using wordTrace_append hprefix tailTrace_915829
  have hstable : (prefixWord ++ tailWord_915829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915829).length < 2 ^ (prefixWord ++ tailWord_915829).sum := by decide
  have hdescent : baseEnd_915829 < baseStart_915829 := by decide
  rcases family_descends (prefixWord ++ tailWord_915829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915860 : List Nat := [2, 4, 2, 1, 3, 2, 2, 5]
def baseStart_915860 : Nat := 118140960795 + 915860 * 2 ^ 59
def prefixEnd_915860 : Nat := 4983230072969 + 3 ^ 40 * 915860 * 2
def baseEnd_915860 : Nat := 69670576626206211442673

theorem tailTrace_915860 : CollatzResearch.WordTrace tailWord_915860 prefixEnd_915860 69670576626206211442673 := by
  unfold tailWord_915860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16702079231001555640080517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22269438974668740853440689 16702079231001555640080517)
  ·
    refine ⟨3131639855812791682515097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16702079231001555640080517 3131639855812791682515097)
    ·
      refine ⟨2348729891859593761886323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3131639855812791682515097 2348729891859593761886323)
      ·
        refine ⟨3523094837789390642829485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2348729891859593761886323 3523094837789390642829485)
        ·
          refine ⟨1321160564171021491061057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3523094837789390642829485 1321160564171021491061057)
          ·
            refine ⟨990870423128266118295793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1321160564171021491061057 990870423128266118295793)
            ·
              refine ⟨743152817346199588721845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990870423128266118295793 743152817346199588721845)
              ·
                refine ⟨69670576626206211442673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 743152817346199588721845 69670576626206211442673)
                ·
                  rfl

theorem cell21_915860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_915860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915860 prefixEnd_915860 := by exact prefixLift 915860
  have htrace : WordTrace (prefixWord ++ tailWord_915860) baseStart_915860 baseEnd_915860 := by
    simpa [prefixWord, tailWord_915860, baseEnd_915860] using wordTrace_append hprefix tailTrace_915860
  have hstable : (prefixWord ++ tailWord_915860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915860).length < 2 ^ (prefixWord ++ tailWord_915860).sum := by decide
  have hdescent : baseEnd_915860 < baseStart_915860 := by decide
  rcases family_descends (prefixWord ++ tailWord_915860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915899 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 11]
def baseStart_915899 : Nat := 118140960795 + 915899 * 2 ^ 59
def prefixEnd_915899 : Nat := 4983230072969 + 3 ^ 40 * 915899 * 2
def baseEnd_915899 : Nat := 209020630209963233177939

theorem tailTrace_915899 : CollatzResearch.WordTrace tailWord_915899 prefixEnd_915899 209020630209963233177939 := by
  unfold tailWord_915899
  simp only [CollatzResearch.WordTrace]
  refine ⟨33405580908861820940830751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22270387272574547293887167 33405580908861820940830751)
  ·
    refine ⟨50108371363292731411246127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33405580908861820940830751 50108371363292731411246127)
    ·
      refine ⟨75162557044939097116869191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50108371363292731411246127 75162557044939097116869191)
      ·
        refine ⟨112743835567408645675303787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75162557044939097116869191 112743835567408645675303787)
        ·
          refine ⟨169115753351112968512955681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112743835567408645675303787 169115753351112968512955681)
          ·
            refine ⟨126836815013334726384716761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169115753351112968512955681 126836815013334726384716761)
            ·
              refine ⟨95127611260001044788537571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126836815013334726384716761 95127611260001044788537571)
              ·
                refine ⟨142691416890001567182806357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95127611260001044788537571 142691416890001567182806357)
                ·
                  refine ⟨209020630209963233177939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 142691416890001567182806357 209020630209963233177939)
                  ·
                    rfl

theorem cell21_915899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_915899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915899 prefixEnd_915899 := by exact prefixLift 915899
  have htrace : WordTrace (prefixWord ++ tailWord_915899) baseStart_915899 baseEnd_915899 := by
    simpa [prefixWord, tailWord_915899, baseEnd_915899] using wordTrace_append hprefix tailTrace_915899
  have hstable : (prefixWord ++ tailWord_915899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915899).length < 2 ^ (prefixWord ++ tailWord_915899).sum := by decide
  have hdescent : baseEnd_915899 < baseStart_915899 := by decide
  rcases family_descends (prefixWord ++ tailWord_915899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915947 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 4]
def baseStart_915947 : Nat := 118140960795 + 915947 * 2 ^ 59
def prefixEnd_915947 : Nat := 4983230072969 + 3 ^ 40 * 915947 * 2
def baseEnd_915947 : Nat := 209031584463925816377841

theorem tailTrace_915947 : CollatzResearch.WordTrace tailWord_915947 prefixEnd_915947 209031584463925816377841 := by
  unfold tailWord_915947
  simp only [CollatzResearch.WordTrace]
  refine ⟨33407331612687925138578095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22271554408458616759052063 33407331612687925138578095)
  ·
    refine ⟨50110997419031887707867143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33407331612687925138578095 50110997419031887707867143)
    ·
      refine ⟨75166496128547831561800715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50110997419031887707867143 75166496128547831561800715)
      ·
        refine ⟨112749744192821747342701073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75166496128547831561800715 112749744192821747342701073)
        ·
          refine ⟨84562308144616310507025805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112749744192821747342701073 84562308144616310507025805)
          ·
            refine ⟨31710865554231116440134677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84562308144616310507025805 31710865554231116440134677)
            ·
              refine ⟨1486446822854583583131313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31710865554231116440134677 1486446822854583583131313)
              ·
                refine ⟨1114835117140937687348485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486446822854583583131313 1114835117140937687348485)
                ·
                  refine ⟨209031584463925816377841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114835117140937687348485 209031584463925816377841)
                  ·
                    rfl

theorem cell21_915947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 4].length) (baseStart_915947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915947 prefixEnd_915947 := by exact prefixLift 915947
  have htrace : WordTrace (prefixWord ++ tailWord_915947) baseStart_915947 baseEnd_915947 := by
    simpa [prefixWord, tailWord_915947, baseEnd_915947] using wordTrace_append hprefix tailTrace_915947
  have hstable : (prefixWord ++ tailWord_915947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915947).length < 2 ^ (prefixWord ++ tailWord_915947).sum := by decide
  have hdescent : baseEnd_915947 < baseStart_915947 := by decide
  rcases family_descends (prefixWord ++ tailWord_915947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915950 : List Nat := [4, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_915950 : Nat := 118140960795 + 915950 * 2 ^ 59
def prefixEnd_915950 : Nat := 4983230072969 + 3 ^ 40 * 915950 * 2
def baseEnd_915950 : Nat := 209032269104798477827835

theorem tailTrace_915950 : CollatzResearch.WordTrace tailWord_915950 prefixEnd_915950 209032269104798477827835 := by
  unfold tailWord_915950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4175930128959632081367163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22271627354451371100624869 4175930128959632081367163)
  ·
    refine ⟨6263895193439448122050745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4175930128959632081367163 6263895193439448122050745)
    ·
      refine ⟨4697921395079586091538059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6263895193439448122050745 4697921395079586091538059)
      ·
        refine ⟨7046882092619379137307089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4697921395079586091538059 7046882092619379137307089)
        ·
          refine ⟨5285161569464534352980317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7046882092619379137307089 5285161569464534352980317)
          ·
            refine ⟨1981935588549200382367619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5285161569464534352980317 1981935588549200382367619)
            ·
              refine ⟨2972903382823800573551429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981935588549200382367619 2972903382823800573551429)
              ·
                refine ⟨557419384279462607540893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2972903382823800573551429 557419384279462607540893)
                ·
                  refine ⟨209032269104798477827835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557419384279462607540893 209032269104798477827835)
                  ·
                    rfl

theorem cell21_915950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_915950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915950 prefixEnd_915950 := by exact prefixLift 915950
  have htrace : WordTrace (prefixWord ++ tailWord_915950) baseStart_915950 baseEnd_915950 := by
    simpa [prefixWord, tailWord_915950, baseEnd_915950] using wordTrace_append hprefix tailTrace_915950
  have hstable : (prefixWord ++ tailWord_915950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915950).length < 2 ^ (prefixWord ++ tailWord_915950).sum := by decide
  have hdescent : baseEnd_915950 < baseStart_915950 := by decide
  rcases family_descends (prefixWord ++ tailWord_915950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915961 : List Nat := [1, 2, 1, 3, 1, 2, 5, 6]
def baseStart_915961 : Nat := 118140960795 + 915961 * 2 ^ 59
def prefixEnd_915961 : Nat := 4983230072969 + 3 ^ 40 * 915961 * 2
def baseEnd_915961 : Nat := 69678259818221634381493

theorem tailTrace_915961 : CollatzResearch.WordTrace tailWord_915961 prefixEnd_915961 69678259818221634381493 := by
  unfold tailWord_915961
  simp only [CollatzResearch.WordTrace]
  refine ⟨33407842234637205529587737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22271894823091470353058491 33407842234637205529587737)
  ·
    refine ⟨25055881675977904147190803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33407842234637205529587737 25055881675977904147190803)
    ·
      refine ⟨37583822513966856220786205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25055881675977904147190803 37583822513966856220786205)
      ·
        refine ⟨14093933442737571082794827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37583822513966856220786205 14093933442737571082794827)
        ·
          refine ⟨21140900164106356624192241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14093933442737571082794827 21140900164106356624192241)
          ·
            refine ⟨15855675123079767468144181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21140900164106356624192241 15855675123079767468144181)
            ·
              refine ⟨1486469542788728200138517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15855675123079767468144181 1486469542788728200138517)
              ·
                refine ⟨69678259818221634381493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1486469542788728200138517 69678259818221634381493)
                ·
                  rfl

theorem cell21_915961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 6].length) (baseStart_915961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915961 prefixEnd_915961 := by exact prefixLift 915961
  have htrace : WordTrace (prefixWord ++ tailWord_915961) baseStart_915961 baseEnd_915961 := by
    simpa [prefixWord, tailWord_915961, baseEnd_915961] using wordTrace_append hprefix tailTrace_915961
  have hstable : (prefixWord ++ tailWord_915961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915961).length < 2 ^ (prefixWord ++ tailWord_915961).sum := by decide
  have hdescent : baseEnd_915961 < baseStart_915961 := by decide
  rcases family_descends (prefixWord ++ tailWord_915961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915978 : List Nat := [3, 1, 2, 2, 2, 1, 5, 5]
def baseStart_915978 : Nat := 118140960795 + 915978 * 2 ^ 59
def prefixEnd_915978 : Nat := 4983230072969 + 3 ^ 40 * 915978 * 2
def baseEnd_915978 : Nat := 69679553028758883787037

theorem tailTrace_915978 : CollatzResearch.WordTrace tailWord_915978 prefixEnd_915978 69679553028758883787037 := by
  unfold tailWord_915978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8352115568893904358239147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22272308183717078288637725 8352115568893904358239147)
  ·
    refine ⟨12528173353340856537358721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8352115568893904358239147 12528173353340856537358721)
    ·
      refine ⟨9396130015005642403019041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12528173353340856537358721 9396130015005642403019041)
      ·
        refine ⟨7047097511254231802264281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9396130015005642403019041 7047097511254231802264281)
        ·
          refine ⟨5285323133440673851698211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7047097511254231802264281 5285323133440673851698211)
          ·
            refine ⟨7927984700161010777547317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285323133440673851698211 7927984700161010777547317)
            ·
              refine ⟨743248565640094760395061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7927984700161010777547317 743248565640094760395061)
              ·
                refine ⟨69679553028758883787037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 743248565640094760395061 69679553028758883787037)
                ·
                  rfl

theorem cell21_915978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_915978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_915978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_915978 prefixEnd_915978 := by exact prefixLift 915978
  have htrace : WordTrace (prefixWord ++ tailWord_915978) baseStart_915978 baseEnd_915978 := by
    simpa [prefixWord, tailWord_915978, baseEnd_915978] using wordTrace_append hprefix tailTrace_915978
  have hstable : (prefixWord ++ tailWord_915978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915978).length < 2 ^ (prefixWord ++ tailWord_915978).sum := by decide
  have hdescent : baseEnd_915978 < baseStart_915978 := by decide
  rcases family_descends (prefixWord ++ tailWord_915978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916037 : List Nat := [1, 3, 1, 1, 1, 6, 1, 7]
def baseStart_916037 : Nat := 118140960795 + 916037 * 2 ^ 59
def prefixEnd_916037 : Nat := 4983230072969 + 3 ^ 40 * 916037 * 2
def baseEnd_916037 : Nat := 69684041230035219959219

theorem tailTrace_916037 : CollatzResearch.WordTrace tailWord_916037 prefixEnd_916037 69684041230035219959219 := by
  unfold tailWord_916037
  simp only [CollatzResearch.WordTrace]
  refine ⟨33410614182361870509354365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22273742788241247006236243 33410614182361870509354365)
  ·
    refine ⟨12528980318385701441007887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33410614182361870509354365 12528980318385701441007887)
    ·
      refine ⟨18793470477578552161511831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12528980318385701441007887 18793470477578552161511831)
      ·
        refine ⟨28190205716367828242267747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18793470477578552161511831 28190205716367828242267747)
        ·
          refine ⟨42285308574551742363401621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28190205716367828242267747 42285308574551742363401621)
          ·
            refine ⟨1982123839432112923284451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42285308574551742363401621 1982123839432112923284451)
            ·
              refine ⟨2973185759148169384926677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982123839432112923284451 2973185759148169384926677)
              ·
                refine ⟨69684041230035219959219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2973185759148169384926677 69684041230035219959219)
                ·
                  rfl

theorem cell21_916037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 7].length) (baseStart_916037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916037 prefixEnd_916037 := by exact prefixLift 916037
  have htrace : WordTrace (prefixWord ++ tailWord_916037) baseStart_916037 baseEnd_916037 := by
    simpa [prefixWord, tailWord_916037, baseEnd_916037] using wordTrace_append hprefix tailTrace_916037
  have hstable : (prefixWord ++ tailWord_916037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916037).length < 2 ^ (prefixWord ++ tailWord_916037).sum := by decide
  have hdescent : baseEnd_916037 < baseStart_916037 := by decide
  rcases family_descends (prefixWord ++ tailWord_916037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916116 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 4]
def baseStart_916116 : Nat := 118140960795 + 916116 * 2 ^ 59
def prefixEnd_916116 : Nat := 4983230072969 + 3 ^ 40 * 916116 * 2
def baseEnd_916116 : Nat := 209070152566419078060829

theorem tailTrace_916116 : CollatzResearch.WordTrace tailWord_916116 prefixEnd_916116 209070152566419078060829 := by
  unfold tailWord_916116
  simp only [CollatzResearch.WordTrace]
  refine ⟨16706747774537833500740101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22275663699383778000986801 16706747774537833500740101)
  ·
    refine ⟨3132515207725843781388769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16706747774537833500740101 3132515207725843781388769)
    ·
      refine ⟨2349386405794382836041577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3132515207725843781388769 2349386405794382836041577)
      ·
        refine ⟨1762039804345787127031183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2349386405794382836041577 1762039804345787127031183)
        ·
          refine ⟨2643059706518680690546775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762039804345787127031183 2643059706518680690546775)
          ·
            refine ⟨3964589559778021035820163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643059706518680690546775 3964589559778021035820163)
            ·
              refine ⟨5946884339667031553730245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964589559778021035820163 5946884339667031553730245)
              ·
                refine ⟨1115040813687568416324421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5946884339667031553730245 1115040813687568416324421)
                ·
                  refine ⟨209070152566419078060829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1115040813687568416324421 209070152566419078060829)
                  ·
                    rfl

theorem cell21_916116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_916116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916116 prefixEnd_916116 := by exact prefixLift 916116
  have htrace : WordTrace (prefixWord ++ tailWord_916116) baseStart_916116 baseEnd_916116 := by
    simpa [prefixWord, tailWord_916116, baseEnd_916116] using wordTrace_append hprefix tailTrace_916116
  have hstable : (prefixWord ++ tailWord_916116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916116).length < 2 ^ (prefixWord ++ tailWord_916116).sum := by decide
  have hdescent : baseEnd_916116 < baseStart_916116 := by decide
  rcases family_descends (prefixWord ++ tailWord_916116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916206 : List Nat := [4, 1, 2, 1, 1, 3, 4, 5]
def baseStart_916206 : Nat := 118140960795 + 916206 * 2 ^ 59
def prefixEnd_916206 : Nat := 4983230072969 + 3 ^ 40 * 916206 * 2
def baseEnd_916206 : Nat := 69696897264199640520215

theorem tailTrace_916206 : CollatzResearch.WordTrace tailWord_916206 prefixEnd_916206 69696897264199640520215 := by
  unfold tailWord_916206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4177097264843701546532059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22277852079166408248170981 4177097264843701546532059)
  ·
    refine ⟨6265645897265552319798089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4177097264843701546532059 6265645897265552319798089)
    ·
      refine ⟨4699234422949164239848567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6265645897265552319798089 4699234422949164239848567)
      ·
        refine ⟨7048851634423746359772851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4699234422949164239848567 7048851634423746359772851)
        ·
          refine ⟨10573277451635619539659277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048851634423746359772851 10573277451635619539659277)
          ·
            refine ⟨3964979044363357327372229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10573277451635619539659277 3964979044363357327372229)
            ·
              refine ⟨743433570818129498882293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3964979044363357327372229 743433570818129498882293)
              ·
                refine ⟨69696897264199640520215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 743433570818129498882293 69696897264199640520215)
                ·
                  rfl

theorem cell21_916206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_916206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916206 prefixEnd_916206 := by exact prefixLift 916206
  have htrace : WordTrace (prefixWord ++ tailWord_916206) baseStart_916206 baseEnd_916206 := by
    simpa [prefixWord, tailWord_916206, baseEnd_916206] using wordTrace_append hprefix tailTrace_916206
  have hstable : (prefixWord ++ tailWord_916206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916206).length < 2 ^ (prefixWord ++ tailWord_916206).sum := by decide
  have hdescent : baseEnd_916206 < baseStart_916206 := by decide
  rcases family_descends (prefixWord ++ tailWord_916206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916234 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_916234 : Nat := 118140960795 + 916234 * 2 ^ 59
def prefixEnd_916234 : Nat := 4983230072969 + 3 ^ 40 * 916234 * 2
def baseEnd_916234 : Nat := 209097081774077095093921

theorem tailTrace_916234 : CollatzResearch.WordTrace tailWord_916234 prefixEnd_916234 209097081774077095093921 := by
  unfold tailWord_916234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8354449840662043288568939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22278532908432115436183837 8354449840662043288568939)
  ·
    refine ⟨12531674760993064932853409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8354449840662043288568939 12531674760993064932853409)
    ·
      refine ⟨9398756070744798699640057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12531674760993064932853409 9398756070744798699640057)
      ·
        refine ⟨7049067053058599024730043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9398756070744798699640057 7049067053058599024730043)
        ·
          refine ⟨10573600579587898537095065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7049067053058599024730043 10573600579587898537095065)
          ·
            refine ⟨7930200434690923902821299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10573600579587898537095065 7930200434690923902821299)
            ·
              refine ⟨11895300652036385854231949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7930200434690923902821299 11895300652036385854231949)
              ·
                refine ⟨4460737744513644695336981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11895300652036385854231949 4460737744513644695336981)
                ·
                  refine ⟨209097081774077095093921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4460737744513644695336981 209097081774077095093921)
                  ·
                    rfl

theorem cell21_916234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_916234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916234 prefixEnd_916234 := by exact prefixLift 916234
  have htrace : WordTrace (prefixWord ++ tailWord_916234) baseStart_916234 baseEnd_916234 := by
    simpa [prefixWord, tailWord_916234, baseEnd_916234] using wordTrace_append hprefix tailTrace_916234
  have hstable : (prefixWord ++ tailWord_916234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916234).length < 2 ^ (prefixWord ++ tailWord_916234).sum := by decide
  have hdescent : baseEnd_916234 < baseStart_916234 := by decide
  rcases family_descends (prefixWord ++ tailWord_916234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916341 : List Nat := [1, 3, 4, 1, 1, 3, 8]
def baseStart_916341 : Nat := 118140960795 + 916341 * 2 ^ 59
def prefixEnd_916341 : Nat := 4983230072969 + 3 ^ 40 * 916341 * 2
def baseEnd_916341 : Nat := 23235722292429854090041

theorem tailTrace_916341 : CollatzResearch.WordTrace tailWord_916341 prefixEnd_916341 23235722292429854090041 := by
  unfold tailWord_916341
  simp only [CollatzResearch.WordTrace]
  refine ⟨33421701973260530428420877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22281134648840353618947251 33421701973260530428420877)
  ·
    refine ⟨12533138239972698910657829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33421701973260530428420877 12533138239972698910657829)
    ·
      refine ⟨2349963419994881045748343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12533138239972698910657829 2349963419994881045748343)
      ·
        refine ⟨3524945129992321568622515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2349963419994881045748343 3524945129992321568622515)
        ·
          refine ⟨5287417694988482352933773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3524945129992321568622515 5287417694988482352933773)
          ·
            refine ⟨1982781635620680882350165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5287417694988482352933773 1982781635620680882350165)
            ·
              refine ⟨23235722292429854090041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1982781635620680882350165 23235722292429854090041)
              ·
                rfl

theorem cell21_916341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 8].length) (baseStart_916341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916341 prefixEnd_916341 := by exact prefixLift 916341
  have htrace : WordTrace (prefixWord ++ tailWord_916341) baseStart_916341 baseEnd_916341 := by
    simpa [prefixWord, tailWord_916341, baseEnd_916341] using wordTrace_append hprefix tailTrace_916341
  have hstable : (prefixWord ++ tailWord_916341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916341).length < 2 ^ (prefixWord ++ tailWord_916341).sum := by decide
  have hdescent : baseEnd_916341 < baseStart_916341 := by decide
  rcases family_descends (prefixWord ++ tailWord_916341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916372 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_916372 : Nat := 118140960795 + 916372 * 2 ^ 59
def prefixEnd_916372 : Nat := 4983230072969 + 3 ^ 40 * 916372 * 2
def baseEnd_916372 : Nat := 209128575254219521793639

theorem tailTrace_916372 : CollatzResearch.WordTrace tailWord_916372 prefixEnd_916372 209128575254219521793639 := by
  unfold tailWord_916372
  simp only [CollatzResearch.WordTrace]
  refine ⟨16711416318074111361399685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22281888424098815148532913 16711416318074111361399685)
  ·
    refine ⟨3133390559638895880262441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16711416318074111361399685 3133390559638895880262441)
    ·
      refine ⟨2350042919729171910196831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3133390559638895880262441 2350042919729171910196831)
      ·
        refine ⟨3525064379593757865295247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2350042919729171910196831 3525064379593757865295247)
        ·
          refine ⟨5287596569390636797942871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3525064379593757865295247 5287596569390636797942871)
          ·
            refine ⟨7931394854085955196914307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287596569390636797942871 7931394854085955196914307)
            ·
              refine ⟨11897092281128932795371461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7931394854085955196914307 11897092281128932795371461)
              ·
                refine ⟨2230704802711674899132149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11897092281128932795371461 2230704802711674899132149)
                ·
                  refine ⟨209128575254219521793639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2230704802711674899132149 209128575254219521793639)
                  ·
                    rfl

theorem cell21_916372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_916372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916372 prefixEnd_916372 := by exact prefixLift 916372
  have htrace : WordTrace (prefixWord ++ tailWord_916372) baseStart_916372 baseEnd_916372 := by
    simpa [prefixWord, tailWord_916372, baseEnd_916372] using wordTrace_append hprefix tailTrace_916372
  have hstable : (prefixWord ++ tailWord_916372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916372).length < 2 ^ (prefixWord ++ tailWord_916372).sum := by decide
  have hdescent : baseEnd_916372 < baseStart_916372 := by decide
  rcases family_descends (prefixWord ++ tailWord_916372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916465 : List Nat := [1, 2, 2, 2, 4, 2, 1, 4, 3]
def baseStart_916465 : Nat := 118140960795 + 916465 * 2 ^ 59
def prefixEnd_916465 : Nat := 4983230072969 + 3 ^ 40 * 916465 * 2
def baseEnd_916465 : Nat := 209149799121272026743449

theorem tailTrace_916465 : CollatzResearch.WordTrace tailWord_916465 prefixEnd_916465 209149799121272026743449 := by
  unfold tailWord_916465
  simp only [CollatzResearch.WordTrace]
  refine ⟨33426224624811299605934849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22284149749874199737289899 33426224624811299605934849)
  ·
    refine ⟨25069668468608474704451137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33426224624811299605934849 25069668468608474704451137)
    ·
      refine ⟨18802251351456356028338353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25069668468608474704451137 18802251351456356028338353)
      ·
        refine ⟨14101688513592267021253765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18802251351456356028338353 14101688513592267021253765)
        ·
          refine ⟨2644066596298550066485081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14101688513592267021253765 2644066596298550066485081)
          ·
            refine ⟨1983049947223912549863811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2644066596298550066485081 1983049947223912549863811)
            ·
              refine ⟨2974574920835868824795717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983049947223912549863811 2974574920835868824795717)
              ·
                refine ⟨557732797656725404649197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2974574920835868824795717 557732797656725404649197)
                ·
                  refine ⟨209149799121272026743449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557732797656725404649197 209149799121272026743449)
                  ·
                    rfl

theorem cell21_916465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 3].length) (baseStart_916465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916465 prefixEnd_916465 := by exact prefixLift 916465
  have htrace : WordTrace (prefixWord ++ tailWord_916465) baseStart_916465 baseEnd_916465 := by
    simpa [prefixWord, tailWord_916465, baseEnd_916465] using wordTrace_append hprefix tailTrace_916465
  have hstable : (prefixWord ++ tailWord_916465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916465).length < 2 ^ (prefixWord ++ tailWord_916465).sum := by decide
  have hdescent : baseEnd_916465 < baseStart_916465 := by decide
  rcases family_descends (prefixWord ++ tailWord_916465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916482 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_916482 : Nat := 118140960795 + 916482 * 2 ^ 59
def prefixEnd_916482 : Nat := 4983230072969 + 3 ^ 40 * 916482 * 2
def baseEnd_916482 : Nat := 209153678752883774960081

theorem tailTrace_916482 : CollatzResearch.WordTrace tailWord_916482 prefixEnd_916482 209153678752883774960081 := by
  unfold tailWord_916482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8356711166437427877325925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22284563110499807672869133 8356711166437427877325925)
  ·
    refine ⟨1566883343707017726998611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8356711166437427877325925 1566883343707017726998611)
    ·
      refine ⟨2350325015560526590497917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1566883343707017726998611 2350325015560526590497917)
      ·
        refine ⟨881371880835197471436719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2350325015560526590497917 881371880835197471436719)
        ·
          refine ⟨1322057821252796207155079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881371880835197471436719 1322057821252796207155079)
          ·
            refine ⟨1983086731879194310732619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322057821252796207155079 1983086731879194310732619)
            ·
              refine ⟨2974630097818791466098929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983086731879194310732619 2974630097818791466098929)
              ·
                refine ⟨2230972573364093599574197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2974630097818791466098929 2230972573364093599574197)
                ·
                  refine ⟨209153678752883774960081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2230972573364093599574197 209153678752883774960081)
                  ·
                    rfl

theorem cell21_916482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_916482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916482 prefixEnd_916482 := by exact prefixLift 916482
  have htrace : WordTrace (prefixWord ++ tailWord_916482) baseStart_916482 baseEnd_916482 := by
    simpa [prefixWord, tailWord_916482, baseEnd_916482] using wordTrace_append hprefix tailTrace_916482
  have hstable : (prefixWord ++ tailWord_916482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916482).length < 2 ^ (prefixWord ++ tailWord_916482).sum := by decide
  have hdescent : baseEnd_916482 < baseStart_916482 := by decide
  rcases family_descends (prefixWord ++ tailWord_916482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916524 : List Nat := [2, 2, 1, 1, 1, 2, 3, 6, 3]
def baseStart_916524 : Nat := 118140960795 + 916524 * 2 ^ 59
def prefixEnd_916524 : Nat := 4983230072969 + 3 ^ 40 * 916524 * 2
def baseEnd_916524 : Nat := 209163263725101035259995

theorem tailTrace_916524 : CollatzResearch.WordTrace tailWord_916524 prefixEnd_916524 209163263725101035259995 := by
  unfold tailWord_916524
  simp only [CollatzResearch.WordTrace]
  refine ⟨16714188265798776341166313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22285584354398368454888417 16714188265798776341166313)
  ·
    refine ⟨12535641199349082255874735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16714188265798776341166313 12535641199349082255874735)
    ·
      refine ⟨18803461799023623383812103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12535641199349082255874735 18803461799023623383812103)
      ·
        refine ⟨28205192698535435075718155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18803461799023623383812103 28205192698535435075718155)
        ·
          refine ⟨42307789047803152613577233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28205192698535435075718155 42307789047803152613577233)
          ·
            refine ⟨31730841785852364460182925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42307789047803152613577233 31730841785852364460182925)
            ·
              refine ⟨11899065669694636672568597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31730841785852364460182925 11899065669694636672568597)
              ·
                refine ⟨557768703266936094026653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11899065669694636672568597 557768703266936094026653)
                ·
                  refine ⟨209163263725101035259995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557768703266936094026653 209163263725101035259995)
                  ·
                    rfl

theorem cell21_916524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_916524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916524 prefixEnd_916524 := by exact prefixLift 916524
  have htrace : WordTrace (prefixWord ++ tailWord_916524) baseStart_916524 baseEnd_916524 := by
    simpa [prefixWord, tailWord_916524, baseEnd_916524] using wordTrace_append hprefix tailTrace_916524
  have hstable : (prefixWord ++ tailWord_916524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916524).length < 2 ^ (prefixWord ++ tailWord_916524).sum := by decide
  have hdescent : baseEnd_916524 < baseStart_916524 := by decide
  rcases family_descends (prefixWord ++ tailWord_916524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916538 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_916538 : Nat := 118140960795 + 916538 * 2 ^ 59
def prefixEnd_916538 : Nat := 4983230072969 + 3 ^ 40 * 916538 * 2
def baseEnd_916538 : Nat := 209166458715840122026633

theorem tailTrace_916538 : CollatzResearch.WordTrace tailWord_916538 prefixEnd_916538 209166458715840122026633 := by
  unfold tailWord_916538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8357221788386708268335567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22285924769031222048894845 8357221788386708268335567)
  ·
    refine ⟨12535832682580062402503351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8357221788386708268335567 12535832682580062402503351)
    ·
      refine ⟨18803749023870093603755027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12535832682580062402503351 18803749023870093603755027)
      ·
        refine ⟨28205623535805140405632541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18803749023870093603755027 28205623535805140405632541)
        ·
          refine ⟨10577108825926927652112203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28205623535805140405632541 10577108825926927652112203)
          ·
            refine ⟨15865663238890391478168305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10577108825926927652112203 15865663238890391478168305)
            ·
              refine ⟨11899247429167793608626229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15865663238890391478168305 11899247429167793608626229)
              ·
                refine ⟨1115554446484480650808709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11899247429167793608626229 1115554446484480650808709)
                ·
                  refine ⟨209166458715840122026633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1115554446484480650808709 209166458715840122026633)
                  ·
                    rfl

theorem cell21_916538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_916538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916538 prefixEnd_916538 := by exact prefixLift 916538
  have htrace : WordTrace (prefixWord ++ tailWord_916538) baseStart_916538 baseEnd_916538 := by
    simpa [prefixWord, tailWord_916538, baseEnd_916538] using wordTrace_append hprefix tailTrace_916538
  have hstable : (prefixWord ++ tailWord_916538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916538).length < 2 ^ (prefixWord ++ tailWord_916538).sum := by decide
  have hdescent : baseEnd_916538 < baseStart_916538 := by decide
  rcases family_descends (prefixWord ++ tailWord_916538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916552 : List Nat := [2, 1, 3, 1, 1, 1, 5, 7]
def baseStart_916552 : Nat := 118140960795 + 916552 * 2 ^ 59
def prefixEnd_916552 : Nat := 4983230072969 + 3 ^ 40 * 916552 * 2
def baseEnd_916552 : Nat := 69723217902193069597757

theorem tailTrace_916552 : CollatzResearch.WordTrace tailWord_916552 prefixEnd_916552 69723217902193069597757 := by
  unfold tailWord_916552
  simp only [CollatzResearch.WordTrace]
  refine ⟨16714698887748056732175955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22286265183664075642901273 16714698887748056732175955)
  ·
    refine ⟨25072048331622085098263933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16714698887748056732175955 25072048331622085098263933)
    ·
      refine ⟨9402018124358281911848975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25072048331622085098263933 9402018124358281911848975)
      ·
        refine ⟨14103027186537422867773463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9402018124358281911848975 14103027186537422867773463)
        ·
          refine ⟨21154540779806134301660195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14103027186537422867773463 21154540779806134301660195)
          ·
            refine ⟨31731811169709201452490293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21154540779806134301660195 31731811169709201452490293)
            ·
              refine ⟨2974857297160237636170965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31731811169709201452490293 2974857297160237636170965)
              ·
                refine ⟨69723217902193069597757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2974857297160237636170965 69723217902193069597757)
                ·
                  rfl

theorem cell21_916552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_916552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916552 prefixEnd_916552 := by exact prefixLift 916552
  have htrace : WordTrace (prefixWord ++ tailWord_916552) baseStart_916552 baseEnd_916552 := by
    simpa [prefixWord, tailWord_916552, baseEnd_916552] using wordTrace_append hprefix tailTrace_916552
  have hstable : (prefixWord ++ tailWord_916552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916552).length < 2 ^ (prefixWord ++ tailWord_916552).sum := by decide
  have hdescent : baseEnd_916552 < baseStart_916552 := by decide
  rcases family_descends (prefixWord ++ tailWord_916552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916628 : List Nat := [2, 4, 2, 13]
def baseStart_916628 : Nat := 118140960795 + 916628 * 2 ^ 59
def prefixEnd_916628 : Nat := 4983230072969 + 3 ^ 40 * 916628 * 2
def baseEnd_916628 : Nat := 860851843382798212043

theorem tailTrace_916628 : CollatzResearch.WordTrace tailWord_916628 prefixEnd_916628 860851843382798212043 := by
  unfold tailWord_916628
  simp only [CollatzResearch.WordTrace]
  refine ⟨16716084861610389222059269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22288113148813852296079025 16716084861610389222059269)
  ·
    refine ⟨3134265911551947979136113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16716084861610389222059269 3134265911551947979136113)
    ·
      refine ⟨2350699433663960984352085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3134265911551947979136113 2350699433663960984352085)
      ·
        refine ⟨860851843382798212043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2350699433663960984352085 860851843382798212043)
        ·
          rfl

theorem cell21_916628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 13].length) (baseStart_916628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916628 prefixEnd_916628 := by exact prefixLift 916628
  have htrace : WordTrace (prefixWord ++ tailWord_916628) baseStart_916628 baseEnd_916628 := by
    simpa [prefixWord, tailWord_916628, baseEnd_916628] using wordTrace_append hprefix tailTrace_916628
  have hstable : (prefixWord ++ tailWord_916628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916628).length < 2 ^ (prefixWord ++ tailWord_916628).sum := by decide
  have hdescent : baseEnd_916628 < baseStart_916628 := by decide
  rcases family_descends (prefixWord ++ tailWord_916628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916631 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 4]
def baseStart_916631 : Nat := 118140960795 + 916631 * 2 ^ 59
def prefixEnd_916631 : Nat := 4983230072969 + 3 ^ 40 * 916631 * 2
def baseEnd_916631 : Nat := 209187682582892626976443

theorem tailTrace_916631 : CollatzResearch.WordTrace tailWord_916631 prefixEnd_916631 209187682582892626976443 := by
  unfold tailWord_916631
  simp only [CollatzResearch.WordTrace]
  refine ⟨33432279142209909956477747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22288186094806606637651831 33432279142209909956477747)
  ·
    refine ⟨50148418713314864934716621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33432279142209909956477747 50148418713314864934716621)
    ·
      refine ⟨18805657017493074350518733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50148418713314864934716621 18805657017493074350518733)
      ·
        refine ⟨7052121381559902881444525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18805657017493074350518733 7052121381559902881444525)
        ·
          refine ⟨2644545518084963580541697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7052121381559902881444525 2644545518084963580541697)
          ·
            refine ⟨1983409138563722685406273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2644545518084963580541697 1983409138563722685406273)
            ·
              refine ⟨1487556853922792014054705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1983409138563722685406273 1487556853922792014054705)
              ·
                refine ⟨1115667640442094010541029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487556853922792014054705 1115667640442094010541029)
                ·
                  refine ⟨209187682582892626976443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1115667640442094010541029 209187682582892626976443)
                  ·
                    rfl

theorem cell21_916631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 4].length) (baseStart_916631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916631 prefixEnd_916631 := by exact prefixLift 916631
  have htrace : WordTrace (prefixWord ++ tailWord_916631) baseStart_916631 baseEnd_916631 := by
    simpa [prefixWord, tailWord_916631, baseEnd_916631] using wordTrace_append hprefix tailTrace_916631
  have hstable : (prefixWord ++ tailWord_916631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916631).length < 2 ^ (prefixWord ++ tailWord_916631).sum := by decide
  have hdescent : baseEnd_916631 < baseStart_916631 := by decide
  rcases family_descends (prefixWord ++ tailWord_916631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916634 : List Nat := [3, 1, 1, 5, 1, 1, 4, 2, 3]
def baseStart_916634 : Nat := 118140960795 + 916634 * 2 ^ 59
def prefixEnd_916634 : Nat := 4983230072969 + 3 ^ 40 * 916634 * 2
def baseEnd_916634 : Nat := 209188367223765288426437

theorem tailTrace_916634 : CollatzResearch.WordTrace tailWord_916634 prefixEnd_916634 209188367223765288426437 := by
  unfold tailWord_916634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8358097140299760367209239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22288259040799360979224637 8358097140299760367209239)
  ·
    refine ⟨12537145710449640550813859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8358097140299760367209239 12537145710449640550813859)
    ·
      refine ⟨18805718565674460826220789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12537145710449640550813859 18805718565674460826220789)
      ·
        refine ⟨1763036115531980702458199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18805718565674460826220789 1763036115531980702458199)
        ·
          refine ⟨2644554173297971053687299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763036115531980702458199 2644554173297971053687299)
          ·
            refine ⟨3966831259946956580530949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644554173297971053687299 3966831259946956580530949)
            ·
              refine ⟨743780861240054358849553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3966831259946956580530949 743780861240054358849553)
              ·
                refine ⟨557835645930040769137165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 743780861240054358849553 557835645930040769137165)
                ·
                  refine ⟨209188367223765288426437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557835645930040769137165 209188367223765288426437)
                  ·
                    rfl

theorem cell21_916634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_916634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916634 prefixEnd_916634 := by exact prefixLift 916634
  have htrace : WordTrace (prefixWord ++ tailWord_916634) baseStart_916634 baseEnd_916634 := by
    simpa [prefixWord, tailWord_916634, baseEnd_916634] using wordTrace_append hprefix tailTrace_916634
  have hstable : (prefixWord ++ tailWord_916634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916634).length < 2 ^ (prefixWord ++ tailWord_916634).sum := by decide
  have hdescent : baseEnd_916634 < baseStart_916634 := by decide
  rcases family_descends (prefixWord ++ tailWord_916634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916645 : List Nat := [1, 3, 1, 2, 1, 6, 1, 6]
def baseStart_916645 : Nat := 118140960795 + 916645 * 2 ^ 59
def prefixEnd_916645 : Nat := 4983230072969 + 3 ^ 40 * 916645 * 2
def baseEnd_916645 : Nat := 69730292524543904581027

theorem tailTrace_916645 : CollatzResearch.WordTrace tailWord_916645 prefixEnd_916645 69730292524543904581027 := by
  unfold tailWord_916645
  simp only [CollatzResearch.WordTrace]
  refine ⟨33432789764159190347487389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22288526509439460231658259 33432789764159190347487389)
  ·
    refine ⟨12537296161559696380307771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33432789764159190347487389 12537296161559696380307771)
    ·
      refine ⟨18805944242339544570461657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12537296161559696380307771 18805944242339544570461657)
      ·
        refine ⟨14104458181754658427846243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18805944242339544570461657 14104458181754658427846243)
        ·
          refine ⟨21156687272631987641769365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14104458181754658427846243 21156687272631987641769365)
          ·
            refine ⟨991719715904624420707939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21156687272631987641769365 991719715904624420707939)
            ·
              refine ⟨1487579573856936631061909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991719715904624420707939 1487579573856936631061909)
              ·
                refine ⟨69730292524543904581027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1487579573856936631061909 69730292524543904581027)
                ·
                  rfl

theorem cell21_916645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 6].length) (baseStart_916645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916645 prefixEnd_916645 := by exact prefixLift 916645
  have htrace : WordTrace (prefixWord ++ tailWord_916645) baseStart_916645 baseEnd_916645 := by
    simpa [prefixWord, tailWord_916645, baseEnd_916645] using wordTrace_append hprefix tailTrace_916645
  have hstable : (prefixWord ++ tailWord_916645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916645).length < 2 ^ (prefixWord ++ tailWord_916645).sum := by decide
  have hdescent : baseEnd_916645 < baseStart_916645 := by decide
  rcases family_descends (prefixWord ++ tailWord_916645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916690 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_916690 : Nat := 118140960795 + 916690 * 2 ^ 59
def prefixEnd_916690 : Nat := 4983230072969 + 3 ^ 40 * 916690 * 2
def baseEnd_916690 : Nat := 209201147186721635492989

theorem tailTrace_916690 : CollatzResearch.WordTrace tailWord_916690 prefixEnd_916690 209201147186721635492989 := by
  unfold tailWord_916690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8358607762249040758218881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22289620699330775355250349 8358607762249040758218881)
  ·
    refine ⟨6268955821686780568664161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8358607762249040758218881 6268955821686780568664161)
    ·
      refine ⟨4701716866265085426498121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6268955821686780568664161 4701716866265085426498121)
      ·
        refine ⟨3526287649698814069873591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4701716866265085426498121 3526287649698814069873591)
        ·
          refine ⟨5289431474548221104810387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526287649698814069873591 5289431474548221104810387)
          ·
            refine ⟨7934147211822331657215581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5289431474548221104810387 7934147211822331657215581)
            ·
              refine ⟨2975305204433374371455843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7934147211822331657215581 2975305204433374371455843)
              ·
                refine ⟨4462957806650061557183765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975305204433374371455843 4462957806650061557183765)
                ·
                  refine ⟨209201147186721635492989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4462957806650061557183765 209201147186721635492989)
                  ·
                    rfl

theorem cell21_916690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_916690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916690 prefixEnd_916690 := by exact prefixLift 916690
  have htrace : WordTrace (prefixWord ++ tailWord_916690) baseStart_916690 baseEnd_916690 := by
    simpa [prefixWord, tailWord_916690, baseEnd_916690] using wordTrace_append hprefix tailTrace_916690
  have hstable : (prefixWord ++ tailWord_916690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916690).length < 2 ^ (prefixWord ++ tailWord_916690).sum := by decide
  have hdescent : baseEnd_916690 < baseStart_916690 := by decide
  rcases family_descends (prefixWord ++ tailWord_916690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916693 : List Nat := [1, 3, 2, 4, 1, 1, 2, 4, 3]
def baseStart_916693 : Nat := 118140960795 + 916693 * 2 ^ 59
def prefixEnd_916693 : Nat := 4983230072969 + 3 ^ 40 * 916693 * 2
def baseEnd_916693 : Nat := 209201831827594296942983

theorem tailTrace_916693 : CollatzResearch.WordTrace tailWord_916693 prefixEnd_916693 209201831827594296942983 := by
  unfold tailWord_916693
  simp only [CollatzResearch.WordTrace]
  refine ⟨33434540467985294545234733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22289693645323529696823155 33434540467985294545234733)
  ·
    refine ⟨12537952675494485454463025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33434540467985294545234733 12537952675494485454463025)
    ·
      refine ⟨9403464506620864090847269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12537952675494485454463025 9403464506620864090847269)
      ·
        refine ⟨1763149594991412017033863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9403464506620864090847269 1763149594991412017033863)
        ·
          refine ⟨2644724392487118025550795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763149594991412017033863 2644724392487118025550795)
          ·
            refine ⟨3967086588730677038326193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644724392487118025550795 3967086588730677038326193)
            ·
              refine ⟨2975314941548007778744645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3967086588730677038326193 2975314941548007778744645)
              ·
                refine ⟨557871551540251458514621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2975314941548007778744645 557871551540251458514621)
                ·
                  refine ⟨209201831827594296942983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557871551540251458514621 209201831827594296942983)
                  ·
                    rfl

theorem cell21_916693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_916693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916693 prefixEnd_916693 := by exact prefixLift 916693
  have htrace : WordTrace (prefixWord ++ tailWord_916693) baseStart_916693 baseEnd_916693 := by
    simpa [prefixWord, tailWord_916693, baseEnd_916693] using wordTrace_append hprefix tailTrace_916693
  have hstable : (prefixWord ++ tailWord_916693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916693).length < 2 ^ (prefixWord ++ tailWord_916693).sum := by decide
  have hdescent : baseEnd_916693 < baseStart_916693 := by decide
  rcases family_descends (prefixWord ++ tailWord_916693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916738 : List Nat := [3, 4, 1, 1, 3, 2, 7]
def baseStart_916738 : Nat := 118140960795 + 916738 * 2 ^ 59
def prefixEnd_916738 : Nat := 4983230072969 + 3 ^ 40 * 916738 * 2
def baseEnd_916738 : Nat := 23245789048964913188099

theorem tailTrace_916738 : CollatzResearch.WordTrace tailWord_916738 prefixEnd_916738 23245789048964913188099 := by
  unfold tailWord_916738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8359045438205566807655717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22290787835214844820415245 8359045438205566807655717)
  ·
    refine ⟨1567321019663543776435447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8359045438205566807655717 1567321019663543776435447)
    ·
      refine ⟨2350981529495315664653171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1567321019663543776435447 2350981529495315664653171)
      ·
        refine ⟨3526472294242973496979757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2350981529495315664653171 3526472294242973496979757)
        ·
          refine ⟨1322427110341115061367409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3526472294242973496979757 1322427110341115061367409)
          ·
            refine ⟨991820332755836296025557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1322427110341115061367409 991820332755836296025557)
            ·
              refine ⟨23245789048964913188099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 991820332755836296025557 23245789048964913188099)
              ·
                rfl

theorem cell21_916738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 7].length) (baseStart_916738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916738 prefixEnd_916738 := by exact prefixLift 916738
  have htrace : WordTrace (prefixWord ++ tailWord_916738) baseStart_916738 baseEnd_916738 := by
    simpa [prefixWord, tailWord_916738, baseEnd_916738] using wordTrace_append hprefix tailTrace_916738
  have hstable : (prefixWord ++ tailWord_916738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916738).length < 2 ^ (prefixWord ++ tailWord_916738).sum := by decide
  have hdescent : baseEnd_916738 < baseStart_916738 := by decide
  rcases family_descends (prefixWord ++ tailWord_916738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916797 : List Nat := [1, 4, 1, 5, 1, 9]
def baseStart_916797 : Nat := 118140960795 + 916797 * 2 ^ 59
def prefixEnd_916797 : Nat := 4983230072969 + 3 ^ 40 * 916797 * 2
def baseEnd_916797 : Nat := 7749095038685675081831

theorem tailTrace_916797 : CollatzResearch.WordTrace tailWord_916797 prefixEnd_916797 7749095038685675081831 := by
  unfold tailWord_916797
  simp only [CollatzResearch.WordTrace]
  refine ⟨33438333659608520307020645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22292222439739013538013763 33438333659608520307020645)
  ·
    refine ⟨6269687561176597557566371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33438333659608520307020645 6269687561176597557566371)
    ·
      refine ⟨9404531341764896336349557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6269687561176597557566371 9404531341764896336349557)
      ·
        refine ⟨881674813290459031532771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9404531341764896336349557 881674813290459031532771)
        ·
          refine ⟨1322512219935688547299157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881674813290459031532771 1322512219935688547299157)
          ·
            refine ⟨7749095038685675081831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1322512219935688547299157 7749095038685675081831)
            ·
              rfl

theorem cell21_916797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 9].length) (baseStart_916797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916797 prefixEnd_916797 := by exact prefixLift 916797
  have htrace : WordTrace (prefixWord ++ tailWord_916797) baseStart_916797 baseEnd_916797 := by
    simpa [prefixWord, tailWord_916797, baseEnd_916797] using wordTrace_append hprefix tailTrace_916797
  have hstable : (prefixWord ++ tailWord_916797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916797).length < 2 ^ (prefixWord ++ tailWord_916797).sum := by decide
  have hdescent : baseEnd_916797 < baseStart_916797 := by decide
  rcases family_descends (prefixWord ++ tailWord_916797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916845 : List Nat := [1, 5, 1, 1, 1, 4, 2, 3, 3]
def baseStart_916845 : Nat := 118140960795 + 916845 * 2 ^ 59
def prefixEnd_916845 : Nat := 4983230072969 + 3 ^ 40 * 916845 * 2
def baseEnd_916845 : Nat := 209236520298475810409339

theorem tailTrace_916845 : CollatzResearch.WordTrace tailWord_916845 prefixEnd_916845 209236520298475810409339 := by
  unfold tailWord_916845
  simp only [CollatzResearch.WordTrace]
  refine ⟨33440084363434624504767989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22293389575623083003178659 33440084363434624504767989)
  ·
    refine ⟨3135007909071996047321999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33440084363434624504767989 3135007909071996047321999)
    ·
      refine ⟨4702511863607994070982999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3135007909071996047321999 4702511863607994070982999)
      ·
        refine ⟨7053767795411991106474499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4702511863607994070982999 7053767795411991106474499)
        ·
          refine ⟨10580651693117986659711749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7053767795411991106474499 10580651693117986659711749)
          ·
            refine ⟨1983872192459622498695953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10580651693117986659711749 1983872192459622498695953)
            ·
              refine ⟨1487904144344716874021965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1983872192459622498695953 1487904144344716874021965)
              ·
                refine ⟨557964054129268827758237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1487904144344716874021965 557964054129268827758237)
                ·
                  refine ⟨209236520298475810409339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557964054129268827758237 209236520298475810409339)
                  ·
                    rfl

theorem cell21_916845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_916845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916845 prefixEnd_916845 := by exact prefixLift 916845
  have htrace : WordTrace (prefixWord ++ tailWord_916845) baseStart_916845 baseEnd_916845 := by
    simpa [prefixWord, tailWord_916845, baseEnd_916845] using wordTrace_append hprefix tailTrace_916845
  have hstable : (prefixWord ++ tailWord_916845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916845).length < 2 ^ (prefixWord ++ tailWord_916845).sum := by decide
  have hdescent : baseEnd_916845 < baseStart_916845 := by decide
  rcases family_descends (prefixWord ++ tailWord_916845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916862 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_916862 : Nat := 118140960795 + 916862 * 2 ^ 59
def prefixEnd_916862 : Nat := 4983230072969 + 3 ^ 40 * 916862 * 2
def baseEnd_916862 : Nat := 209240399930087558625971

theorem tailTrace_916862 : CollatzResearch.WordTrace tailWord_916862 prefixEnd_916862 209240399930087558625971 := by
  unfold tailWord_916862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4180088050546629551017105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22293802936248690938757893 4180088050546629551017105)
  ·
    refine ⟨3135066037909972163262829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4180088050546629551017105 3135066037909972163262829)
    ·
      refine ⟨1175649764216239561223561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3135066037909972163262829 1175649764216239561223561)
      ·
        refine ⟨881737323162179670917671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1175649764216239561223561 881737323162179670917671)
        ·
          refine ⟨1322605984743269506376507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881737323162179670917671 1322605984743269506376507)
          ·
            refine ⟨1983908977114904259564761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322605984743269506376507 1983908977114904259564761)
            ·
              refine ⟨1487931732836178194673571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1983908977114904259564761 1487931732836178194673571)
              ·
                refine ⟨2231897599254267292010357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487931732836178194673571 2231897599254267292010357)
                ·
                  refine ⟨209240399930087558625971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2231897599254267292010357 209240399930087558625971)
                  ·
                    rfl

theorem cell21_916862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_916862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916862 prefixEnd_916862 := by exact prefixLift 916862
  have htrace : WordTrace (prefixWord ++ tailWord_916862) baseStart_916862 baseEnd_916862 := by
    simpa [prefixWord, tailWord_916862, baseEnd_916862] using wordTrace_append hprefix tailTrace_916862
  have hstable : (prefixWord ++ tailWord_916862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916862).length < 2 ^ (prefixWord ++ tailWord_916862).sum := by decide
  have hdescent : baseEnd_916862 < baseStart_916862 := by decide
  rcases family_descends (prefixWord ++ tailWord_916862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916921 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 5]
def baseStart_916921 : Nat := 118140960795 + 916921 * 2 ^ 59
def prefixEnd_916921 : Nat := 4983230072969 + 3 ^ 40 * 916921 * 2
def baseEnd_916921 : Nat := 209253864533916567142517

theorem tailTrace_916921 : CollatzResearch.WordTrace tailWord_916921 prefixEnd_916921 209253864533916567142517 := by
  unfold tailWord_916921
  simp only [CollatzResearch.WordTrace]
  refine ⟨33442856311159289484534617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22295237540772859656356411 33442856311159289484534617)
  ·
    refine ⟨25082142233369467113400963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33442856311159289484534617 25082142233369467113400963)
    ·
      refine ⟨37623213350054200670101445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25082142233369467113400963 37623213350054200670101445)
      ·
        refine ⟨7054352503135162625644021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37623213350054200670101445 7054352503135162625644021)
        ·
          refine ⟨661345547168921496154127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7054352503135162625644021 661345547168921496154127)
          ·
            refine ⟨992018320753382244231191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661345547168921496154127 992018320753382244231191)
            ·
              refine ⟨1488027481130073366346787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992018320753382244231191 1488027481130073366346787)
              ·
                refine ⟨2232041221695110049520181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488027481130073366346787 2232041221695110049520181)
                ·
                  refine ⟨209253864533916567142517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2232041221695110049520181 209253864533916567142517)
                  ·
                    rfl

theorem cell21_916921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 5].length) (baseStart_916921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916921 prefixEnd_916921 := by exact prefixLift 916921
  have htrace : WordTrace (prefixWord ++ tailWord_916921) baseStart_916921 baseEnd_916921 := by
    simpa [prefixWord, tailWord_916921, baseEnd_916921] using wordTrace_append hprefix tailTrace_916921
  have hstable : (prefixWord ++ tailWord_916921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916921).length < 2 ^ (prefixWord ++ tailWord_916921).sum := by decide
  have hdescent : baseEnd_916921 < baseStart_916921 := by decide
  rcases family_descends (prefixWord ++ tailWord_916921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916991 : List Nat := [1, 1, 2, 2, 1, 2, 2, 10]
def baseStart_916991 : Nat := 118140960795 + 916991 * 2 ^ 59
def prefixEnd_916991 : Nat := 4983230072969 + 3 ^ 40 * 916991 * 2
def baseEnd_916991 : Nat := 69756613162537333658569

theorem tailTrace_916991 : CollatzResearch.WordTrace tailWord_916991 prefixEnd_916991 69756613162537333658569 := by
  unfold tailWord_916991
  simp only [CollatzResearch.WordTrace]
  refine ⟨33445409420905691439582827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22296939613937127626388551 33445409420905691439582827)
  ·
    refine ⟨50168114131358537159374241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33445409420905691439582827 50168114131358537159374241)
    ·
      refine ⟨37626085598518902869530681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50168114131358537159374241 37626085598518902869530681)
      ·
        refine ⟨28219564198889177152148011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37626085598518902869530681 28219564198889177152148011)
        ·
          refine ⟨42329346298333765728222017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28219564198889177152148011 42329346298333765728222017)
          ·
            refine ⟨31747009723750324296166513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42329346298333765728222017 31747009723750324296166513)
            ·
              refine ⟨23810257292812743222124885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31747009723750324296166513 23810257292812743222124885)
              ·
                refine ⟨69756613162537333658569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23810257292812743222124885 69756613162537333658569)
                ·
                  rfl

theorem cell21_916991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 10].length) (baseStart_916991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_916991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_916991 prefixEnd_916991 := by exact prefixLift 916991
  have htrace : WordTrace (prefixWord ++ tailWord_916991) baseStart_916991 baseEnd_916991 := by
    simpa [prefixWord, tailWord_916991, baseEnd_916991] using wordTrace_append hprefix tailTrace_916991
  have hstable : (prefixWord ++ tailWord_916991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916991).length < 2 ^ (prefixWord ++ tailWord_916991).sum := by decide
  have hdescent : baseEnd_916991 < baseStart_916991 := by decide
  rcases family_descends (prefixWord ++ tailWord_916991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917084 : List Nat := [2, 2, 4, 1, 2, 1, 9]
def baseStart_917084 : Nat := 118140960795 + 917084 * 2 ^ 59
def prefixEnd_917084 : Nat := 4983230072969 + 3 ^ 40 * 917084 * 2
def baseEnd_917084 : Nat := 23254562594962722880613

theorem tailTrace_917084 : CollatzResearch.WordTrace tailWord_917084 prefixEnd_917084 23254562594962722880613 := by
  unfold tailWord_917084
  simp only [CollatzResearch.WordTrace]
  refine ⟨16724400704784384161359153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22299200939712512215145537 16724400704784384161359153)
  ·
    refine ⟨12543300528588288121019365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16724400704784384161359153 12543300528588288121019365)
    ·
      refine ⟨2351868849110304022691131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12543300528588288121019365 2351868849110304022691131)
      ·
        refine ⟨3527803273665456034036697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351868849110304022691131 3527803273665456034036697)
        ·
          refine ⟨2645852455249092025527523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3527803273665456034036697 2645852455249092025527523)
          ·
            refine ⟨3968778682873638038291285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645852455249092025527523 3968778682873638038291285)
            ·
              refine ⟨23254562594962722880613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3968778682873638038291285 23254562594962722880613)
              ·
                rfl

theorem cell21_917084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 9].length) (baseStart_917084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917084 prefixEnd_917084 := by exact prefixLift 917084
  have htrace : WordTrace (prefixWord ++ tailWord_917084) baseStart_917084 baseEnd_917084 := by
    simpa [prefixWord, tailWord_917084, baseEnd_917084] using wordTrace_append hprefix tailTrace_917084
  have hstable : (prefixWord ++ tailWord_917084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917084).length < 2 ^ (prefixWord ++ tailWord_917084).sum := by decide
  have hdescent : baseEnd_917084 < baseStart_917084 := by decide
  rcases family_descends (prefixWord ++ tailWord_917084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917101 : List Nat := [1, 5, 1, 1, 4, 1, 2, 6]
def baseStart_917101 : Nat := 118140960795 + 917101 * 2 ^ 59
def prefixEnd_917101 : Nat := 4983230072969 + 3 ^ 40 * 917101 * 2
def baseEnd_917101 : Nat := 69764980995425418047383

theorem tailTrace_917101 : CollatzResearch.WordTrace tailWord_917101 prefixEnd_917101 69764980995425418047383 := by
  unfold tailWord_917101
  simp only [CollatzResearch.WordTrace]
  refine ⟨33449421450507180226087157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22299614300338120150724771 33449421450507180226087157)
  ·
    refine ⟨3135883260985048146195671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33449421450507180226087157 3135883260985048146195671)
    ·
      refine ⟨4703824891477572219293507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3135883260985048146195671 4703824891477572219293507)
      ·
        refine ⟨7055737337216358328940261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4703824891477572219293507 7055737337216358328940261)
        ·
          refine ⟨1322950750728067186676299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7055737337216358328940261 1322950750728067186676299)
          ·
            refine ⟨1984426126092100780014449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322950750728067186676299 1984426126092100780014449)
            ·
              refine ⟨1488319594569075585010837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984426126092100780014449 1488319594569075585010837)
              ·
                refine ⟨69764980995425418047383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1488319594569075585010837 69764980995425418047383)
                ·
                  rfl

theorem cell21_917101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 6].length) (baseStart_917101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917101 prefixEnd_917101 := by exact prefixLift 917101
  have htrace : WordTrace (prefixWord ++ tailWord_917101) baseStart_917101 baseEnd_917101 := by
    simpa [prefixWord, tailWord_917101, baseEnd_917101] using wordTrace_append hprefix tailTrace_917101
  have hstable : (prefixWord ++ tailWord_917101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917101).length < 2 ^ (prefixWord ++ tailWord_917101).sum := by decide
  have hdescent : baseEnd_917101 < baseStart_917101 := by decide
  rcases family_descends (prefixWord ++ tailWord_917101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917143 : List Nat := [1, 1, 3, 3, 2, 11]
def baseStart_917143 : Nat := 118140960795 + 917143 * 2 ^ 59
def prefixEnd_917143 : Nat := 4983230072969 + 3 ^ 40 * 917143 * 2
def baseEnd_917143 : Nat := 7752019554018278312669

theorem tailTrace_917143 : CollatzResearch.WordTrace tailWord_917143 prefixEnd_917143 7752019554018278312669 := by
  unfold tailWord_917143
  simp only [CollatzResearch.WordTrace]
  refine ⟨33450953316355021399116083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22300635544236680932744055 33450953316355021399116083)
  ·
    refine ⟨50176429974532532098674125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33450953316355021399116083 50176429974532532098674125)
    ·
      refine ⟨18816161240449699537002797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50176429974532532098674125 18816161240449699537002797)
      ·
        refine ⟨7056060465168637326376049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18816161240449699537002797 7056060465168637326376049)
        ·
          refine ⟨5292045348876477994782037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7056060465168637326376049 5292045348876477994782037)
          ·
            refine ⟨7752019554018278312669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5292045348876477994782037 7752019554018278312669)
            ·
              rfl

theorem cell21_917143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 11].length) (baseStart_917143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917143 prefixEnd_917143 := by exact prefixLift 917143
  have htrace : WordTrace (prefixWord ++ tailWord_917143) baseStart_917143 baseEnd_917143 := by
    simpa [prefixWord, tailWord_917143, baseEnd_917143] using wordTrace_append hprefix tailTrace_917143
  have hstable : (prefixWord ++ tailWord_917143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917143).length < 2 ^ (prefixWord ++ tailWord_917143).sum := by decide
  have hdescent : baseEnd_917143 < baseStart_917143 := by decide
  rcases family_descends (prefixWord ++ tailWord_917143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917318 : List Nat := [6, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_917318 : Nat := 118140960795 + 917318 * 2 ^ 59
def prefixEnd_917318 : Nat := 4983230072969 + 3 ^ 40 * 917318 * 2
def baseEnd_917318 : Nat := 209344465342732099025039

theorem tailTrace_917318 : CollatzResearch.WordTrace tailWord_917318 prefixEnd_917318 209344465342732099025039 := by
  unfold tailWord_917318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045541752835032071460519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22304890727147350857824405 1045541752835032071460519)
  ·
    refine ⟨1568312629252548107190779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1045541752835032071460519 1568312629252548107190779)
    ·
      refine ⟨2352468943878822160786169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568312629252548107190779 2352468943878822160786169)
      ·
        refine ⟨1764351707909116620589627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2352468943878822160786169 1764351707909116620589627)
        ·
          refine ⟨2646527561863674930884441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764351707909116620589627 2646527561863674930884441)
          ·
            refine ⟨1984895671397756198163331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2646527561863674930884441 1984895671397756198163331)
            ·
              refine ⟨2977343507096634297244997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984895671397756198163331 2977343507096634297244997)
              ·
                refine ⟨558251907580618930733437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2977343507096634297244997 558251907580618930733437)
                ·
                  refine ⟨209344465342732099025039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 558251907580618930733437 209344465342732099025039)
                  ·
                    rfl

theorem cell21_917318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_917318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917318 prefixEnd_917318 := by exact prefixLift 917318
  have htrace : WordTrace (prefixWord ++ tailWord_917318) baseStart_917318 baseEnd_917318 := by
    simpa [prefixWord, tailWord_917318, baseEnd_917318] using wordTrace_append hprefix tailTrace_917318
  have hstable : (prefixWord ++ tailWord_917318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917318).length < 2 ^ (prefixWord ++ tailWord_917318).sum := by decide
  have hdescent : baseEnd_917318 < baseStart_917318 := by decide
  rcases family_descends (prefixWord ++ tailWord_917318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917405 : List Nat := [1, 4, 2, 1, 2, 4, 2, 5]
def baseStart_917405 : Nat := 118140960795 + 917405 * 2 ^ 59
def prefixEnd_917405 : Nat := 4983230072969 + 3 ^ 40 * 917405 * 2
def baseEnd_917405 : Nat := 69788106642679760358287

theorem tailTrace_917405 : CollatzResearch.WordTrace tailWord_917405 prefixEnd_917405 69788106642679760358287 := by
  unfold tailWord_917405
  simp only [CollatzResearch.WordTrace]
  refine ⟨33460509241405840145153669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22307006160937226763435779 33460509241405840145153669)
  ·
    refine ⟨6273845482763595027216313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33460509241405840145153669 6273845482763595027216313)
    ·
      refine ⟨4705384112072696270412235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6273845482763595027216313 4705384112072696270412235)
      ·
        refine ⟨7058076168109044405618353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4705384112072696270412235 7058076168109044405618353)
        ·
          refine ⟨5293557126081783304213765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7058076168109044405618353 5293557126081783304213765)
          ·
            refine ⟨992541961140334369540081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5293557126081783304213765 992541961140334369540081)
            ·
              refine ⟨744406470855250777155061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992541961140334369540081 744406470855250777155061)
              ·
                refine ⟨69788106642679760358287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 744406470855250777155061 69788106642679760358287)
                ·
                  rfl

theorem cell21_917405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 5].length) (baseStart_917405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917405 prefixEnd_917405 := by exact prefixLift 917405
  have htrace : WordTrace (prefixWord ++ tailWord_917405) baseStart_917405 baseEnd_917405 := by
    simpa [prefixWord, tailWord_917405, baseEnd_917405] using wordTrace_append hprefix tailTrace_917405
  have hstable : (prefixWord ++ tailWord_917405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917405).length < 2 ^ (prefixWord ++ tailWord_917405).sum := by decide
  have hdescent : baseEnd_917405 < baseStart_917405 := by decide
  rcases family_descends (prefixWord ++ tailWord_917405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917433 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 4]
def baseStart_917433 : Nat := 118140960795 + 917433 * 2 ^ 59
def prefixEnd_917433 : Nat := 4983230072969 + 3 ^ 40 * 917433 * 2
def baseEnd_917433 : Nat := 209370709909517454608137

theorem tailTrace_917433 : CollatzResearch.WordTrace tailWord_917433 prefixEnd_917433 209370709909517454608137 := by
  unfold tailWord_917433
  simp only [CollatzResearch.WordTrace]
  refine ⟨33461530485304400927172953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22307686990202933951448635 33461530485304400927172953)
  ·
    refine ⟨25096147863978300695379715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33461530485304400927172953 25096147863978300695379715)
    ·
      refine ⟨37644221795967451043069573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25096147863978300695379715 37644221795967451043069573)
      ·
        refine ⟨7058291586743897070575545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37644221795967451043069573 7058291586743897070575545)
        ·
          refine ⟨5293718690057922802931659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7058291586743897070575545 5293718690057922802931659)
          ·
            refine ⟨7940578035086884204397489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5293718690057922802931659 7940578035086884204397489)
            ·
              refine ⟨5955433526315163153298117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7940578035086884204397489 5955433526315163153298117)
              ·
                refine ⟨1116643786184093091243397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5955433526315163153298117 1116643786184093091243397)
                ·
                  refine ⟨209370709909517454608137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1116643786184093091243397 209370709909517454608137)
                  ·
                    rfl

theorem cell21_917433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_917433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917433 prefixEnd_917433 := by exact prefixLift 917433
  have htrace : WordTrace (prefixWord ++ tailWord_917433) baseStart_917433 baseEnd_917433 := by
    simpa [prefixWord, tailWord_917433, baseEnd_917433] using wordTrace_append hprefix tailTrace_917433
  have hstable : (prefixWord ++ tailWord_917433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917433).length < 2 ^ (prefixWord ++ tailWord_917433).sum := by decide
  have hdescent : baseEnd_917433 < baseStart_917433 := by decide
  rcases family_descends (prefixWord ++ tailWord_917433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917450 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_917450 : Nat := 118140960795 + 917450 * 2 ^ 59
def prefixEnd_917450 : Nat := 4983230072969 + 3 ^ 40 * 917450 * 2
def baseEnd_917450 : Nat := 209374589541129202824769

theorem tailTrace_917450 : CollatzResearch.WordTrace tailWord_917450 prefixEnd_917450 209374589541129202824769 := by
  unfold tailWord_917450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8365537631560703207635451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22308100350828541887027869 8365537631560703207635451)
  ·
    refine ⟨12548306447341054811453177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8365537631560703207635451 12548306447341054811453177)
    ·
      refine ⟨9411229835505791108589883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12548306447341054811453177 9411229835505791108589883)
      ·
        refine ⟨14116844753258686662884825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9411229835505791108589883 14116844753258686662884825)
        ·
          refine ⟨10587633564944014997163619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14116844753258686662884825 10587633564944014997163619)
          ·
            refine ⟨15881450347416022495745429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10587633564944014997163619 15881450347416022495745429)
            ·
              refine ⟨744442985035126054488067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15881450347416022495745429 744442985035126054488067)
              ·
                refine ⟨1116664477552689081732101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744442985035126054488067 1116664477552689081732101)
                ·
                  refine ⟨209374589541129202824769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1116664477552689081732101 209374589541129202824769)
                  ·
                    rfl

theorem cell21_917450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_917450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917450 prefixEnd_917450 := by exact prefixLift 917450
  have htrace : WordTrace (prefixWord ++ tailWord_917450) baseStart_917450 baseEnd_917450 := by
    simpa [prefixWord, tailWord_917450, baseEnd_917450] using wordTrace_append hprefix tailTrace_917450
  have hstable : (prefixWord ++ tailWord_917450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917450).length < 2 ^ (prefixWord ++ tailWord_917450).sum := by decide
  have hdescent : baseEnd_917450 < baseStart_917450 := by decide
  rcases family_descends (prefixWord ++ tailWord_917450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917509 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 4]
def baseStart_917509 : Nat := 118140960795 + 917509 * 2 ^ 59
def prefixEnd_917509 : Nat := 4983230072969 + 3 ^ 40 * 917509 * 2
def baseEnd_917509 : Nat := 209388054144958211341315

theorem tailTrace_917509 : CollatzResearch.WordTrace tailWord_917509 prefixEnd_917509 209388054144958211341315 := by
  unfold tailWord_917509
  simp only [CollatzResearch.WordTrace]
  refine ⟨33464302433029065906939581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22309534955352710604626387 33464302433029065906939581)
  ·
    refine ⟨12549113412385899715102343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33464302433029065906939581 12549113412385899715102343)
    ·
      refine ⟨18823670118578849572653515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12549113412385899715102343 18823670118578849572653515)
      ·
        refine ⟨28235505177868274358980273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18823670118578849572653515 28235505177868274358980273)
        ·
          refine ⟨21176628883401205769235205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28235505177868274358980273 21176628883401205769235205)
          ·
            refine ⟨3970617915637726081731601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21176628883401205769235205 3970617915637726081731601)
            ·
              refine ⟨2977963436728294561298701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3970617915637726081731601 2977963436728294561298701)
              ·
                refine ⟨1116736288773110460487013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2977963436728294561298701 1116736288773110460487013)
                ·
                  refine ⟨209388054144958211341315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1116736288773110460487013 209388054144958211341315)
                  ·
                    rfl

theorem cell21_917509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_917509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917509 prefixEnd_917509 := by exact prefixLift 917509
  have htrace : WordTrace (prefixWord ++ tailWord_917509) baseStart_917509 baseEnd_917509 := by
    simpa [prefixWord, tailWord_917509, baseEnd_917509] using wordTrace_append hprefix tailTrace_917509
  have hstable : (prefixWord ++ tailWord_917509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917509).length < 2 ^ (prefixWord ++ tailWord_917509).sum := by decide
  have hdescent : baseEnd_917509 < baseStart_917509 := by decide
  rcases family_descends (prefixWord ++ tailWord_917509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917540 : List Nat := [2, 3, 1, 4, 2, 1, 8]
def baseStart_917540 : Nat := 118140960795 + 917540 * 2 ^ 59
def prefixEnd_917540 : Nat := 4983230072969 + 3 ^ 40 * 917540 * 2
def baseEnd_917540 : Nat := 23266125418589894036065

theorem tailTrace_917540 : CollatzResearch.WordTrace tailWord_917540 prefixEnd_917540 23266125418589894036065 := by
  unfold tailWord_917540
  simp only [CollatzResearch.WordTrace]
  refine ⟨16732716547958379100659037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22310288730611172134212049 16732716547958379100659037)
  ·
    refine ⟨6274768705484392162747139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16732716547958379100659037 6274768705484392162747139)
    ·
      refine ⟨9412153058226588244120709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6274768705484392162747139 9412153058226588244120709)
      ·
        refine ⟨1764778698417485295772633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9412153058226588244120709 1764778698417485295772633)
        ·
          refine ⟨1323584023813113971829475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1764778698417485295772633 1323584023813113971829475)
          ·
            refine ⟨1985376035719670957744213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323584023813113971829475 1985376035719670957744213)
            ·
              refine ⟨23266125418589894036065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1985376035719670957744213 23266125418589894036065)
              ·
                rfl

theorem cell21_917540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 8].length) (baseStart_917540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917540 prefixEnd_917540 := by exact prefixLift 917540
  have htrace : WordTrace (prefixWord ++ tailWord_917540) baseStart_917540 baseEnd_917540 := by
    simpa [prefixWord, tailWord_917540, baseEnd_917540] using wordTrace_append hprefix tailTrace_917540
  have hstable : (prefixWord ++ tailWord_917540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917540).length < 2 ^ (prefixWord ++ tailWord_917540).sum := by decide
  have hdescent : baseEnd_917540 < baseStart_917540 := by decide
  rcases family_descends (prefixWord ++ tailWord_917540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917554 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_917554 : Nat := 118140960795 + 917554 * 2 ^ 59
def prefixEnd_917554 : Nat := 4983230072969 + 3 ^ 40 * 917554 * 2
def baseEnd_917554 : Nat := 209398323758048133091223

theorem tailTrace_917554 : CollatzResearch.WordTrace tailWord_917554 prefixEnd_917554 209398323758048133091223 := by
  unfold tailWord_917554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8366485929466509648081929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22310629145244025728218477 8366485929466509648081929)
  ·
    refine ⟨6274864447099882236061447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8366485929466509648081929 6274864447099882236061447)
    ·
      refine ⟨9412296670649823354092171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6274864447099882236061447 9412296670649823354092171)
      ·
        refine ⟨14118445005974735031138257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9412296670649823354092171 14118445005974735031138257)
        ·
          refine ⟨10588833754481051273353693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14118445005974735031138257 10588833754481051273353693)
          ·
            refine ⟨3970812657930394227507635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10588833754481051273353693 3970812657930394227507635)
            ·
              refine ⟨5956218986895591341261453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3970812657930394227507635 5956218986895591341261453)
              ·
                refine ⟨2233582120085846752973045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5956218986895591341261453 2233582120085846752973045)
                ·
                  refine ⟨209398323758048133091223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2233582120085846752973045 209398323758048133091223)
                  ·
                    rfl

theorem cell21_917554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_917554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917554 prefixEnd_917554 := by exact prefixLift 917554
  have htrace : WordTrace (prefixWord ++ tailWord_917554) baseStart_917554 baseEnd_917554 := by
    simpa [prefixWord, tailWord_917554, baseEnd_917554] using wordTrace_append hprefix tailTrace_917554
  have hstable : (prefixWord ++ tailWord_917554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917554).length < 2 ^ (prefixWord ++ tailWord_917554).sum := by decide
  have hdescent : baseEnd_917554 < baseStart_917554 := by decide
  rcases family_descends (prefixWord ++ tailWord_917554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917661 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 4]
def baseStart_917661 : Nat := 118140960795 + 917661 * 2 ^ 59
def prefixEnd_917661 : Nat := 4983230072969 + 3 ^ 40 * 917661 * 2
def baseEnd_917661 : Nat := 209422742615839724807671

theorem tailTrace_917661 : CollatzResearch.WordTrace tailWord_917661 prefixEnd_917661 209422742615839724807671 := by
  unfold tailWord_917661
  simp only [CollatzResearch.WordTrace]
  refine ⟨33469846328478395866472837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22313230885652263910981891 33469846328478395866472837)
  ·
    refine ⟨6275596186589699224963657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33469846328478395866472837 6275596186589699224963657)
    ·
      refine ⟨4706697139942274418722743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6275596186589699224963657 4706697139942274418722743)
      ·
        refine ⟨7060045709913411628084115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4706697139942274418722743 7060045709913411628084115)
        ·
          refine ⟨10590068564870117442126173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7060045709913411628084115 10590068564870117442126173)
          ·
            refine ⟨3971275711826294040797315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10590068564870117442126173 3971275711826294040797315)
            ·
              refine ⟨5956913567739441061195973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3971275711826294040797315 5956913567739441061195973)
              ·
                refine ⟨1116921293951145198974245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5956913567739441061195973 1116921293951145198974245)
                ·
                  refine ⟨209422742615839724807671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1116921293951145198974245 209422742615839724807671)
                  ·
                    rfl

theorem cell21_917661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_917661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917661 prefixEnd_917661 := by exact prefixLift 917661
  have htrace : WordTrace (prefixWord ++ tailWord_917661) baseStart_917661 baseEnd_917661 := by
    simpa [prefixWord, tailWord_917661, baseEnd_917661] using wordTrace_append hprefix tailTrace_917661
  have hstable : (prefixWord ++ tailWord_917661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917661).length < 2 ^ (prefixWord ++ tailWord_917661).sum := by decide
  have hdescent : baseEnd_917661 < baseStart_917661 := by decide
  rcases family_descends (prefixWord ++ tailWord_917661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917664 : List Nat := [2, 1, 1, 4, 2, 2, 4, 2, 3]
def baseStart_917664 : Nat := 118140960795 + 917664 * 2 ^ 59
def prefixEnd_917664 : Nat := 4983230072969 + 3 ^ 40 * 917664 * 2
def baseEnd_917664 : Nat := 209423427256712386257665

theorem tailTrace_917664 : CollatzResearch.WordTrace tailWord_917664 prefixEnd_917664 209423427256712386257665 := by
  unfold tailWord_917664
  simp only [CollatzResearch.WordTrace]
  refine ⟨16734977873733763689416023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22313303831645018252554697 16734977873733763689416023)
  ·
    refine ⟨25102466810600645534124035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16734977873733763689416023 25102466810600645534124035)
    ·
      refine ⟨37653700215900968301186053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25102466810600645534124035 37653700215900968301186053)
      ·
        refine ⟨7060068790481431556472385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37653700215900968301186053 7060068790481431556472385)
        ·
          refine ⟨5295051592861073667354289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7060068790481431556472385 5295051592861073667354289)
          ·
            refine ⟨3971288694645805250515717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5295051592861073667354289 3971288694645805250515717)
            ·
              refine ⟨744616630246088484471697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3971288694645805250515717 744616630246088484471697)
              ·
                refine ⟨558462472684566363353773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744616630246088484471697 558462472684566363353773)
                ·
                  refine ⟨209423427256712386257665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 558462472684566363353773 209423427256712386257665)
                  ·
                    rfl

theorem cell21_917664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 3].length) (baseStart_917664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917664 prefixEnd_917664 := by exact prefixLift 917664
  have htrace : WordTrace (prefixWord ++ tailWord_917664) baseStart_917664 baseEnd_917664 := by
    simpa [prefixWord, tailWord_917664, baseEnd_917664] using wordTrace_append hprefix tailTrace_917664
  have hstable : (prefixWord ++ tailWord_917664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917664).length < 2 ^ (prefixWord ++ tailWord_917664).sum := by decide
  have hdescent : baseEnd_917664 < baseStart_917664 := by decide
  rcases family_descends (prefixWord ++ tailWord_917664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917698 : List Nat := [3, 5, 1, 1, 1, 2, 2, 3, 3]
def baseStart_917698 : Nat := 118140960795 + 917698 * 2 ^ 59
def prefixEnd_917698 : Nat := 4983230072969 + 3 ^ 40 * 917698 * 2
def baseEnd_917698 : Nat := 209431186519935882690929

theorem tailTrace_917698 : CollatzResearch.WordTrace tailWord_917698 prefixEnd_917698 209431186519935882690929 := by
  unfold tailWord_917698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8367798957336087796392437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22314130552896234123713165 8367798957336087796392437)
  ·
    refine ⟨784481152250258230911791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8367798957336087796392437 784481152250258230911791)
    ·
      refine ⟨1176721728375387346367687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 784481152250258230911791 1176721728375387346367687)
      ·
        refine ⟨1765082592563081019551531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176721728375387346367687 1765082592563081019551531)
        ·
          refine ⟨2647623888844621529327297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765082592563081019551531 2647623888844621529327297)
          ·
            refine ⟨1985717916633466146995473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647623888844621529327297 1985717916633466146995473)
            ·
              refine ⟨1489288437475099610246605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985717916633466146995473 1489288437475099610246605)
              ·
                refine ⟨558483164053162353842477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1489288437475099610246605 558483164053162353842477)
                ·
                  refine ⟨209431186519935882690929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 558483164053162353842477 209431186519935882690929)
                  ·
                    rfl

theorem cell21_917698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_917698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917698 prefixEnd_917698 := by exact prefixLift 917698
  have htrace : WordTrace (prefixWord ++ tailWord_917698) baseStart_917698 baseEnd_917698 := by
    simpa [prefixWord, tailWord_917698, baseEnd_917698] using wordTrace_append hprefix tailTrace_917698
  have hstable : (prefixWord ++ tailWord_917698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917698).length < 2 ^ (prefixWord ++ tailWord_917698).sum := by decide
  have hdescent : baseEnd_917698 < baseStart_917698 := by decide
  rcases family_descends (prefixWord ++ tailWord_917698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917844 : List Nat := [2, 4, 1, 1, 2, 4, 1, 6]
def baseStart_917844 : Nat := 118140960795 + 917844 * 2 ^ 59
def prefixEnd_917844 : Nat := 4983230072969 + 3 ^ 40 * 917844 * 2
def baseEnd_917844 : Nat := 69821501903024024419099

theorem tailTrace_917844 : CollatzResearch.WordTrace tailWord_917844 prefixEnd_917844 69821501903024024419099 := by
  unfold tailWord_917844
  simp only [CollatzResearch.WordTrace]
  refine ⟨16738260443407709060192293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22317680591210278746923057 16738260443407709060192293)
  ·
    refine ⟨3138423833138945448786055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16738260443407709060192293 3138423833138945448786055)
    ·
      refine ⟨4707635749708418173179083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3138423833138945448786055 4707635749708418173179083)
      ·
        refine ⟨7061453624562627259768625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707635749708418173179083 7061453624562627259768625)
        ·
          refine ⟨5296090218421970444826469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7061453624562627259768625 5296090218421970444826469)
          ·
            refine ⟨993016915954119458404963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5296090218421970444826469 993016915954119458404963)
            ·
              refine ⟨1489525373931179187607445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993016915954119458404963 1489525373931179187607445)
              ·
                refine ⟨69821501903024024419099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1489525373931179187607445 69821501903024024419099)
                ·
                  rfl

theorem cell21_917844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_917844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917844 prefixEnd_917844 := by exact prefixLift 917844
  have htrace : WordTrace (prefixWord ++ tailWord_917844) baseStart_917844 baseEnd_917844 := by
    simpa [prefixWord, tailWord_917844, baseEnd_917844] using wordTrace_append hprefix tailTrace_917844
  have hstable : (prefixWord ++ tailWord_917844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917844).length < 2 ^ (prefixWord ++ tailWord_917844).sum := by decide
  have hdescent : baseEnd_917844 < baseStart_917844 := by decide
  rcases family_descends (prefixWord ++ tailWord_917844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917858 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_917858 : Nat := 118140960795 + 917858 * 2 ^ 59
def prefixEnd_917858 : Nat := 4983230072969 + 3 ^ 40 * 917858 * 2
def baseEnd_917858 : Nat := 209467700699811160023935

theorem tailTrace_917858 : CollatzResearch.WordTrace tailWord_917858 prefixEnd_917858 209467700699811160023935 := by
  unfold tailWord_917858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8369257877191174627848557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22318021005843132340929485 8369257877191174627848557)
  ·
    refine ⟨3138471703946690485443209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8369257877191174627848557 3138471703946690485443209)
    ·
      refine ⟨2353853777960017864082407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3138471703946690485443209 2353853777960017864082407)
      ·
        refine ⟨3530780666940026796123611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353853777960017864082407 3530780666940026796123611)
        ·
          refine ⟨5296171000410040194185417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3530780666940026796123611 5296171000410040194185417)
          ·
            refine ⟨3972128250307530145639063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5296171000410040194185417 3972128250307530145639063)
            ·
              refine ⟨5958192375461295218458595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972128250307530145639063 5958192375461295218458595)
              ·
                refine ⟨8937288563191942827687893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5958192375461295218458595 8937288563191942827687893)
                ·
                  refine ⟨209467700699811160023935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8937288563191942827687893 209467700699811160023935)
                  ·
                    rfl

theorem cell21_917858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_917858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917858 prefixEnd_917858 := by exact prefixLift 917858
  have htrace : WordTrace (prefixWord ++ tailWord_917858) baseStart_917858 baseEnd_917858 := by
    simpa [prefixWord, tailWord_917858, baseEnd_917858] using wordTrace_append hprefix tailTrace_917858
  have hstable : (prefixWord ++ tailWord_917858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917858).length < 2 ^ (prefixWord ++ tailWord_917858).sum := by decide
  have hdescent : baseEnd_917858 < baseStart_917858 := by decide
  rcases family_descends (prefixWord ++ tailWord_917858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917889 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 6]
def baseStart_917889 : Nat := 118140960795 + 917889 * 2 ^ 59
def prefixEnd_917889 : Nat := 4983230072969 + 3 ^ 40 * 917889 * 2
def baseEnd_917889 : Nat := 209474775322161995007205

theorem tailTrace_917889 : CollatzResearch.WordTrace tailWord_917889 prefixEnd_917889 209474775322161995007205 := by
  unfold tailWord_917889
  simp only [CollatzResearch.WordTrace]
  refine ⟨33478162171652390805772721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22318774781101593870515147 33478162171652390805772721)
  ·
    refine ⟨25108621628739293104329541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33478162171652390805772721 25108621628739293104329541)
    ·
      refine ⟨4707866555388617457061789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25108621628739293104329541 4707866555388617457061789)
      ·
        refine ⟨1765449958270731546398171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4707866555388617457061789 1765449958270731546398171)
        ·
          refine ⟨2648174937406097319597257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765449958270731546398171 2648174937406097319597257)
          ·
            refine ⟨1986131203054572989697943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2648174937406097319597257 1986131203054572989697943)
            ·
              refine ⟨2979196804581859484546915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986131203054572989697943 2979196804581859484546915)
              ·
                refine ⟨4468795206872789226820373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979196804581859484546915 4468795206872789226820373)
                ·
                  refine ⟨209474775322161995007205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4468795206872789226820373 209474775322161995007205)
                  ·
                    rfl

theorem cell21_917889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_917889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917889 prefixEnd_917889 := by exact prefixLift 917889
  have htrace : WordTrace (prefixWord ++ tailWord_917889) baseStart_917889 baseEnd_917889 := by
    simpa [prefixWord, tailWord_917889, baseEnd_917889] using wordTrace_append hprefix tailTrace_917889
  have hstable : (prefixWord ++ tailWord_917889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917889).length < 2 ^ (prefixWord ++ tailWord_917889).sum := by decide
  have hdescent : baseEnd_917889 < baseStart_917889 := by decide
  rcases family_descends (prefixWord ++ tailWord_917889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917920 : List Nat := [2, 1, 1, 4, 1, 5, 2, 5]
def baseStart_917920 : Nat := 118140960795 + 917920 * 2 ^ 59
def prefixEnd_917920 : Nat := 4983230072969 + 3 ^ 40 * 917920 * 2
def baseEnd_917920 : Nat := 69827283314837609996825

theorem tailTrace_917920 : CollatzResearch.WordTrace tailWord_917920 prefixEnd_917920 69827283314837609996825 := by
  unfold tailWord_917920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16739646417270041550075607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22319528556360055400100809 16739646417270041550075607)
  ·
    refine ⟨25109469625905062325113411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16739646417270041550075607 25109469625905062325113411)
    ·
      refine ⟨37664204438857593487670117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25109469625905062325113411 37664204438857593487670117)
      ·
        refine ⟨7062038332285798778938147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37664204438857593487670117 7062038332285798778938147)
        ·
          refine ⟨10593057498428698168407221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7062038332285798778938147 10593057498428698168407221)
          ·
            refine ⟨993099140477690453288177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10593057498428698168407221 993099140477690453288177)
            ·
              refine ⟨744824355358267839966133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993099140477690453288177 744824355358267839966133)
              ·
                refine ⟨69827283314837609996825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 744824355358267839966133 69827283314837609996825)
                ·
                  rfl

theorem cell21_917920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_917920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_917920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_917920 prefixEnd_917920 := by exact prefixLift 917920
  have htrace : WordTrace (prefixWord ++ tailWord_917920) baseStart_917920 baseEnd_917920 := by
    simpa [prefixWord, tailWord_917920, baseEnd_917920] using wordTrace_append hprefix tailTrace_917920
  have hstable : (prefixWord ++ tailWord_917920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917920).length < 2 ^ (prefixWord ++ tailWord_917920).sum := by decide
  have hdescent : baseEnd_917920 < baseStart_917920 := by decide
  rcases family_descends (prefixWord ++ tailWord_917920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918002 : List Nat := [3, 2, 1, 4, 3, 1, 2, 2, 3]
def baseStart_918002 : Nat := 118140960795 + 918002 * 2 ^ 59
def prefixEnd_918002 : Nat := 4983230072969 + 3 ^ 40 * 918002 * 2
def baseEnd_918002 : Nat := 209500563461698909623641

theorem tailTrace_918002 : CollatzResearch.WordTrace tailWord_918002 prefixEnd_918002 209500563461698909623641 := by
  unfold tailWord_918002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8370570905060752776159065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22321522413495340736424173 8370570905060752776159065)
  ·
    refine ⟨6277928178795564582119299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8370570905060752776159065 6277928178795564582119299)
    ·
      refine ⟨9416892268193346873178949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6277928178795564582119299 9416892268193346873178949)
      ·
        refine ⟨1765667300286252538721053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9416892268193346873178949 1765667300286252538721053)
        ·
          refine ⟨662125237607344702020395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1765667300286252538721053 662125237607344702020395)
          ·
            refine ⟨993187856411017053030593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662125237607344702020395 993187856411017053030593)
            ·
              refine ⟨744890892308262789772945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993187856411017053030593 744890892308262789772945)
              ·
                refine ⟨558668169231197092329709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744890892308262789772945 558668169231197092329709)
                ·
                  refine ⟨209500563461698909623641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 558668169231197092329709 209500563461698909623641)
                  ·
                    rfl

theorem cell21_918002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_918002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918002 prefixEnd_918002 := by exact prefixLift 918002
  have htrace : WordTrace (prefixWord ++ tailWord_918002) baseStart_918002 baseEnd_918002 := by
    simpa [prefixWord, tailWord_918002, baseEnd_918002] using wordTrace_append hprefix tailTrace_918002
  have hstable : (prefixWord ++ tailWord_918002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918002).length < 2 ^ (prefixWord ++ tailWord_918002).sum := by decide
  have hdescent : baseEnd_918002 < baseStart_918002 := by decide
  rcases family_descends (prefixWord ++ tailWord_918002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918007 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 10]
def baseStart_918007 : Nat := 118140960795 + 918007 * 2 ^ 59
def prefixEnd_918007 : Nat := 4983230072969 + 3 ^ 40 * 918007 * 2
def baseEnd_918007 : Nat := 209501704529820012040297

theorem tailTrace_918007 : CollatzResearch.WordTrace tailWord_918007 prefixEnd_918007 209501704529820012040297 := by
  unfold tailWord_918007
  simp only [CollatzResearch.WordTrace]
  refine ⟨33482465985224896958568275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22321643990149931305712183 33482465985224896958568275)
  ·
    refine ⟨50223698977837345437852413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33482465985224896958568275 50223698977837345437852413)
    ·
      refine ⟨18833887116689004539194655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50223698977837345437852413 18833887116689004539194655)
      ·
        refine ⟨28250830675033506808791983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18833887116689004539194655 28250830675033506808791983)
        ·
          refine ⟨42376246012550260213187975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28250830675033506808791983 42376246012550260213187975)
          ·
            refine ⟨63564369018825390319781963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42376246012550260213187975 63564369018825390319781963)
            ·
              refine ⟨95346553528238085479672945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63564369018825390319781963 95346553528238085479672945)
              ·
                refine ⟨71509915146178564109754709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95346553528238085479672945 71509915146178564109754709)
                ·
                  refine ⟨209501704529820012040297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 71509915146178564109754709 209501704529820012040297)
                  ·
                    rfl

theorem cell21_918007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_918007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918007 prefixEnd_918007 := by exact prefixLift 918007
  have htrace : WordTrace (prefixWord ++ tailWord_918007) baseStart_918007 baseEnd_918007 := by
    simpa [prefixWord, tailWord_918007, baseEnd_918007] using wordTrace_append hprefix tailTrace_918007
  have hstable : (prefixWord ++ tailWord_918007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918007).length < 2 ^ (prefixWord ++ tailWord_918007).sum := by decide
  have hdescent : baseEnd_918007 < baseStart_918007 := by decide
  rcases family_descends (prefixWord ++ tailWord_918007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918058 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_918058 : Nat := 118140960795 + 918058 * 2 ^ 59
def prefixEnd_918058 : Nat := 4983230072969 + 3 ^ 40 * 918058 * 2
def baseEnd_918058 : Nat := 209513343424655256690193

theorem tailTrace_918058 : CollatzResearch.WordTrace tailWord_918058 prefixEnd_918058 209513343424655256690193 := by
  unfold tailWord_918058
  simp only [CollatzResearch.WordTrace]
  refine ⟨8371081527010033167168707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22322884072026755112449885 8371081527010033167168707)
  ·
    refine ⟨12556622290515049750753061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8371081527010033167168707 12556622290515049750753061)
    ·
      refine ⟨2354366679471571828266199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12556622290515049750753061 2354366679471571828266199)
      ·
        refine ⟨3531550019207357742399299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354366679471571828266199 3531550019207357742399299)
        ·
          refine ⟨5297325028811036613598949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531550019207357742399299 5297325028811036613598949)
          ·
            refine ⟨993248442902069365049803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5297325028811036613598949 993248442902069365049803)
            ·
              refine ⟨1489872664353104047574705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993248442902069365049803 1489872664353104047574705)
              ·
                refine ⟨1117404498264828035681029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1489872664353104047574705 1117404498264828035681029)
                ·
                  refine ⟨209513343424655256690193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1117404498264828035681029 209513343424655256690193)
                  ·
                    rfl

theorem cell21_918058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_918058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918058 prefixEnd_918058 := by exact prefixLift 918058
  have htrace : WordTrace (prefixWord ++ tailWord_918058) baseStart_918058 baseEnd_918058 := by
    simpa [prefixWord, tailWord_918058, baseEnd_918058] using wordTrace_append hprefix tailTrace_918058
  have hstable : (prefixWord ++ tailWord_918058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918058).length < 2 ^ (prefixWord ++ tailWord_918058).sum := by decide
  have hdescent : baseEnd_918058 < baseStart_918058 := by decide
  rcases family_descends (prefixWord ++ tailWord_918058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918061 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 5]
def baseStart_918061 : Nat := 118140960795 + 918061 * 2 ^ 59
def prefixEnd_918061 : Nat := 4983230072969 + 3 ^ 40 * 918061 * 2
def baseEnd_918061 : Nat := 209514028065527918140187

theorem tailTrace_918061 : CollatzResearch.WordTrace tailWord_918061 prefixEnd_918061 209514028065527918140187 := by
  unfold tailWord_918061
  simp only [CollatzResearch.WordTrace]
  refine ⟨33484435527029264181034037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22322957018019509454022691 33484435527029264181034037)
  ·
    refine ⟨3139165830658993516971941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33484435527029264181034037 3139165830658993516971941)
    ·
      refine ⟨588593593248561284432239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3139165830658993516971941 588593593248561284432239)
      ·
        refine ⟨882890389872841926648359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588593593248561284432239 882890389872841926648359)
        ·
          refine ⟨1324335584809262889972539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882890389872841926648359 1324335584809262889972539)
          ·
            refine ⟨1986503377213894334958809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324335584809262889972539 1986503377213894334958809)
            ·
              refine ⟨1489877532910420751219107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986503377213894334958809 1489877532910420751219107)
              ·
                refine ⟨2234816299365631126828661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489877532910420751219107 2234816299365631126828661)
                ·
                  refine ⟨209514028065527918140187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2234816299365631126828661 209514028065527918140187)
                  ·
                    rfl

theorem cell21_918061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_918061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918061 prefixEnd_918061 := by exact prefixLift 918061
  have htrace : WordTrace (prefixWord ++ tailWord_918061) baseStart_918061 baseEnd_918061 := by
    simpa [prefixWord, tailWord_918061, baseEnd_918061] using wordTrace_append hprefix tailTrace_918061
  have hstable : (prefixWord ++ tailWord_918061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918061).length < 2 ^ (prefixWord ++ tailWord_918061).sum := by decide
  have hdescent : baseEnd_918061 < baseStart_918061 := by decide
  rcases family_descends (prefixWord ++ tailWord_918061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918100 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_918100 : Nat := 118140960795 + 918100 * 2 ^ 59
def prefixEnd_918100 : Nat := 4983230072969 + 3 ^ 40 * 918100 * 2
def baseEnd_918100 : Nat := 209522928396872516990107

theorem tailTrace_918100 : CollatzResearch.WordTrace tailWord_918100 prefixEnd_918100 209522928396872516990107 := by
  unfold tailWord_918100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16742928986943986920851877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22323905315925315894469169 16742928986943986920851877)
  ·
    refine ⟨3139299185051997547659727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16742928986943986920851877 3139299185051997547659727)
    ·
      refine ⟨4708948777577996321489591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139299185051997547659727 4708948777577996321489591)
      ·
        refine ⟨7063423166366994482234387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4708948777577996321489591 7063423166366994482234387)
        ·
          refine ⟨10595134749550491723351581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7063423166366994482234387 10595134749550491723351581)
          ·
            refine ⟨3973175531081434396256843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10595134749550491723351581 3973175531081434396256843)
            ·
              refine ⟨5959763296622151594385265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973175531081434396256843 5959763296622151594385265)
              ·
                refine ⟨4469822472466613695788949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5959763296622151594385265 4469822472466613695788949)
                ·
                  refine ⟨209522928396872516990107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4469822472466613695788949 209522928396872516990107)
                  ·
                    rfl

theorem cell21_918100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_918100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918100 prefixEnd_918100 := by exact prefixLift 918100
  have htrace : WordTrace (prefixWord ++ tailWord_918100) baseStart_918100 baseEnd_918100 := by
    simpa [prefixWord, tailWord_918100, baseEnd_918100] using wordTrace_append hprefix tailTrace_918100
  have hstable : (prefixWord ++ tailWord_918100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918100).length < 2 ^ (prefixWord ++ tailWord_918100).sum := by decide
  have hdescent : baseEnd_918100 < baseStart_918100 := by decide
  rcases family_descends (prefixWord ++ tailWord_918100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918120 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 5]
def baseStart_918120 : Nat := 118140960795 + 918120 * 2 ^ 59
def prefixEnd_918120 : Nat := 4983230072969 + 3 ^ 40 * 918120 * 2
def baseEnd_918120 : Nat := 209527492669356926656733

theorem tailTrace_918120 : CollatzResearch.WordTrace tailWord_918120 prefixEnd_918120 209527492669356926656733 := by
  unfold tailWord_918120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16743293716907758628715907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22324391622543678171621209 16743293716907758628715907)
  ·
    refine ⟨25114940575361637943073861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16743293716907758628715907 25114940575361637943073861)
    ·
      refine ⟨4709051357880307114326349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25114940575361637943073861 4709051357880307114326349)
      ·
        refine ⟨1765894259205115167872381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4709051357880307114326349 1765894259205115167872381)
        ·
          refine ⟨662210347201918187952143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1765894259205115167872381 662210347201918187952143)
          ·
            refine ⟨993315520802877281928215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662210347201918187952143 993315520802877281928215)
            ·
              refine ⟨1489973281204315922892323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993315520802877281928215 1489973281204315922892323)
              ·
                refine ⟨2234959921806473884338485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489973281204315922892323 2234959921806473884338485)
                ·
                  refine ⟨209527492669356926656733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2234959921806473884338485 209527492669356926656733)
                  ·
                    rfl

theorem cell21_918120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 5].length) (baseStart_918120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918120 prefixEnd_918120 := by exact prefixLift 918120
  have htrace : WordTrace (prefixWord ++ tailWord_918120) baseStart_918120 baseEnd_918120 := by
    simpa [prefixWord, tailWord_918120, baseEnd_918120] using wordTrace_append hprefix tailTrace_918120
  have hstable : (prefixWord ++ tailWord_918120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918120).length < 2 ^ (prefixWord ++ tailWord_918120).sum := by decide
  have hdescent : baseEnd_918120 < baseStart_918120 := by decide
  rcases family_descends (prefixWord ++ tailWord_918120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918134 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_918134 : Nat := 118140960795 + 918134 * 2 ^ 59
def prefixEnd_918134 : Nat := 4983230072969 + 3 ^ 40 * 918134 * 2
def baseEnd_918134 : Nat := 209530687660096013423371

theorem tailTrace_918134 : CollatzResearch.WordTrace tailWord_918134 prefixEnd_918134 209530687660096013423371 := by
  unfold tailWord_918134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092943628485299853027591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22324732037176531765627637 2092943628485299853027591)
  ·
    refine ⟨3139415442727949779541387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2092943628485299853027591 3139415442727949779541387)
    ·
      refine ⟨4709123164091924669312081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139415442727949779541387 4709123164091924669312081)
      ·
        refine ⟨3531842373068943501984061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4709123164091924669312081 3531842373068943501984061)
        ·
          refine ⟨1324440889900853813244023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3531842373068943501984061 1324440889900853813244023)
          ·
            refine ⟨1986661334851280719866035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324440889900853813244023 1986661334851280719866035)
            ·
              refine ⟨2979992002276921079799053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986661334851280719866035 2979992002276921079799053)
              ·
                refine ⟨1117497000853845404924645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2979992002276921079799053 1117497000853845404924645)
                ·
                  refine ⟨209530687660096013423371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1117497000853845404924645 209530687660096013423371)
                  ·
                    rfl

theorem cell21_918134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_918134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918134 prefixEnd_918134 := by exact prefixLift 918134
  have htrace : WordTrace (prefixWord ++ tailWord_918134) baseStart_918134 baseEnd_918134 := by
    simpa [prefixWord, tailWord_918134, baseEnd_918134] using wordTrace_append hprefix tailTrace_918134
  have hstable : (prefixWord ++ tailWord_918134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918134).length < 2 ^ (prefixWord ++ tailWord_918134).sum := by decide
  have hdescent : baseEnd_918134 < baseStart_918134 := by decide
  rcases family_descends (prefixWord ++ tailWord_918134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918145 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 7]
def baseStart_918145 : Nat := 118140960795 + 918145 * 2 ^ 59
def prefixEnd_918145 : Nat := 4983230072969 + 3 ^ 40 * 918145 * 2
def baseEnd_918145 : Nat := 209533198009962438740015

theorem tailTrace_918145 : CollatzResearch.WordTrace tailWord_918145 prefixEnd_918145 209533198009962438740015 := by
  unfold tailWord_918145
  simp only [CollatzResearch.WordTrace]
  refine ⟨33487499258724946527091889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22324999505816631018061259 33487499258724946527091889)
  ·
    refine ⟨25115624444043709895318917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33487499258724946527091889 25115624444043709895318917)
    ·
      refine ⟨4709179583258195605372297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25115624444043709895318917 4709179583258195605372297)
      ·
        refine ⟨3531884687443646704029223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4709179583258195605372297 3531884687443646704029223)
        ·
          refine ⟨5297827031165470056043835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531884687443646704029223 5297827031165470056043835)
          ·
            refine ⟨7946740546748205084065753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297827031165470056043835 7946740546748205084065753)
            ·
              refine ⟨5960055410061153813049315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7946740546748205084065753 5960055410061153813049315)
              ·
                refine ⟨8940083115091730719573973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960055410061153813049315 8940083115091730719573973)
                ·
                  refine ⟨209533198009962438740015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8940083115091730719573973 209533198009962438740015)
                  ·
                    rfl

theorem cell21_918145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_918145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918145 prefixEnd_918145 := by exact prefixLift 918145
  have htrace : WordTrace (prefixWord ++ tailWord_918145) baseStart_918145 baseEnd_918145 := by
    simpa [prefixWord, tailWord_918145, baseEnd_918145] using wordTrace_append hprefix tailTrace_918145
  have hstable : (prefixWord ++ tailWord_918145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918145).length < 2 ^ (prefixWord ++ tailWord_918145).sum := by decide
  have hdescent : baseEnd_918145 < baseStart_918145 := by decide
  rcases family_descends (prefixWord ++ tailWord_918145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918207 : List Nat := [1, 1, 2, 2, 2, 5, 3, 5]
def baseStart_918207 : Nat := 118140960795 + 918207 * 2 ^ 59
def prefixEnd_918207 : Nat := 4983230072969 + 3 ^ 40 * 918207 * 2
def baseEnd_918207 : Nat := 69849115751554702902185

theorem tailTrace_918207 : CollatzResearch.WordTrace tailWord_918207 prefixEnd_918207 69849115751554702902185 := by
  unfold tailWord_918207
  simp only [CollatzResearch.WordTrace]
  refine ⟨33489760584500331115848875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22326507056333554077232583 33489760584500331115848875)
  ·
    refine ⟨50234640876750496673773313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33489760584500331115848875 50234640876750496673773313)
    ·
      refine ⟨37675980657562872505329985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50234640876750496673773313 37675980657562872505329985)
      ·
        refine ⟨28256985493172154378997489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37675980657562872505329985 28256985493172154378997489)
        ·
          refine ⟨21192739119879115784248117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28256985493172154378997489 21192739119879115784248117)
          ·
            refine ⟨1986819292488667104773261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21192739119879115784248117 1986819292488667104773261)
            ·
              refine ⟨745057234683250164289973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1986819292488667104773261 745057234683250164289973)
              ·
                refine ⟨69849115751554702902185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 745057234683250164289973 69849115751554702902185)
                ·
                  rfl

theorem cell21_918207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 5].length) (baseStart_918207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918207 prefixEnd_918207 := by exact prefixLift 918207
  have htrace : WordTrace (prefixWord ++ tailWord_918207) baseStart_918207 baseEnd_918207 := by
    simpa [prefixWord, tailWord_918207, baseEnd_918207] using wordTrace_append hprefix tailTrace_918207
  have hstable : (prefixWord ++ tailWord_918207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918207).length < 2 ^ (prefixWord ++ tailWord_918207).sum := by decide
  have hdescent : baseEnd_918207 < baseStart_918207 := by decide
  rcases family_descends (prefixWord ++ tailWord_918207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918348 : List Nat := [2, 2, 1, 3, 3, 3, 2, 2, 3]
def baseStart_918348 : Nat := 118140960795 + 918348 * 2 ^ 59
def prefixEnd_918348 : Nat := 4983230072969 + 3 ^ 40 * 918348 * 2
def baseEnd_918348 : Nat := 209579525375679196856267

theorem tailTrace_918348 : CollatzResearch.WordTrace tailWord_918348 prefixEnd_918348 209579525375679196856267 := by
  unfold tailWord_918348
  simp only [CollatzResearch.WordTrace]
  refine ⟨16747451638494756098365849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22329935517993008131154465 16747451638494756098365849)
  ·
    refine ⟨12560588728871067073774387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16747451638494756098365849 12560588728871067073774387)
    ·
      refine ⟨18840883093306600610661581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12560588728871067073774387 18840883093306600610661581)
      ·
        refine ⟨7065331159989975228998093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18840883093306600610661581 7065331159989975228998093)
        ·
          refine ⟨2649499184996240710874285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7065331159989975228998093 2649499184996240710874285)
          ·
            refine ⟨993562194373590266577857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2649499184996240710874285 993562194373590266577857)
            ·
              refine ⟨745171645780192699933393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993562194373590266577857 745171645780192699933393)
              ·
                refine ⟨558878734335144524950045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745171645780192699933393 558878734335144524950045)
                ·
                  refine ⟨209579525375679196856267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 558878734335144524950045 209579525375679196856267)
                  ·
                    rfl

theorem cell21_918348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_918348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918348 prefixEnd_918348 := by exact prefixLift 918348
  have htrace : WordTrace (prefixWord ++ tailWord_918348) baseStart_918348 baseEnd_918348 := by
    simpa [prefixWord, tailWord_918348, baseEnd_918348] using wordTrace_append hprefix tailTrace_918348
  have hstable : (prefixWord ++ tailWord_918348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918348).length < 2 ^ (prefixWord ++ tailWord_918348).sum := by decide
  have hdescent : baseEnd_918348 < baseStart_918348 := by decide
  rcases family_descends (prefixWord ++ tailWord_918348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918359 : List Nat := [1, 1, 3, 2, 4, 3, 1, 6]
def baseStart_918359 : Nat := 118140960795 + 918359 * 2 ^ 59
def prefixEnd_918359 : Nat := 4983230072969 + 3 ^ 40 * 918359 * 2
def baseEnd_918359 : Nat := 69860678575181874057637

theorem tailTrace_918359 : CollatzResearch.WordTrace tailWord_918359 prefixEnd_918359 69860678575181874057637 := by
  unfold tailWord_918359
  simp only [CollatzResearch.WordTrace]
  refine ⟨33495304479949661075382131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22330202986633107383588087 33495304479949661075382131)
  ·
    refine ⟨50242956719924491613073197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33495304479949661075382131 50242956719924491613073197)
    ·
      refine ⟨18841108769971684354902449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50242956719924491613073197 18841108769971684354902449)
      ·
        refine ⟨14130831577478763266176837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18841108769971684354902449 14130831577478763266176837)
        ·
          refine ⟨2649530920777268112408157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14130831577478763266176837 2649530920777268112408157)
          ·
            refine ⟨993574095291475542153059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2649530920777268112408157 993574095291475542153059)
            ·
              refine ⟨1490361142937213313229589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993574095291475542153059 1490361142937213313229589)
              ·
                refine ⟨69860678575181874057637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1490361142937213313229589 69860678575181874057637)
                ·
                  rfl

theorem cell21_918359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 6].length) (baseStart_918359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918359 prefixEnd_918359 := by exact prefixLift 918359
  have htrace : WordTrace (prefixWord ++ tailWord_918359) baseStart_918359 baseEnd_918359 := by
    simpa [prefixWord, tailWord_918359, baseEnd_918359] using wordTrace_append hprefix tailTrace_918359
  have hstable : (prefixWord ++ tailWord_918359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918359).length < 2 ^ (prefixWord ++ tailWord_918359).sum := by decide
  have hdescent : baseEnd_918359 < baseStart_918359 := by decide
  rcases family_descends (prefixWord ++ tailWord_918359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918421 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 4]
def baseStart_918421 : Nat := 118140960795 + 918421 * 2 ^ 59
def prefixEnd_918421 : Nat := 4983230072969 + 3 ^ 40 * 918421 * 2
def baseEnd_918421 : Nat := 209596184970247292139451

theorem tailTrace_918421 : CollatzResearch.WordTrace tailWord_918421 prefixEnd_918421 209596184970247292139451 := by
  unfold tailWord_918421
  simp only [CollatzResearch.WordTrace]
  refine ⟨33497565805725045664139117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22331710537150030442759411 33497565805725045664139117)
  ·
    refine ⟨12561587177146892124052169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33497565805725045664139117 12561587177146892124052169)
    ·
      refine ⟨9421190382860169093039127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12561587177146892124052169 9421190382860169093039127)
      ·
        refine ⟨14131785574290253639558691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9421190382860169093039127 14131785574290253639558691)
        ·
          refine ⟨21197678361435380459338037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14131785574290253639558691 21197678361435380459338037)
          ·
            refine ⟨1987282346384566918062941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21197678361435380459338037 1987282346384566918062941)
            ·
              refine ⟨745230879894212594273603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1987282346384566918062941 745230879894212594273603)
              ·
                refine ⟨1117846319841318891410405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745230879894212594273603 1117846319841318891410405)
                ·
                  refine ⟨209596184970247292139451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1117846319841318891410405 209596184970247292139451)
                  ·
                    rfl

theorem cell21_918421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_918421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918421 prefixEnd_918421 := by exact prefixLift 918421
  have htrace : WordTrace (prefixWord ++ tailWord_918421) baseStart_918421 baseEnd_918421 := by
    simpa [prefixWord, tailWord_918421, baseEnd_918421] using wordTrace_append hprefix tailTrace_918421
  have hstable : (prefixWord ++ tailWord_918421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918421).length < 2 ^ (prefixWord ++ tailWord_918421).sum := by decide
  have hdescent : baseEnd_918421 < baseStart_918421 := by decide
  rcases family_descends (prefixWord ++ tailWord_918421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918452 : List Nat := [2, 5, 2, 1, 1, 3, 7]
def baseStart_918452 : Nat := 118140960795 + 918452 * 2 ^ 59
def prefixEnd_918452 : Nat := 4983230072969 + 3 ^ 40 * 918452 * 2
def baseEnd_918452 : Nat := 23289251065844236346969

theorem tailTrace_918452 : CollatzResearch.WordTrace tailWord_918452 prefixEnd_918452 23289251065844236346969 := by
  unfold tailWord_918452
  simp only [CollatzResearch.WordTrace]
  refine ⟨16749348234306368979258805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22332464312408491972345073 16749348234306368979258805)
  ·
    refine ⟨1570251396966222091805513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16749348234306368979258805 1570251396966222091805513)
    ·
      refine ⟨1177688547724666568854135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1570251396966222091805513 1177688547724666568854135)
      ·
        refine ⟨1766532821586999853281203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177688547724666568854135 1766532821586999853281203)
        ·
          refine ⟨2649799232380499779921805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766532821586999853281203 2649799232380499779921805)
          ·
            refine ⟨993674712142687417470677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2649799232380499779921805 993674712142687417470677)
            ·
              refine ⟨23289251065844236346969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 993674712142687417470677 23289251065844236346969)
              ·
                rfl

theorem cell21_918452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 7].length) (baseStart_918452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918452 prefixEnd_918452 := by exact prefixLift 918452
  have htrace : WordTrace (prefixWord ++ tailWord_918452) baseStart_918452 baseEnd_918452 := by
    simpa [prefixWord, tailWord_918452, baseEnd_918452] using wordTrace_append hprefix tailTrace_918452
  have hstable : (prefixWord ++ tailWord_918452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918452).length < 2 ^ (prefixWord ++ tailWord_918452).sum := by decide
  have hdescent : baseEnd_918452 < baseStart_918452 := by decide
  rcases family_descends (prefixWord ++ tailWord_918452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918514 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_918514 : Nat := 118140960795 + 918514 * 2 ^ 59
def prefixEnd_918514 : Nat := 4983230072969 + 3 ^ 40 * 918514 * 2
def baseEnd_918514 : Nat := 209617408837299797089261

theorem tailTrace_918514 : CollatzResearch.WordTrace tailWord_918514 prefixEnd_918514 209617408837299797089261 := by
  unfold tailWord_918514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8375239448597030636818649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22333971862925415031516397 8375239448597030636818649)
  ·
    refine ⟨6281429586447772977613987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8375239448597030636818649 6281429586447772977613987)
    ·
      refine ⟨9422144379671659466420981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6281429586447772977613987 9422144379671659466420981)
      ·
        refine ⟨883326035594218074976967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9422144379671659466420981 883326035594218074976967)
        ·
          refine ⟨1324989053391327112465451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883326035594218074976967 1324989053391327112465451)
          ·
            refine ⟨1987483580086990668698177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324989053391327112465451 1987483580086990668698177)
            ·
              refine ⟨1490612685065243001523633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1987483580086990668698177 1490612685065243001523633)
              ·
                refine ⟨1117959513798932251142725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490612685065243001523633 1117959513798932251142725)
                ·
                  refine ⟨209617408837299797089261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1117959513798932251142725 209617408837299797089261)
                  ·
                    rfl

theorem cell21_918514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_918514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918514 prefixEnd_918514 := by exact prefixLift 918514
  have htrace : WordTrace (prefixWord ++ tailWord_918514) baseStart_918514 baseEnd_918514 := by
    simpa [prefixWord, tailWord_918514, baseEnd_918514] using wordTrace_append hprefix tailTrace_918514
  have hstable : (prefixWord ++ tailWord_918514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918514).length < 2 ^ (prefixWord ++ tailWord_918514).sum := by decide
  have hdescent : baseEnd_918514 < baseStart_918514 := by decide
  rcases family_descends (prefixWord ++ tailWord_918514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918553 : List Nat := [1, 2, 1, 2, 1, 1, 4, 9]
def baseStart_918553 : Nat := 118140960795 + 918553 * 2 ^ 59
def prefixEnd_918553 : Nat := 4983230072969 + 3 ^ 40 * 918553 * 2
def baseEnd_918553 : Nat := 69875436389548131979727

theorem tailTrace_918553 : CollatzResearch.WordTrace tailWord_918553 prefixEnd_918553 69875436389548131979727 := by
  unfold tailWord_918553
  simp only [CollatzResearch.WordTrace]
  refine ⟨33502380241246832207944313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22334920160831221471962875 33502380241246832207944313)
  ·
    refine ⟨25126785180935124155958235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33502380241246832207944313 25126785180935124155958235)
    ·
      refine ⟨37690177771402686233937353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25126785180935124155958235 37690177771402686233937353)
      ·
        refine ⟨28267633328552014675453015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37690177771402686233937353 28267633328552014675453015)
        ·
          refine ⟨42401449992828022013179523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28267633328552014675453015 42401449992828022013179523)
          ·
            refine ⟨63602174989242033019769285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42401449992828022013179523 63602174989242033019769285)
            ·
              refine ⟨11925407810482881191206741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63602174989242033019769285 11925407810482881191206741)
              ·
                refine ⟨69875436389548131979727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11925407810482881191206741 69875436389548131979727)
                ·
                  rfl

theorem cell21_918553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 9].length) (baseStart_918553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918553 prefixEnd_918553 := by exact prefixLift 918553
  have htrace : WordTrace (prefixWord ++ tailWord_918553) baseStart_918553 baseEnd_918553 := by
    simpa [prefixWord, tailWord_918553, baseEnd_918553] using wordTrace_append hprefix tailTrace_918553
  have hstable : (prefixWord ++ tailWord_918553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918553).length < 2 ^ (prefixWord ++ tailWord_918553).sum := by decide
  have hdescent : baseEnd_918553 < baseStart_918553 := by decide
  rcases family_descends (prefixWord ++ tailWord_918553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918590 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_918590 : Nat := 118140960795 + 918590 * 2 ^ 59
def prefixEnd_918590 : Nat := 4983230072969 + 3 ^ 40 * 918590 * 2
def baseEnd_918590 : Nat := 209634753072740553822439

theorem tailTrace_918590 : CollatzResearch.WordTrace tailWord_918590 prefixEnd_918590 209634753072740553822439 := by
  unfold tailWord_918590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4187966217764098440880153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22335819828075191684694149 4187966217764098440880153)
  ·
    refine ⟨3140974663323073830660115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4187966217764098440880153 3140974663323073830660115)
    ·
      refine ⟨4711461994984610745990173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3140974663323073830660115 4711461994984610745990173)
      ·
        refine ⟨1766798248119229029746315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4711461994984610745990173 1766798248119229029746315)
        ·
          refine ⟨2650197372178843544619473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766798248119229029746315 2650197372178843544619473)
          ·
            refine ⟨1987648029134132658464605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2650197372178843544619473 1987648029134132658464605)
            ·
              refine ⟨745368010925299746924227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1987648029134132658464605 745368010925299746924227)
              ·
                refine ⟨1118052016387949620386341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745368010925299746924227 1118052016387949620386341)
                ·
                  refine ⟨209634753072740553822439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1118052016387949620386341 209634753072740553822439)
                  ·
                    rfl

theorem cell21_918590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_918590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918590 prefixEnd_918590 := by exact prefixLift 918590
  have htrace : WordTrace (prefixWord ++ tailWord_918590) baseStart_918590 baseEnd_918590 := by
    simpa [prefixWord, tailWord_918590, baseEnd_918590] using wordTrace_append hprefix tailTrace_918590
  have hstable : (prefixWord ++ tailWord_918590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918590).length < 2 ^ (prefixWord ++ tailWord_918590).sum := by decide
  have hdescent : baseEnd_918590 < baseStart_918590 := by decide
  rcases family_descends (prefixWord ++ tailWord_918590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918753 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 5]
def baseStart_918753 : Nat := 118140960795 + 918753 * 2 ^ 59
def prefixEnd_918753 : Nat := 4983230072969 + 3 ^ 40 * 918753 * 2
def baseEnd_918753 : Nat := 209671951893488492605439

theorem tailTrace_918753 : CollatzResearch.WordTrace tailWord_918753 prefixEnd_918753 209671951893488492605439 := by
  unfold tailWord_918753
  simp only [CollatzResearch.WordTrace]
  refine ⟨33509674840522266365224913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22339783227014844243483275 33509674840522266365224913)
  ·
    refine ⟨25132256130391699773918685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33509674840522266365224913 25132256130391699773918685)
    ·
      refine ⟨9424596048896887415219507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25132256130391699773918685 9424596048896887415219507)
      ·
        refine ⟨14136894073345331122829261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9424596048896887415219507 14136894073345331122829261)
        ·
          refine ⟨5301335277504499171060973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14136894073345331122829261 5301335277504499171060973)
          ·
            refine ⟨1988000729064187189147865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5301335277504499171060973 1988000729064187189147865)
            ·
              refine ⟨1491000546798140391860899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988000729064187189147865 1491000546798140391860899)
              ·
                refine ⟨2236500820197210587791349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491000546798140391860899 2236500820197210587791349)
                ·
                  refine ⟨209671951893488492605439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2236500820197210587791349 209671951893488492605439)
                  ·
                    rfl

theorem cell21_918753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_918753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918753 prefixEnd_918753 := by exact prefixLift 918753
  have htrace : WordTrace (prefixWord ++ tailWord_918753) baseStart_918753 baseEnd_918753 := by
    simpa [prefixWord, tailWord_918753, baseEnd_918753] using wordTrace_append hprefix tailTrace_918753
  have hstable : (prefixWord ++ tailWord_918753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918753).length < 2 ^ (prefixWord ++ tailWord_918753).sum := by decide
  have hdescent : baseEnd_918753 < baseStart_918753 := by decide
  rcases family_descends (prefixWord ++ tailWord_918753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918798 : List Nat := [4, 1, 1, 2, 1, 5, 7]
def baseStart_918798 : Nat := 118140960795 + 918798 * 2 ^ 59
def prefixEnd_918798 : Nat := 4983230072969 + 3 ^ 40 * 918798 * 2
def baseEnd_918798 : Nat := 23298024611842046039483

theorem tailTrace_918798 : CollatzResearch.WordTrace tailWord_918798 prefixEnd_918798 23298024611842046039483 := by
  unfold tailWord_918798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4188914515669904881326631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22340877416906159367075365 4188914515669904881326631)
  ·
    refine ⟨6283371773504857321989947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4188914515669904881326631 6283371773504857321989947)
    ·
      refine ⟨9425057660257285982984921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6283371773504857321989947 9425057660257285982984921)
      ·
        refine ⟨7068793245192964487238691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9425057660257285982984921 7068793245192964487238691)
        ·
          refine ⟨10603189867789446730858037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7068793245192964487238691 10603189867789446730858037)
          ·
            refine ⟨994049050105260631017941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10603189867789446730858037 994049050105260631017941)
            ·
              refine ⟨23298024611842046039483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 994049050105260631017941 23298024611842046039483)
              ·
                rfl

theorem cell21_918798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 7].length) (baseStart_918798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918798 prefixEnd_918798 := by exact prefixLift 918798
  have htrace : WordTrace (prefixWord ++ tailWord_918798) baseStart_918798 baseEnd_918798 := by
    simpa [prefixWord, tailWord_918798, baseEnd_918798] using wordTrace_append hprefix tailTrace_918798
  have hstable : (prefixWord ++ tailWord_918798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918798).length < 2 ^ (prefixWord ++ tailWord_918798).sum := by decide
  have hdescent : baseEnd_918798 < baseStart_918798 := by decide
  rcases family_descends (prefixWord ++ tailWord_918798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918818 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_918818 : Nat := 118140960795 + 918818 * 2 ^ 59
def prefixEnd_918818 : Nat := 4983230072969 + 3 ^ 40 * 918818 * 2
def baseEnd_918818 : Nat := 209686785779062824021973

theorem tailTrace_918818 : CollatzResearch.WordTrace tailWord_918818 prefixEnd_918818 209686785779062824021973 := by
  unfold tailWord_918818
  simp only [CollatzResearch.WordTrace]
  refine ⟨8378011396321695616585277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22341363723524521644227405 8378011396321695616585277)
  ·
    refine ⟨3141754273620635856219479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8378011396321695616585277 3141754273620635856219479)
    ·
      refine ⟨4712631410430953784329219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3141754273620635856219479 4712631410430953784329219)
      ·
        refine ⟨7068947115646430676493829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4712631410430953784329219 7068947115646430676493829)
        ·
          refine ⟨1325427584183705751842593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7068947115646430676493829 1325427584183705751842593)
          ·
            refine ⟨994070688137779313881945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325427584183705751842593 994070688137779313881945)
            ·
              refine ⟨745553016103334485411459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994070688137779313881945 745553016103334485411459)
              ·
                refine ⟨1118329524155001728117189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745553016103334485411459 1118329524155001728117189)
                ·
                  refine ⟨209686785779062824021973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1118329524155001728117189 209686785779062824021973)
                  ·
                    rfl

theorem cell21_918818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_918818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918818 prefixEnd_918818 := by exact prefixLift 918818
  have htrace : WordTrace (prefixWord ++ tailWord_918818) baseStart_918818 baseEnd_918818 := by
    simpa [prefixWord, tailWord_918818, baseEnd_918818] using wordTrace_append hprefix tailTrace_918818
  have hstable : (prefixWord ++ tailWord_918818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918818).length < 2 ^ (prefixWord ++ tailWord_918818).sum := by decide
  have hdescent : baseEnd_918818 < baseStart_918818 := by decide
  rcases family_descends (prefixWord ++ tailWord_918818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918846 : List Nat := [4, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_918846 : Nat := 118140960795 + 918846 * 2 ^ 59
def prefixEnd_918846 : Nat := 4983230072969 + 3 ^ 40 * 918846 * 2
def baseEnd_918846 : Nat := 209693175760540997555249

theorem tailTrace_918846 : CollatzResearch.WordTrace tailWord_918846 prefixEnd_918846 209693175760540997555249 := by
  unfold tailWord_918846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4189133353648167906045049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22342044552790228832240261 4189133353648167906045049)
  ·
    refine ⟨3141850015236125929533787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4189133353648167906045049 3141850015236125929533787)
    ·
      refine ⟨4712775022854188894300681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3141850015236125929533787 4712775022854188894300681)
      ·
        refine ⟨3534581267140641670725511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4712775022854188894300681 3534581267140641670725511)
        ·
          refine ⟨5301871900710962506088267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3534581267140641670725511 5301871900710962506088267)
          ·
            refine ⟨7952807851066443759132401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301871900710962506088267 7952807851066443759132401)
            ·
              refine ⟨5964605888299832819349301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7952807851066443759132401 5964605888299832819349301)
              ·
                refine ⟨559181802028109326813997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5964605888299832819349301 559181802028109326813997)
                ·
                  refine ⟨209693175760540997555249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559181802028109326813997 209693175760540997555249)
                  ·
                    rfl

theorem cell21_918846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_918846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918846 prefixEnd_918846 := by exact prefixLift 918846
  have htrace : WordTrace (prefixWord ++ tailWord_918846) baseStart_918846 baseEnd_918846 := by
    simpa [prefixWord, tailWord_918846, baseEnd_918846] using wordTrace_append hprefix tailTrace_918846
  have hstable : (prefixWord ++ tailWord_918846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918846).length < 2 ^ (prefixWord ++ tailWord_918846).sum := by decide
  have hdescent : baseEnd_918846 < baseStart_918846 := by decide
  rcases family_descends (prefixWord ++ tailWord_918846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918860 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 4]
def baseStart_918860 : Nat := 118140960795 + 918860 * 2 ^ 59
def prefixEnd_918860 : Nat := 4983230072969 + 3 ^ 40 * 918860 * 2
def baseEnd_918860 : Nat := 209696370751280084321887

theorem tailTrace_918860 : CollatzResearch.WordTrace tailWord_918860 prefixEnd_918860 209696370751280084321887 := by
  unfold tailWord_918860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16756788725567311819685017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22342384967423082426246689 16756788725567311819685017)
  ·
    refine ⟨12567591544175483864763763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16756788725567311819685017 12567591544175483864763763)
    ·
      refine ⟨18851387316263225797145645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12567591544175483864763763 18851387316263225797145645)
      ·
        refine ⟨7069270243598709673929617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18851387316263225797145645 7069270243598709673929617)
        ·
          refine ⟨5301952682699032255447213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7069270243598709673929617 5301952682699032255447213)
          ·
            refine ⟨1988232256012137095792705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5301952682699032255447213 1988232256012137095792705)
            ·
              refine ⟨1491174192009102821844529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988232256012137095792705 1491174192009102821844529)
              ·
                refine ⟨1118380644006827116383397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491174192009102821844529 1118380644006827116383397)
                ·
                  refine ⟨209696370751280084321887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1118380644006827116383397 209696370751280084321887)
                  ·
                    rfl

theorem cell21_918860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_918860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918860 prefixEnd_918860 := by exact prefixLift 918860
  have htrace : WordTrace (prefixWord ++ tailWord_918860) baseStart_918860 baseEnd_918860 := by
    simpa [prefixWord, tailWord_918860, baseEnd_918860] using wordTrace_append hprefix tailTrace_918860
  have hstable : (prefixWord ++ tailWord_918860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918860).length < 2 ^ (prefixWord ++ tailWord_918860).sum := by decide
  have hdescent : baseEnd_918860 < baseStart_918860 := by decide
  rcases family_descends (prefixWord ++ tailWord_918860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918905 : List Nat := [1, 2, 1, 3, 2, 1, 3, 5, 3]
def baseStart_918905 : Nat := 118140960795 + 918905 * 2 ^ 59
def prefixEnd_918905 : Nat := 4983230072969 + 3 ^ 40 * 918905 * 2
def baseEnd_918905 : Nat := 209706640364370006071795

theorem tailTrace_918905 : CollatzResearch.WordTrace tailWord_918905 prefixEnd_918905 209706640364370006071795 := by
  unfold tailWord_918905
  simp only [CollatzResearch.WordTrace]
  refine ⟨33515218735971596324758169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22343479157314397549838779 33515218735971596324758169)
  ·
    refine ⟨25136414051978697243568627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33515218735971596324758169 25136414051978697243568627)
    ·
      refine ⟨37704621077968045865352941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25136414051978697243568627 37704621077968045865352941)
      ·
        refine ⟨14139232904238017199507353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37704621077968045865352941 14139232904238017199507353)
        ·
          refine ⟨10604424678178512899630515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14139232904238017199507353 10604424678178512899630515)
          ·
            refine ⟨15906637017267769349445773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10604424678178512899630515 15906637017267769349445773)
            ·
              refine ⟨5964988881475413506042165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15906637017267769349445773 5964988881475413506042165)
              ·
                refine ⟨559217707638320016191453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5964988881475413506042165 559217707638320016191453)
                ·
                  refine ⟨209706640364370006071795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559217707638320016191453 209706640364370006071795)
                  ·
                    rfl

theorem cell21_918905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 3].length) (baseStart_918905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918905 prefixEnd_918905 := by exact prefixLift 918905
  have htrace : WordTrace (prefixWord ++ tailWord_918905) baseStart_918905 baseEnd_918905 := by
    simpa [prefixWord, tailWord_918905, baseEnd_918905] using wordTrace_append hprefix tailTrace_918905
  have hstable : (prefixWord ++ tailWord_918905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918905).length < 2 ^ (prefixWord ++ tailWord_918905).sum := by decide
  have hdescent : baseEnd_918905 < baseStart_918905 := by decide
  rcases family_descends (prefixWord ++ tailWord_918905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918919 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 6]
def baseStart_918919 : Nat := 118140960795 + 918919 * 2 ^ 59
def prefixEnd_918919 : Nat := 4983230072969 + 3 ^ 40 * 918919 * 2
def baseEnd_918919 : Nat := 209709835355109092838433

theorem tailTrace_918919 : CollatzResearch.WordTrace tailWord_918919 prefixEnd_918919 209709835355109092838433 := by
  unfold tailWord_918919
  simp only [CollatzResearch.WordTrace]
  refine ⟨33515729357920876715767811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22343819571947251143845207 33515729357920876715767811)
  ·
    refine ⟨50273594036881315073651717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33515729357920876715767811 50273594036881315073651717)
    ·
      refine ⟨9426298881915246576309697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50273594036881315073651717 9426298881915246576309697)
      ·
        refine ⟨7069724161436434932232273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9426298881915246576309697 7069724161436434932232273)
        ·
          refine ⟨5302293121077326199174205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7069724161436434932232273 5302293121077326199174205)
          ·
            refine ⟨1988359920403997324690327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5302293121077326199174205 1988359920403997324690327)
            ·
              refine ⟨2982539880605995987035491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988359920403997324690327 2982539880605995987035491)
              ·
                refine ⟨4473809820908993980553237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2982539880605995987035491 4473809820908993980553237)
                ·
                  refine ⟨209709835355109092838433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4473809820908993980553237 209709835355109092838433)
                  ·
                    rfl

theorem cell21_918919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 6].length) (baseStart_918919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_918919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_918919 prefixEnd_918919 := by exact prefixLift 918919
  have htrace : WordTrace (prefixWord ++ tailWord_918919) baseStart_918919 baseEnd_918919 := by
    simpa [prefixWord, tailWord_918919, baseEnd_918919] using wordTrace_append hprefix tailTrace_918919
  have hstable : (prefixWord ++ tailWord_918919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918919).length < 2 ^ (prefixWord ++ tailWord_918919).sum := by decide
  have hdescent : baseEnd_918919 < baseStart_918919 := by decide
  rcases family_descends (prefixWord ++ tailWord_918919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919009 : List Nat := [1, 2, 3, 1, 2, 3, 2, 7]
def baseStart_919009 : Nat := 118140960795 + 919009 * 2 ^ 59
def prefixEnd_919009 : Nat := 4983230072969 + 3 ^ 40 * 919009 * 2
def baseEnd_919009 : Nat := 69910124860429645446083

theorem tailTrace_919009 : CollatzResearch.WordTrace tailWord_919009 prefixEnd_919009 69910124860429645446083 := by
  unfold tailWord_919009
  simp only [CollatzResearch.WordTrace]
  refine ⟨33519011927594822086544081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22346007951729881391029387 33519011927594822086544081)
  ·
    refine ⟨25139258945696116564908061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33519011927594822086544081 25139258945696116564908061)
    ·
      refine ⟨9427222104636043711840523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25139258945696116564908061 9427222104636043711840523)
      ·
        refine ⟨14140833156954065567760785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9427222104636043711840523 14140833156954065567760785)
        ·
          refine ⟨10605624867715549175820589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14140833156954065567760785 10605624867715549175820589)
          ·
            refine ⟨3977109325393330940932721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10605624867715549175820589 3977109325393330940932721)
            ·
              refine ⟨2982831994044998205699541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977109325393330940932721 2982831994044998205699541)
              ·
                refine ⟨69910124860429645446083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2982831994044998205699541 69910124860429645446083)
                ·
                  rfl

theorem cell21_919009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 7].length) (baseStart_919009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919009 prefixEnd_919009 := by exact prefixLift 919009
  have htrace : WordTrace (prefixWord ++ tailWord_919009) baseStart_919009 baseEnd_919009 := by
    simpa [prefixWord, tailWord_919009, baseEnd_919009] using wordTrace_append hprefix tailTrace_919009
  have hstable : (prefixWord ++ tailWord_919009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919009).length < 2 ^ (prefixWord ++ tailWord_919009).sum := by decide
  have hdescent : baseEnd_919009 < baseStart_919009 := by decide
  rcases family_descends (prefixWord ++ tailWord_919009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919029 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 4]
def baseStart_919029 : Nat := 118140960795 + 919029 * 2 ^ 59
def prefixEnd_919029 : Nat := 4983230072969 + 3 ^ 40 * 919029 * 2
def baseEnd_919029 : Nat := 209734938853773346004875

theorem tailTrace_919029 : CollatzResearch.WordTrace tailWord_919029 prefixEnd_919029 209734938853773346004875 := by
  unfold tailWord_919029
  simp only [CollatzResearch.WordTrace]
  refine ⟨33519741387522365502272141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22346494258348243668181427 33519741387522365502272141)
  ·
    refine ⟨12569903020320887063352053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33519741387522365502272141 12569903020320887063352053)
    ·
      refine ⟨1178428408155083162189255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12569903020320887063352053 1178428408155083162189255)
      ·
        refine ⟨1767642612232624743283883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178428408155083162189255 1767642612232624743283883)
        ·
          refine ⟨2651463918348937114925825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767642612232624743283883 2651463918348937114925825)
          ·
            refine ⟨1988597938761702836194369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2651463918348937114925825 1988597938761702836194369)
            ·
              refine ⟨1491448454071277127145777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988597938761702836194369 1491448454071277127145777)
              ·
                refine ⟨1118586340553457845359333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491448454071277127145777 1118586340553457845359333)
                ·
                  refine ⟨209734938853773346004875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1118586340553457845359333 209734938853773346004875)
                  ·
                    rfl

theorem cell21_919029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_919029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919029 prefixEnd_919029 := by exact prefixLift 919029
  have htrace : WordTrace (prefixWord ++ tailWord_919029) baseStart_919029 baseEnd_919029 := by
    simpa [prefixWord, tailWord_919029, baseEnd_919029] using wordTrace_append hprefix tailTrace_919029
  have hstable : (prefixWord ++ tailWord_919029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919029).length < 2 ^ (prefixWord ++ tailWord_919029).sum := by decide
  have hdescent : baseEnd_919029 < baseStart_919029 := by decide
  rcases family_descends (prefixWord ++ tailWord_919029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919060 : List Nat := [2, 4, 3, 1, 2, 1, 3, 5]
def baseStart_919060 : Nat := 118140960795 + 919060 * 2 ^ 59
def prefixEnd_919060 : Nat := 4983230072969 + 3 ^ 40 * 919060 * 2
def baseEnd_919060 : Nat := 69914004492041393662715

theorem tailTrace_919060 : CollatzResearch.WordTrace tailWord_919060 prefixEnd_919060 69914004492041393662715 := by
  unfold tailWord_919060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16760436025205028898325317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22347248033606705197767089 16760436025205028898325317)
  ·
    refine ⟨3142581754725942918435997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16760436025205028898325317 3142581754725942918435997)
    ·
      refine ⟨1178468158022228594413499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3142581754725942918435997 1178468158022228594413499)
      ·
        refine ⟨1767702237033342891620249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178468158022228594413499 1767702237033342891620249)
        ·
          refine ⟨1325776677775007168715187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1767702237033342891620249 1325776677775007168715187)
          ·
            refine ⟨1988665016662510753072781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325776677775007168715187 1988665016662510753072781)
            ·
              refine ⟨745749381248441532402293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1988665016662510753072781 745749381248441532402293)
              ·
                refine ⟨69914004492041393662715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 745749381248441532402293 69914004492041393662715)
                ·
                  rfl

theorem cell21_919060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_919060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919060 prefixEnd_919060 := by exact prefixLift 919060
  have htrace : WordTrace (prefixWord ++ tailWord_919060) baseStart_919060 baseEnd_919060 := by
    simpa [prefixWord, tailWord_919060, baseEnd_919060] using wordTrace_append hprefix tailTrace_919060
  have hstable : (prefixWord ++ tailWord_919060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919060).length < 2 ^ (prefixWord ++ tailWord_919060).sum := by decide
  have hdescent : baseEnd_919060 < baseStart_919060 := by decide
  rcases family_descends (prefixWord ++ tailWord_919060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919116 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_919116 : Nat := 118140960795 + 919116 * 2 ^ 59
def prefixEnd_919116 : Nat := 4983230072969 + 3 ^ 40 * 919116 * 2
def baseEnd_919116 : Nat := 209754793439080528054697

theorem tailTrace_919116 : CollatzResearch.WordTrace tailWord_919116 prefixEnd_919116 209754793439080528054697 := by
  unfold tailWord_919116
  simp only [CollatzResearch.WordTrace]
  refine ⟨16761457269103589680344601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22348609692138119573792801 16761457269103589680344601)
  ·
    refine ⟨12571092951827692260258451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16761457269103589680344601 12571092951827692260258451)
    ·
      refine ⟨18856639427741538390387677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12571092951827692260258451 18856639427741538390387677)
      ·
        refine ⟨7071239785403076896395379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18856639427741538390387677 7071239785403076896395379)
        ·
          refine ⟨10606859678104615344593069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7071239785403076896395379 10606859678104615344593069)
          ·
            refine ⟨3977572379289230754222401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10606859678104615344593069 3977572379289230754222401)
            ·
              refine ⟨2983179284466923065666801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977572379289230754222401 2983179284466923065666801)
              ·
                refine ⟨2237384463350192299250101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2983179284466923065666801 2237384463350192299250101)
                ·
                  refine ⟨209754793439080528054697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2237384463350192299250101 209754793439080528054697)
                  ·
                    rfl

theorem cell21_919116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_919116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919116 prefixEnd_919116 := by exact prefixLift 919116
  have htrace : WordTrace (prefixWord ++ tailWord_919116) baseStart_919116 baseEnd_919116 := by
    simpa [prefixWord, tailWord_919116, baseEnd_919116] using wordTrace_append hprefix tailTrace_919116
  have hstable : (prefixWord ++ tailWord_919116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919116).length < 2 ^ (prefixWord ++ tailWord_919116).sum := by decide
  have hdescent : baseEnd_919116 < baseStart_919116 := by decide
  rcases family_descends (prefixWord ++ tailWord_919116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919150 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_919150 : Nat := 118140960795 + 919150 * 2 ^ 59
def prefixEnd_919150 : Nat := 4983230072969 + 3 ^ 40 * 919150 * 2
def baseEnd_919150 : Nat := 209762552702304024487961

theorem tailTrace_919150 : CollatzResearch.WordTrace tailWord_919150 prefixEnd_919150 209762552702304024487961 := by
  unfold tailWord_919150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4190519327510500395928363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22349436413389335444951269 4190519327510500395928363)
  ·
    refine ⟨6285778991265750593892545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4190519327510500395928363 6285778991265750593892545)
    ·
      refine ⟨4714334243449312945419409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6285778991265750593892545 4714334243449312945419409)
      ·
        refine ⟨3535750682586984709064557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4714334243449312945419409 3535750682586984709064557)
        ·
          refine ⟨1325906505970119265899209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3535750682586984709064557 1325906505970119265899209)
          ·
            refine ⟨994429879477589449424407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325906505970119265899209 994429879477589449424407)
            ·
              refine ⟨1491644819216384174136611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994429879477589449424407 1491644819216384174136611)
              ·
                refine ⟨2237467228824576261204917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491644819216384174136611 2237467228824576261204917)
                ·
                  refine ⟨209762552702304024487961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2237467228824576261204917 209762552702304024487961)
                  ·
                    rfl

theorem cell21_919150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_919150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919150 prefixEnd_919150 := by exact prefixLift 919150
  have htrace : WordTrace (prefixWord ++ tailWord_919150) baseStart_919150 baseEnd_919150 := by
    simpa [prefixWord, tailWord_919150, baseEnd_919150] using wordTrace_append hprefix tailTrace_919150
  have hstable : (prefixWord ++ tailWord_919150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919150).length < 2 ^ (prefixWord ++ tailWord_919150).sum := by decide
  have hdescent : baseEnd_919150 < baseStart_919150 := by decide
  rcases family_descends (prefixWord ++ tailWord_919150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919161 : List Nat := [1, 2, 1, 3, 3, 1, 4, 6]
def baseStart_919161 : Nat := 118140960795 + 919161 * 2 ^ 59
def prefixEnd_919161 : Nat := 4983230072969 + 3 ^ 40 * 919161 * 2
def baseEnd_919161 : Nat := 69921687684056816601535

theorem tailTrace_919161 : CollatzResearch.WordTrace tailWord_919161 prefixEnd_919161 69921687684056816601535 := by
  unfold tailWord_919161
  simp only [CollatzResearch.WordTrace]
  refine ⟨33524555823044152046077337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22349703882029434697384891 33524555823044152046077337)
  ·
    refine ⟨25143416867283114034558003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33524555823044152046077337 25143416867283114034558003)
    ·
      refine ⟨37715125300924671051837005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25143416867283114034558003 37715125300924671051837005)
      ·
        refine ⟨14143171987846751644438877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37715125300924671051837005 14143171987846751644438877)
        ·
          refine ⟨5303689495442531866664579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14143171987846751644438877 5303689495442531866664579)
          ·
            refine ⟨7955534243163797799996869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303689495442531866664579 7955534243163797799996869)
            ·
              refine ⟨1491662670593212087499413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7955534243163797799996869 1491662670593212087499413)
              ·
                refine ⟨69921687684056816601535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1491662670593212087499413 69921687684056816601535)
                ·
                  rfl

theorem cell21_919161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 6].length) (baseStart_919161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919161 prefixEnd_919161 := by exact prefixLift 919161
  have htrace : WordTrace (prefixWord ++ tailWord_919161) baseStart_919161 baseEnd_919161 := by
    simpa [prefixWord, tailWord_919161, baseEnd_919161] using wordTrace_append hprefix tailTrace_919161
  have hstable : (prefixWord ++ tailWord_919161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919161).length < 2 ^ (prefixWord ++ tailWord_919161).sum := by decide
  have hdescent : baseEnd_919161 < baseStart_919161 := by decide
  rcases family_descends (prefixWord ++ tailWord_919161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919223 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 4]
def baseStart_919223 : Nat := 118140960795 + 919223 * 2 ^ 59
def prefixEnd_919223 : Nat := 4983230072969 + 3 ^ 40 * 919223 * 2
def baseEnd_919223 : Nat := 209779212296872119771145

theorem tailTrace_919223 : CollatzResearch.WordTrace tailWord_919223 prefixEnd_919223 209779212296872119771145 := by
  unfold tailWord_919223
  simp only [CollatzResearch.WordTrace]
  refine ⟨33526817148819536634834323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22351211432546357756556215 33526817148819536634834323)
  ·
    refine ⟨50290225723229304952251485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33526817148819536634834323 50290225723229304952251485)
    ·
      refine ⟨18858834646210989357094307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50290225723229304952251485 18858834646210989357094307)
      ·
        refine ⟨28288251969316484035641461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18858834646210989357094307 28288251969316484035641461)
        ·
          refine ⟨2652023622123420378341387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28288251969316484035641461 2652023622123420378341387)
          ·
            refine ⟨3978035433185130567512081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652023622123420378341387 3978035433185130567512081)
            ·
              refine ⟨2983526574888847925634061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3978035433185130567512081 2983526574888847925634061)
              ·
                refine ⟨1118822465583317972112773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2983526574888847925634061 1118822465583317972112773)
                ·
                  refine ⟨209779212296872119771145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1118822465583317972112773 209779212296872119771145)
                  ·
                    rfl

theorem cell21_919223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 4].length) (baseStart_919223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919223 prefixEnd_919223 := by exact prefixLift 919223
  have htrace : WordTrace (prefixWord ++ tailWord_919223) baseStart_919223 baseEnd_919223 := by
    simpa [prefixWord, tailWord_919223, baseEnd_919223] using wordTrace_append hprefix tailTrace_919223
  have hstable : (prefixWord ++ tailWord_919223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919223).length < 2 ^ (prefixWord ++ tailWord_919223).sum := by decide
  have hdescent : baseEnd_919223 < baseStart_919223 := by decide
  rcases family_descends (prefixWord ++ tailWord_919223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919268 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 5]
def baseStart_919268 : Nat := 118140960795 + 919268 * 2 ^ 59
def prefixEnd_919268 : Nat := 4983230072969 + 3 ^ 40 * 919268 * 2
def baseEnd_919268 : Nat := 209789481909962041521053

theorem tailTrace_919268 : CollatzResearch.WordTrace tailWord_919268 prefixEnd_919268 209789481909962041521053 := by
  unfold tailWord_919268
  simp only [CollatzResearch.WordTrace]
  refine ⟨16764229216828254660111229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22352305622437672880148305 16764229216828254660111229)
  ·
    refine ⟨6286585956310595497541711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16764229216828254660111229 6286585956310595497541711)
    ·
      refine ⟨9429878934465893246312567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6286585956310595497541711 9429878934465893246312567)
      ·
        refine ⟨14144818401698839869468851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9429878934465893246312567 14144818401698839869468851)
        ·
          refine ⟨21217227602548259804203277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14144818401698839869468851 21217227602548259804203277)
          ·
            refine ⟨7956460350955597426576229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21217227602548259804203277 7956460350955597426576229)
            ·
              refine ⟨1491836315804174517483043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7956460350955597426576229 1491836315804174517483043)
              ·
                refine ⟨2237754473706261776224565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491836315804174517483043 2237754473706261776224565)
                ·
                  refine ⟨209789481909962041521053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2237754473706261776224565 209789481909962041521053)
                  ·
                    rfl

theorem cell21_919268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_919268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919268 prefixEnd_919268 := by exact prefixLift 919268
  have htrace : WordTrace (prefixWord ++ tailWord_919268) baseStart_919268 baseEnd_919268 := by
    simpa [prefixWord, tailWord_919268, baseEnd_919268] using wordTrace_append hprefix tailTrace_919268
  have hstable : (prefixWord ++ tailWord_919268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919268).length < 2 ^ (prefixWord ++ tailWord_919268).sum := by decide
  have hdescent : baseEnd_919268 < baseStart_919268 := by decide
  rcases family_descends (prefixWord ++ tailWord_919268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919296 : List Nat := [2, 1, 1, 2, 1, 1, 2, 11]
def baseStart_919296 : Nat := 118140960795 + 919296 * 2 ^ 59
def prefixEnd_919296 : Nat := 4983230072969 + 3 ^ 40 * 919296 * 2
def baseEnd_919296 : Nat := 69931957297146738351443

theorem tailTrace_919296 : CollatzResearch.WordTrace tailWord_919296 prefixEnd_919296 69931957297146738351443 := by
  unfold tailWord_919296
  simp only [CollatzResearch.WordTrace]
  refine ⟨16764739838777535051120871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22352986451703380068161161 16764739838777535051120871)
  ·
    refine ⟨25147109758166302576681307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16764739838777535051120871 25147109758166302576681307)
    ·
      refine ⟨37720664637249453865021961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25147109758166302576681307 37720664637249453865021961)
      ·
        refine ⟨28290498477937090398766471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37720664637249453865021961 28290498477937090398766471)
        ·
          refine ⟨42435747716905635598149707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28290498477937090398766471 42435747716905635598149707)
          ·
            refine ⟨63653621575358453397224561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42435747716905635598149707 63653621575358453397224561)
            ·
              refine ⟨47740216181518840047918421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63653621575358453397224561 47740216181518840047918421)
              ·
                refine ⟨69931957297146738351443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 47740216181518840047918421 69931957297146738351443)
                ·
                  rfl

theorem cell21_919296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_919296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919296 prefixEnd_919296 := by exact prefixLift 919296
  have htrace : WordTrace (prefixWord ++ tailWord_919296) baseStart_919296 baseEnd_919296 := by
    simpa [prefixWord, tailWord_919296, baseEnd_919296] using wordTrace_append hprefix tailTrace_919296
  have hstable : (prefixWord ++ tailWord_919296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919296).length < 2 ^ (prefixWord ++ tailWord_919296).sum := by decide
  have hdescent : baseEnd_919296 < baseStart_919296 := by decide
  rcases family_descends (prefixWord ++ tailWord_919296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919372 : List Nat := [2, 2, 1, 3, 13]
def baseStart_919372 : Nat := 118140960795 + 919372 * 2 ^ 59
def prefixEnd_919372 : Nat := 4983230072969 + 3 ^ 40 * 919372 * 2
def baseEnd_919372 : Nat := 2590286618850382367747

theorem tailTrace_919372 : CollatzResearch.WordTrace tailWord_919372 prefixEnd_919372 2590286618850382367747 := by
  unfold tailWord_919372
  simp only [CollatzResearch.WordTrace]
  refine ⟨16766125812639867541004185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22354834416853156721338913 16766125812639867541004185)
  ·
    refine ⟨12574594359479900655753139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16766125812639867541004185 12574594359479900655753139)
    ·
      refine ⟨18861891539219850983629709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12574594359479900655753139 18861891539219850983629709)
      ·
        refine ⟨7073209327207444118861141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18861891539219850983629709 7073209327207444118861141)
        ·
          refine ⟨2590286618850382367747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7073209327207444118861141 2590286618850382367747)
          ·
            rfl

theorem cell21_919372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 13].length) (baseStart_919372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919372 prefixEnd_919372 := by exact prefixLift 919372
  have htrace : WordTrace (prefixWord ++ tailWord_919372) baseStart_919372 baseEnd_919372 := by
    simpa [prefixWord, tailWord_919372, baseEnd_919372] using wordTrace_append hprefix tailTrace_919372
  have hstable : (prefixWord ++ tailWord_919372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919372).length < 2 ^ (prefixWord ++ tailWord_919372).sum := by decide
  have hdescent : baseEnd_919372 < baseStart_919372 := by decide
  rcases family_descends (prefixWord ++ tailWord_919372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919378 : List Nat := [3, 2, 2, 1, 1, 3, 4, 2, 3]
def baseStart_919378 : Nat := 118140960795 + 919378 * 2 ^ 59
def prefixEnd_919378 : Nat := 4983230072969 + 3 ^ 40 * 919378 * 2
def baseEnd_919378 : Nat := 209814585408626294687495

theorem tailTrace_919378 : CollatzResearch.WordTrace tailWord_919378 prefixEnd_919378 209814585408626294687495 := by
  unfold tailWord_919378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8383117615814499526681697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22354980308838665404484525 8383117615814499526681697)
  ·
    refine ⟨6287338211860874645011273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8383117615814499526681697 6287338211860874645011273)
    ·
      refine ⟨4715503658895655983758455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6287338211860874645011273 4715503658895655983758455)
      ·
        refine ⟨7073255488343483975637683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4715503658895655983758455 7073255488343483975637683)
        ·
          refine ⟨10609883232515225963456525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7073255488343483975637683 10609883232515225963456525)
          ·
            refine ⟨3978706212193209736296197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10609883232515225963456525 3978706212193209736296197)
            ·
              refine ⟨746007414786226825555537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3978706212193209736296197 746007414786226825555537)
              ·
                refine ⟨559505561089670119166653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746007414786226825555537 559505561089670119166653)
                ·
                  refine ⟨209814585408626294687495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559505561089670119166653 209814585408626294687495)
                  ·
                    rfl

theorem cell21_919378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_919378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919378 prefixEnd_919378 := by exact prefixLift 919378
  have htrace : WordTrace (prefixWord ++ tailWord_919378) baseStart_919378 baseEnd_919378 := by
    simpa [prefixWord, tailWord_919378, baseEnd_919378] using wordTrace_append hprefix tailTrace_919378
  have hstable : (prefixWord ++ tailWord_919378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919378).length < 2 ^ (prefixWord ++ tailWord_919378).sum := by decide
  have hdescent : baseEnd_919378 < baseStart_919378 := by decide
  rcases family_descends (prefixWord ++ tailWord_919378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919496 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 5]
def baseStart_919496 : Nat := 118140960795 + 919496 * 2 ^ 59
def prefixEnd_919496 : Nat := 4983230072969 + 3 ^ 40 * 919496 * 2
def baseEnd_919496 : Nat := 209841514616284311720587

theorem tailTrace_919496 : CollatzResearch.WordTrace tailWord_919496 prefixEnd_919496 209841514616284311720587 := by
  unfold tailWord_919496
  simp only [CollatzResearch.WordTrace]
  refine ⟨16768387138415252129761171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22357849517887002839681561 16768387138415252129761171)
  ·
    refine ⟨25152580707622878194641757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16768387138415252129761171 25152580707622878194641757)
    ·
      refine ⟨9432217765358579322990659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25152580707622878194641757 9432217765358579322990659)
      ·
        refine ⟨14148326648037868984485989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9432217765358579322990659 14148326648037868984485989)
        ·
          refine ⟨2652811246507100434591123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14148326648037868984485989 2652811246507100434591123)
          ·
            refine ⟨3979216869760650651886685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652811246507100434591123 3979216869760650651886685)
            ·
              refine ⟨1492206326160243994457507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3979216869760650651886685 1492206326160243994457507)
              ·
                refine ⟨2238309489240365991686261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492206326160243994457507 2238309489240365991686261)
                ·
                  refine ⟨209841514616284311720587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2238309489240365991686261 209841514616284311720587)
                  ·
                    rfl

theorem cell21_919496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_919496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919496 prefixEnd_919496 := by exact prefixLift 919496
  have htrace : WordTrace (prefixWord ++ tailWord_919496) baseStart_919496 baseEnd_919496 := by
    simpa [prefixWord, tailWord_919496, baseEnd_919496] using wordTrace_append hprefix tailTrace_919496
  have hstable : (prefixWord ++ tailWord_919496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919496).length < 2 ^ (prefixWord ++ tailWord_919496).sum := by decide
  have hdescent : baseEnd_919496 < baseStart_919496 := by decide
  rcases family_descends (prefixWord ++ tailWord_919496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919524 : List Nat := [2, 3, 1, 1, 1, 1, 3, 9]
def baseStart_919524 : Nat := 118140960795 + 919524 * 2 ^ 59
def prefixEnd_919524 : Nat := 4983230072969 + 3 ^ 40 * 919524 * 2
def baseEnd_919524 : Nat := 69949301532587495084621

theorem tailTrace_919524 : CollatzResearch.WordTrace tailWord_919524 prefixEnd_919524 69949301532587495084621 := by
  unfold tailWord_919524
  simp only [CollatzResearch.WordTrace]
  refine ⟨16768897760364532520770813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22358530347152710027694417 16768897760364532520770813)
  ·
    refine ⟨6288336660136699695289055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16768897760364532520770813 6288336660136699695289055)
    ·
      refine ⟨9432504990205049542933583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6288336660136699695289055 9432504990205049542933583)
      ·
        refine ⟨14148757485307574314400375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9432504990205049542933583 14148757485307574314400375)
        ·
          refine ⟨21223136227961361471600563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14148757485307574314400375 21223136227961361471600563)
          ·
            refine ⟨31834704341942042207400845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21223136227961361471600563 31834704341942042207400845)
            ·
              refine ⟨11938014128228265827775317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31834704341942042207400845 11938014128228265827775317)
              ·
                refine ⟨69949301532587495084621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11938014128228265827775317 69949301532587495084621)
                ·
                  rfl

theorem cell21_919524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_919524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919524 prefixEnd_919524 := by exact prefixLift 919524
  have htrace : WordTrace (prefixWord ++ tailWord_919524) baseStart_919524 baseEnd_919524 := by
    simpa [prefixWord, tailWord_919524, baseEnd_919524] using wordTrace_append hprefix tailTrace_919524
  have hstable : (prefixWord ++ tailWord_919524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919524).length < 2 ^ (prefixWord ++ tailWord_919524).sum := by decide
  have hdescent : baseEnd_919524 < baseStart_919524 := by decide
  rcases family_descends (prefixWord ++ tailWord_919524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919569 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 10]
def baseStart_919569 : Nat := 118140960795 + 919569 * 2 ^ 59
def prefixEnd_919569 : Nat := 4983230072969 + 3 ^ 40 * 919569 * 2
def baseEnd_919569 : Nat := 209858174210852407003771

theorem tailTrace_919569 : CollatzResearch.WordTrace tailWord_919569 prefixEnd_919569 209858174210852407003771 := by
  unfold tailWord_919569
  simp only [CollatzResearch.WordTrace]
  refine ⟨33539436805566037726929761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22359624537044025151286507 33539436805566037726929761)
  ·
    refine ⟨25154577604174528295197321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33539436805566037726929761 25154577604174528295197321)
    ·
      refine ⟨18865933203130896221397991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25154577604174528295197321 18865933203130896221397991)
      ·
        refine ⟨28298899804696344332096987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18865933203130896221397991 28298899804696344332096987)
        ·
          refine ⟨42448349707044516498145481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28298899804696344332096987 42448349707044516498145481)
          ·
            refine ⟨31836262280283387373609111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42448349707044516498145481 31836262280283387373609111)
            ·
              refine ⟨47754393420425081060413667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31836262280283387373609111 47754393420425081060413667)
              ·
                refine ⟨71631590130637621590620501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47754393420425081060413667 71631590130637621590620501)
                ·
                  refine ⟨209858174210852407003771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 71631590130637621590620501 209858174210852407003771)
                  ·
                    rfl

theorem cell21_919569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_919569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919569 prefixEnd_919569 := by exact prefixLift 919569
  have htrace : WordTrace (prefixWord ++ tailWord_919569) baseStart_919569 baseEnd_919569 := by
    simpa [prefixWord, tailWord_919569, baseEnd_919569] using wordTrace_append hprefix tailTrace_919569
  have hstable : (prefixWord ++ tailWord_919569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919569).length < 2 ^ (prefixWord ++ tailWord_919569).sum := by decide
  have hdescent : baseEnd_919569 < baseStart_919569 := by decide
  rcases family_descends (prefixWord ++ tailWord_919569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919586 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_919586 : Nat := 118140960795 + 919586 * 2 ^ 59
def prefixEnd_919586 : Nat := 4983230072969 + 3 ^ 40 * 919586 * 2
def baseEnd_919586 : Nat := 209862053842464155220403

theorem tailTrace_919586 : CollatzResearch.WordTrace tailWord_919586 prefixEnd_919586 209862053842464155220403 := by
  unfold tailWord_919586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8385014211626112407574653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22360037897669633086865741 8385014211626112407574653)
  ·
    refine ⟨3144380329359792152840495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8385014211626112407574653 3144380329359792152840495)
    ·
      refine ⟨4716570494039688229260743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3144380329359792152840495 4716570494039688229260743)
      ·
        refine ⟨7074855741059532343891115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4716570494039688229260743 7074855741059532343891115)
        ·
          refine ⟨10612283611589298515836673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7074855741059532343891115 10612283611589298515836673)
          ·
            refine ⟨7959212708691973886877505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10612283611589298515836673 7959212708691973886877505)
            ·
              refine ⟨5969409531518980415158129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7959212708691973886877505 5969409531518980415158129)
              ·
                refine ⟨4477057148639235311368597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969409531518980415158129 4477057148639235311368597)
                ·
                  refine ⟨209862053842464155220403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4477057148639235311368597 209862053842464155220403)
                  ·
                    rfl

theorem cell21_919586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_919586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919586 prefixEnd_919586 := by exact prefixLift 919586
  have htrace : WordTrace (prefixWord ++ tailWord_919586) baseStart_919586 baseEnd_919586 := by
    simpa [prefixWord, tailWord_919586, baseEnd_919586] using wordTrace_append hprefix tailTrace_919586
  have hstable : (prefixWord ++ tailWord_919586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919586).length < 2 ^ (prefixWord ++ tailWord_919586).sum := by decide
  have hdescent : baseEnd_919586 < baseStart_919586 := by decide
  rcases family_descends (prefixWord ++ tailWord_919586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919589 : List Nat := [1, 3, 1, 2, 2, 4, 2, 3, 3]
def baseStart_919589 : Nat := 118140960795 + 919589 * 2 ^ 59
def prefixEnd_919589 : Nat := 4983230072969 + 3 ^ 40 * 919589 * 2
def baseEnd_919589 : Nat := 209862738483336816670397

theorem tailTrace_919589 : CollatzResearch.WordTrace tailWord_919589 prefixEnd_919589 209862738483336816670397 := by
  unfold tailWord_919589
  simp only [CollatzResearch.WordTrace]
  refine ⟨33540166265493581142657821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22360110843662387428438547 33540166265493581142657821)
  ·
    refine ⟨12577562349560092928496683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33540166265493581142657821 12577562349560092928496683)
    ·
      refine ⟨18866343524340139392745025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12577562349560092928496683 18866343524340139392745025)
      ·
        refine ⟨14149757643255104544558769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18866343524340139392745025 14149757643255104544558769)
        ·
          refine ⟨10612318232441328408419077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14149757643255104544558769 10612318232441328408419077)
          ·
            refine ⟨1989809668582749076578577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10612318232441328408419077 1989809668582749076578577)
            ·
              refine ⟨1492357251437061807433933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989809668582749076578577 1492357251437061807433933)
              ·
                refine ⟨559633969288898177787725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1492357251437061807433933 559633969288898177787725)
                ·
                  refine ⟨209862738483336816670397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559633969288898177787725 209862738483336816670397)
                  ·
                    rfl

theorem cell21_919589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_919589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919589 prefixEnd_919589 := by exact prefixLift 919589
  have htrace : WordTrace (prefixWord ++ tailWord_919589) baseStart_919589 baseEnd_919589 := by
    simpa [prefixWord, tailWord_919589, baseEnd_919589] using wordTrace_append hprefix tailTrace_919589
  have hstable : (prefixWord ++ tailWord_919589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919589).length < 2 ^ (prefixWord ++ tailWord_919589).sum := by decide
  have hdescent : baseEnd_919589 < baseStart_919589 := by decide
  rcases family_descends (prefixWord ++ tailWord_919589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919600 : List Nat := [2, 1, 1, 1, 2, 6, 8]
def baseStart_919600 : Nat := 118140960795 + 919600 * 2 ^ 59
def prefixEnd_919600 : Nat := 4983230072969 + 3 ^ 40 * 919600 * 2
def baseEnd_919600 : Nat := 23318360981467026887449

theorem tailTrace_919600 : CollatzResearch.WordTrace tailWord_919600 prefixEnd_919600 23318360981467026887449 := by
  unfold tailWord_919600
  simp only [CollatzResearch.WordTrace]
  refine ⟨16770283734226865010654127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22360378312302486680872169 16770283734226865010654127)
  ·
    refine ⟨25155425601340297515981191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16770283734226865010654127 25155425601340297515981191)
    ·
      refine ⟨37733138402010446273971787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25155425601340297515981191 37733138402010446273971787)
      ·
        refine ⟨56599707603015669410957681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37733138402010446273971787 56599707603015669410957681)
        ·
          refine ⟨42449780702261752058218261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56599707603015669410957681 42449780702261752058218261)
          ·
            refine ⟨1989833470418519627728981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42449780702261752058218261 1989833470418519627728981)
            ·
              refine ⟨23318360981467026887449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1989833470418519627728981 23318360981467026887449)
              ·
                rfl

theorem cell21_919600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 8].length) (baseStart_919600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919600 prefixEnd_919600 := by exact prefixLift 919600
  have htrace : WordTrace (prefixWord ++ tailWord_919600) baseStart_919600 baseEnd_919600 := by
    simpa [prefixWord, tailWord_919600, baseEnd_919600] using wordTrace_append hprefix tailTrace_919600
  have hstable : (prefixWord ++ tailWord_919600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919600).length < 2 ^ (prefixWord ++ tailWord_919600).sum := by decide
  have hdescent : baseEnd_919600 < baseStart_919600 := by decide
  rcases family_descends (prefixWord ++ tailWord_919600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919662 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_919662 : Nat := 118140960795 + 919662 * 2 ^ 59
def prefixEnd_919662 : Nat := 4983230072969 + 3 ^ 40 * 919662 * 2
def baseEnd_919662 : Nat := 209879398077904911953581

theorem tailTrace_919662 : CollatzResearch.WordTrace tailWord_919662 prefixEnd_919662 209879398077904911953581 := by
  unfold tailWord_919662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192853599278639326258155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22361885862819409740043493 4192853599278639326258155)
  ·
    refine ⟨6289280398917958989387233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4192853599278639326258155 6289280398917958989387233)
    ·
      refine ⟨4716960299188469242040425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6289280398917958989387233 4716960299188469242040425)
      ·
        refine ⟨3537720224391351931530319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4716960299188469242040425 3537720224391351931530319)
        ·
          refine ⟨5306580336587027897295479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537720224391351931530319 5306580336587027897295479)
          ·
            refine ⟨7959870504880541845943219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306580336587027897295479 7959870504880541845943219)
            ·
              refine ⟨11939805757320812768914829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959870504880541845943219 11939805757320812768914829)
              ·
                refine ⟨4477427158995304788343061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11939805757320812768914829 4477427158995304788343061)
                ·
                  refine ⟨209879398077904911953581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4477427158995304788343061 209879398077904911953581)
                  ·
                    rfl

theorem cell21_919662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_919662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919662 prefixEnd_919662 := by exact prefixLift 919662
  have htrace : WordTrace (prefixWord ++ tailWord_919662) baseStart_919662 baseEnd_919662 := by
    simpa [prefixWord, tailWord_919662, baseEnd_919662] using wordTrace_append hprefix tailTrace_919662
  have hstable : (prefixWord ++ tailWord_919662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919662).length < 2 ^ (prefixWord ++ tailWord_919662).sum := by decide
  have hdescent : baseEnd_919662 < baseStart_919662 := by decide
  rcases family_descends (prefixWord ++ tailWord_919662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919665 : List Nat := [1, 2, 2, 2, 1, 1, 7, 2, 3]
def baseStart_919665 : Nat := 118140960795 + 919665 * 2 ^ 59
def prefixEnd_919665 : Nat := 4983230072969 + 3 ^ 40 * 919665 * 2
def baseEnd_919665 : Nat := 209880082718777573403575

theorem tailTrace_919665 : CollatzResearch.WordTrace tailWord_919665 prefixEnd_919665 209880082718777573403575 := by
  unfold tailWord_919665
  simp only [CollatzResearch.WordTrace]
  refine ⟨33542938213218246122424449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22361958808812164081616299 33542938213218246122424449)
  ·
    refine ⟨25157203659913684591818337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33542938213218246122424449 25157203659913684591818337)
    ·
      refine ⟨18867902744935263443863753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25157203659913684591818337 18867902744935263443863753)
      ·
        refine ⟨14150927058701447582897815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18867902744935263443863753 14150927058701447582897815)
        ·
          refine ⟨21226390588052171374346723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14150927058701447582897815 21226390588052171374346723)
          ·
            refine ⟨31839585882078257061520085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21226390588052171374346723 31839585882078257061520085)
            ·
              refine ⟨746240294111209149879377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31839585882078257061520085 746240294111209149879377)
              ·
                refine ⟨559680220583406862409533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746240294111209149879377 559680220583406862409533)
                ·
                  refine ⟨209880082718777573403575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559680220583406862409533 209880082718777573403575)
                  ·
                    rfl

theorem cell21_919665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 3].length) (baseStart_919665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919665 prefixEnd_919665 := by exact prefixLift 919665
  have htrace : WordTrace (prefixWord ++ tailWord_919665) baseStart_919665 baseEnd_919665 := by
    simpa [prefixWord, tailWord_919665, baseEnd_919665] using wordTrace_append hprefix tailTrace_919665
  have hstable : (prefixWord ++ tailWord_919665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919665).length < 2 ^ (prefixWord ++ tailWord_919665).sum := by decide
  have hdescent : baseEnd_919665 < baseStart_919665 := by decide
  rcases family_descends (prefixWord ++ tailWord_919665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919676 : List Nat := [2, 2, 2, 1, 1, 4, 1, 8]
def baseStart_919676 : Nat := 118140960795 + 919676 * 2 ^ 59
def prefixEnd_919676 : Nat := 4983230072969 + 3 ^ 40 * 919676 * 2
def baseEnd_919676 : Nat := 69960864356214666240073

theorem tailTrace_919676 : CollatzResearch.WordTrace tailWord_919676 prefixEnd_919676 69960864356214666240073 := by
  unfold tailWord_919676
  simp only [CollatzResearch.WordTrace]
  refine ⟨16771669708089197500537441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22362226277452263334049921 16771669708089197500537441)
  ·
    refine ⟨12578752281066898125403081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16771669708089197500537441 12578752281066898125403081)
    ·
      refine ⟨9434064210800173594052311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12578752281066898125403081 9434064210800173594052311)
      ·
        refine ⟨14151096316200260391078467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9434064210800173594052311 14151096316200260391078467)
        ·
          refine ⟨21226644474300390586617701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14151096316200260391078467 21226644474300390586617701)
          ·
            refine ⟨3979995838931323234990819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21226644474300390586617701 3979995838931323234990819)
            ·
              refine ⟨5969993758396984852486229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979995838931323234990819 5969993758396984852486229)
              ·
                refine ⟨69960864356214666240073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5969993758396984852486229 69960864356214666240073)
                ·
                  rfl

theorem cell21_919676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_919676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919676 prefixEnd_919676 := by exact prefixLift 919676
  have htrace : WordTrace (prefixWord ++ tailWord_919676) baseStart_919676 baseEnd_919676 := by
    simpa [prefixWord, tailWord_919676, baseEnd_919676] using wordTrace_append hprefix tailTrace_919676
  have hstable : (prefixWord ++ tailWord_919676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919676).length < 2 ^ (prefixWord ++ tailWord_919676).sum := by decide
  have hdescent : baseEnd_919676 < baseStart_919676 := by decide
  rcases family_descends (prefixWord ++ tailWord_919676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919710 : List Nat := [4, 3, 1, 1, 4, 8]
def baseStart_919710 : Nat := 118140960795 + 919710 * 2 ^ 59
def prefixEnd_919710 : Nat := 4983230072969 + 3 ^ 40 * 919710 * 2
def baseEnd_919710 : Nat := 7773716753032129450129

theorem tailTrace_919710 : CollatzResearch.WordTrace tailWord_919710 prefixEnd_919710 7773716753032129450129 := by
  unfold tailWord_919710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4193072437256902350976573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22363052998703479205208389 4193072437256902350976573)
  ·
    refine ⟨1572402163971338381616215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4193072437256902350976573 1572402163971338381616215)
    ·
      refine ⟨2358603245957007572424323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1572402163971338381616215 2358603245957007572424323)
      ·
        refine ⟨3537904868935511358636485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358603245957007572424323 3537904868935511358636485)
        ·
          refine ⟨663357162925408379744341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3537904868935511358636485 663357162925408379744341)
          ·
            refine ⟨7773716753032129450129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 663357162925408379744341 7773716753032129450129)
            ·
              rfl

theorem cell21_919710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 8].length) (baseStart_919710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919710 prefixEnd_919710 := by exact prefixLift 919710
  have htrace : WordTrace (prefixWord ++ tailWord_919710) baseStart_919710 baseEnd_919710 := by
    simpa [prefixWord, tailWord_919710, baseEnd_919710] using wordTrace_append hprefix tailTrace_919710
  have hstable : (prefixWord ++ tailWord_919710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919710).length < 2 ^ (prefixWord ++ tailWord_919710).sum := by decide
  have hdescent : baseEnd_919710 < baseStart_919710 := by decide
  rcases family_descends (prefixWord ++ tailWord_919710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919738 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_919738 : Nat := 118140960795 + 919738 * 2 ^ 59
def prefixEnd_919738 : Nat := 4983230072969 + 3 ^ 40 * 919738 * 2
def baseEnd_919738 : Nat := 209896742313345668686759

theorem tailTrace_919738 : CollatzResearch.WordTrace tailWord_919738 prefixEnd_919738 209896742313345668686759 := by
  unfold tailWord_919738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386400185488444897457967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22363733827969186393221245 8386400185488444897457967)
  ·
    refine ⟨12579600278232667346186951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8386400185488444897457967 12579600278232667346186951)
    ·
      refine ⟨18869400417349001019280427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12579600278232667346186951 18869400417349001019280427)
      ·
        refine ⟨28304100626023501528920641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18869400417349001019280427 28304100626023501528920641)
        ·
          refine ⟨21228075469517626146690481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28304100626023501528920641 21228075469517626146690481)
          ·
            refine ⟨15921056602138219610017861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21228075469517626146690481 15921056602138219610017861)
            ·
              refine ⟨2985198112900916176878349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15921056602138219610017861 2985198112900916176878349)
              ·
                refine ⟨1119449292337843566329381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2985198112900916176878349 1119449292337843566329381)
                ·
                  refine ⟨209896742313345668686759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119449292337843566329381 209896742313345668686759)
                  ·
                    rfl

theorem cell21_919738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_919738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919738 prefixEnd_919738 := by exact prefixLift 919738
  have htrace : WordTrace (prefixWord ++ tailWord_919738) baseStart_919738 baseEnd_919738 := by
    simpa [prefixWord, tailWord_919738, baseEnd_919738] using wordTrace_append hprefix tailTrace_919738
  have hstable : (prefixWord ++ tailWord_919738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919738).length < 2 ^ (prefixWord ++ tailWord_919738).sum := by decide
  have hdescent : baseEnd_919738 < baseStart_919738 := by decide
  rcases family_descends (prefixWord ++ tailWord_919738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919772 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 6]
def baseStart_919772 : Nat := 118140960795 + 919772 * 2 ^ 59
def prefixEnd_919772 : Nat := 4983230072969 + 3 ^ 40 * 919772 * 2
def baseEnd_919772 : Nat := 209904501576569165120023

theorem tailTrace_919772 : CollatzResearch.WordTrace tailWord_919772 prefixEnd_919772 209904501576569165120023 := by
  unfold tailWord_919772
  simp only [CollatzResearch.WordTrace]
  refine ⟨16773420411915301698284785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22364560549220402264379713 16773420411915301698284785)
  ·
    refine ⟨12580065308936476273713589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16773420411915301698284785 12580065308936476273713589)
    ·
      refine ⟨1179381122712794650660649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12580065308936476273713589 1179381122712794650660649)
      ·
        refine ⟨884535842034595987995487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1179381122712794650660649 884535842034595987995487)
        ·
          refine ⟨1326803763051893981993231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884535842034595987995487 1326803763051893981993231)
          ·
            refine ⟨1990205644577840972989847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326803763051893981993231 1990205644577840972989847)
            ·
              refine ⟨2985308466866761459484771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990205644577840972989847 2985308466866761459484771)
              ·
                refine ⟨4477962700300142189227157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985308466866761459484771 4477962700300142189227157)
                ·
                  refine ⟨209904501576569165120023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4477962700300142189227157 209904501576569165120023)
                  ·
                    rfl

theorem cell21_919772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_919772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919772 prefixEnd_919772 := by exact prefixLift 919772
  have htrace : WordTrace (prefixWord ++ tailWord_919772) baseStart_919772 baseEnd_919772 := by
    simpa [prefixWord, tailWord_919772, baseEnd_919772] using wordTrace_append hprefix tailTrace_919772
  have hstable : (prefixWord ++ tailWord_919772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919772).length < 2 ^ (prefixWord ++ tailWord_919772).sum := by decide
  have hdescent : baseEnd_919772 < baseStart_919772 := by decide
  rcases family_descends (prefixWord ++ tailWord_919772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919817 : List Nat := [1, 2, 1, 1, 3, 6, 1, 3, 3]
def baseStart_919817 : Nat := 118140960795 + 919817 * 2 ^ 59
def prefixEnd_919817 : Nat := 4983230072969 + 3 ^ 40 * 919817 * 2
def baseEnd_919817 : Nat := 209914771189659086869931

theorem tailTrace_919817 : CollatzResearch.WordTrace tailWord_919817 prefixEnd_919817 209914771189659086869931 := by
  unfold tailWord_919817
  simp only [CollatzResearch.WordTrace]
  refine ⟨33548482108667576081957705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22365654739111717387971803 33548482108667576081957705)
  ·
    refine ⟨25161361581500682061468279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33548482108667576081957705 25161361581500682061468279)
    ·
      refine ⟨37742042372251023092202419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25161361581500682061468279 37742042372251023092202419)
      ·
        refine ⟨56613063558376534638303629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37742042372251023092202419 56613063558376534638303629)
        ·
          refine ⟨21229898834391200489363861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56613063558376534638303629 21229898834391200489363861)
          ·
            refine ⟨995151507862087522938931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21229898834391200489363861 995151507862087522938931)
            ·
              refine ⟨1492727261793131284408397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995151507862087522938931 1492727261793131284408397)
              ·
                refine ⟨559772723172424231653149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1492727261793131284408397 559772723172424231653149)
                ·
                  refine ⟨209914771189659086869931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559772723172424231653149 209914771189659086869931)
                  ·
                    rfl

theorem cell21_919817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 3].length) (baseStart_919817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919817 prefixEnd_919817 := by exact prefixLift 919817
  have htrace : WordTrace (prefixWord ++ tailWord_919817) baseStart_919817 baseEnd_919817 := by
    simpa [prefixWord, tailWord_919817, baseEnd_919817] using wordTrace_append hprefix tailTrace_919817
  have hstable : (prefixWord ++ tailWord_919817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919817).length < 2 ^ (prefixWord ++ tailWord_919817).sum := by decide
  have hdescent : baseEnd_919817 < baseStart_919817 := by decide
  rcases family_descends (prefixWord ++ tailWord_919817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919834 : List Nat := [3, 1, 1, 3, 4, 1, 3, 2, 3]
def baseStart_919834 : Nat := 118140960795 + 919834 * 2 ^ 59
def prefixEnd_919834 : Nat := 4983230072969 + 3 ^ 40 * 919834 * 2
def baseEnd_919834 : Nat := 209918650821270835086563

theorem tailTrace_919834 : CollatzResearch.WordTrace tailWord_919834 prefixEnd_919834 209918650821270835086563 := by
  unfold tailWord_919834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8387275537401496996331639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22366068099737325323551037 8387275537401496996331639)
  ·
    refine ⟨12580913306102245494497459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8387275537401496996331639 12580913306102245494497459)
    ·
      refine ⟨18871369959153368241746189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12580913306102245494497459 18871369959153368241746189)
      ·
        refine ⟨7076763734682513090654821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18871369959153368241746189 7076763734682513090654821)
        ·
          refine ⟨1326893200252971204497779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7076763734682513090654821 1326893200252971204497779)
          ·
            refine ⟨1990339800379456806746669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326893200252971204497779 1990339800379456806746669)
            ·
              refine ⟨746377425142296302530001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1990339800379456806746669 746377425142296302530001)
              ·
                refine ⟨559783068856722226897501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746377425142296302530001 559783068856722226897501)
                ·
                  refine ⟨209918650821270835086563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559783068856722226897501 209918650821270835086563)
                  ·
                    rfl

theorem cell21_919834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_919834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919834 prefixEnd_919834 := by exact prefixLift 919834
  have htrace : WordTrace (prefixWord ++ tailWord_919834) baseStart_919834 baseEnd_919834 := by
    simpa [prefixWord, tailWord_919834, baseEnd_919834] using wordTrace_append hprefix tailTrace_919834
  have hstable : (prefixWord ++ tailWord_919834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919834).length < 2 ^ (prefixWord ++ tailWord_919834).sum := by decide
  have hdescent : baseEnd_919834 < baseStart_919834 := by decide
  rcases family_descends (prefixWord ++ tailWord_919834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919845 : List Nat := [1, 3, 1, 2, 5, 1, 2, 6]
def baseStart_919845 : Nat := 118140960795 + 919845 * 2 ^ 59
def prefixEnd_919845 : Nat := 4983230072969 + 3 ^ 40 * 919845 * 2
def baseEnd_919845 : Nat := 69973720390379086801069

theorem tailTrace_919845 : CollatzResearch.WordTrace tailWord_919845 prefixEnd_919845 69973720390379086801069 := by
  unfold tailWord_919845
  simp only [CollatzResearch.WordTrace]
  refine ⟨33549503352566136863976989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22366335568377424575984659 33549503352566136863976989)
  ·
    refine ⟨12581063757212301323991371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33549503352566136863976989 12581063757212301323991371)
    ·
      refine ⟨18871595635818451985987057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12581063757212301323991371 18871595635818451985987057)
      ·
        refine ⟨14153696726863838989490293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18871595635818451985987057 14153696726863838989490293)
        ·
          refine ⟨1326909068143484905264715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14153696726863838989490293 1326909068143484905264715)
          ·
            refine ⟨1990363602215227357897073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326909068143484905264715 1990363602215227357897073)
            ·
              refine ⟨1492772701661420518422805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990363602215227357897073 1492772701661420518422805)
              ·
                refine ⟨69973720390379086801069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1492772701661420518422805 69973720390379086801069)
                ·
                  rfl

theorem cell21_919845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 6].length) (baseStart_919845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919845 prefixEnd_919845 := by exact prefixLift 919845
  have htrace : WordTrace (prefixWord ++ tailWord_919845) baseStart_919845 baseEnd_919845 := by
    simpa [prefixWord, tailWord_919845, baseEnd_919845] using wordTrace_append hprefix tailTrace_919845
  have hstable : (prefixWord ++ tailWord_919845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919845).length < 2 ^ (prefixWord ++ tailWord_919845).sum := by decide
  have hdescent : baseEnd_919845 < baseStart_919845 := by decide
  rcases family_descends (prefixWord ++ tailWord_919845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919890 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_919890 : Nat := 118140960795 + 919890 * 2 ^ 59
def prefixEnd_919890 : Nat := 4983230072969 + 3 ^ 40 * 919890 * 2
def baseEnd_919890 : Nat := 209931430784227182153115

theorem tailTrace_919890 : CollatzResearch.WordTrace tailWord_919890 prefixEnd_919890 209931430784227182153115 := by
  unfold tailWord_919890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8387786159350777387341281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22367429758268739699576749 8387786159350777387341281)
  ·
    refine ⟨6290839619513083040505961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8387786159350777387341281 6290839619513083040505961)
    ·
      refine ⟨4718129714634812280379471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6290839619513083040505961 4718129714634812280379471)
      ·
        refine ⟨7077194571952218420569207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4718129714634812280379471 7077194571952218420569207)
        ·
          refine ⟨10615791857928327630853811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7077194571952218420569207 10615791857928327630853811)
          ·
            refine ⟨15923687786892491446280717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10615791857928327630853811 15923687786892491446280717)
            ·
              refine ⟨5971382920084684292355269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15923687786892491446280717 5971382920084684292355269)
              ·
                refine ⟨1119634297515878304816613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5971382920084684292355269 1119634297515878304816613)
                ·
                  refine ⟨209931430784227182153115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119634297515878304816613 209931430784227182153115)
                  ·
                    rfl

theorem cell21_919890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_919890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919890 prefixEnd_919890 := by exact prefixLift 919890
  have htrace : WordTrace (prefixWord ++ tailWord_919890) baseStart_919890 baseEnd_919890 := by
    simpa [prefixWord, tailWord_919890, baseEnd_919890] using wordTrace_append hprefix tailTrace_919890
  have hstable : (prefixWord ++ tailWord_919890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919890).length < 2 ^ (prefixWord ++ tailWord_919890).sum := by decide
  have hdescent : baseEnd_919890 < baseStart_919890 := by decide
  rcases family_descends (prefixWord ++ tailWord_919890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919893 : List Nat := [1, 3, 2, 2, 4, 1, 1, 4, 3]
def baseStart_919893 : Nat := 118140960795 + 919893 * 2 ^ 59
def prefixEnd_919893 : Nat := 4983230072969 + 3 ^ 40 * 919893 * 2
def baseEnd_919893 : Nat := 209932115425099843603109

theorem tailTrace_919893 : CollatzResearch.WordTrace tailWord_919893 prefixEnd_919893 209932115425099843603109 := by
  unfold tailWord_919893
  simp only [CollatzResearch.WordTrace]
  refine ⟨33551254056392241061724333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22367502704261494041149555 33551254056392241061724333)
  ·
    refine ⟨12581720271147090398146625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33551254056392241061724333 12581720271147090398146625)
    ·
      refine ⟨9436290203360317798609969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12581720271147090398146625 9436290203360317798609969)
      ·
        refine ⟨7077217652520238348957477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9436290203360317798609969 7077217652520238348957477)
        ·
          refine ⟨1326978309847544690429527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7077217652520238348957477 1326978309847544690429527)
          ·
            refine ⟨1990467464771317035644291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326978309847544690429527 1990467464771317035644291)
            ·
              refine ⟨2985701197156975553466437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990467464771317035644291 2985701197156975553466437)
              ·
                refine ⟨559818974466932916274957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2985701197156975553466437 559818974466932916274957)
                ·
                  refine ⟨209932115425099843603109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559818974466932916274957 209932115425099843603109)
                  ·
                    rfl

theorem cell21_919893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_919893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919893 prefixEnd_919893 := by exact prefixLift 919893
  have htrace : WordTrace (prefixWord ++ tailWord_919893) baseStart_919893 baseEnd_919893 := by
    simpa [prefixWord, tailWord_919893, baseEnd_919893] using wordTrace_append hprefix tailTrace_919893
  have hstable : (prefixWord ++ tailWord_919893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919893).length < 2 ^ (prefixWord ++ tailWord_919893).sum := by decide
  have hdescent : baseEnd_919893 < baseStart_919893 := by decide
  rcases family_descends (prefixWord ++ tailWord_919893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919938 : List Nat := [3, 4, 2, 1, 2, 1, 8]
def baseStart_919938 : Nat := 118140960795 + 919938 * 2 ^ 59
def prefixEnd_919938 : Nat := 4983230072969 + 3 ^ 40 * 919938 * 2
def baseEnd_919938 : Nat := 23326931670909973928113

theorem tailTrace_919938 : CollatzResearch.WordTrace tailWord_919938 prefixEnd_919938 23326931670909973928113 := by
  unfold tailWord_919938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8388223835307303436778117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22368596894152809164741645 8388223835307303436778117)
  ·
    refine ⟨1572791969120119394395897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8388223835307303436778117 1572791969120119394395897)
    ·
      refine ⟨1179593976840089545796923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1572791969120119394395897 1179593976840089545796923)
      ·
        refine ⟨1769390965260134318695385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179593976840089545796923 1769390965260134318695385)
        ·
          refine ⟨1327043223945100739021539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1769390965260134318695385 1327043223945100739021539)
          ·
            refine ⟨1990564835917651108532309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327043223945100739021539 1990564835917651108532309)
            ·
              refine ⟨23326931670909973928113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1990564835917651108532309 23326931670909973928113)
              ·
                rfl

theorem cell21_919938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 8].length) (baseStart_919938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919938 prefixEnd_919938 := by exact prefixLift 919938
  have htrace : WordTrace (prefixWord ++ tailWord_919938) baseStart_919938 baseEnd_919938 := by
    simpa [prefixWord, tailWord_919938, baseEnd_919938] using wordTrace_append hprefix tailTrace_919938
  have hstable : (prefixWord ++ tailWord_919938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919938).length < 2 ^ (prefixWord ++ tailWord_919938).sum := by decide
  have hdescent : baseEnd_919938 < baseStart_919938 := by decide
  rcases family_descends (prefixWord ++ tailWord_919938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919994 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_919994 : Nat := 118140960795 + 919994 * 2 ^ 59
def prefixEnd_919994 : Nat := 4983230072969 + 3 ^ 40 * 919994 * 2
def baseEnd_919994 : Nat := 209955165001146112419569

theorem tailTrace_919994 : CollatzResearch.WordTrace tailWord_919994 prefixEnd_919994 209955165001146112419569 := by
  unfold tailWord_919994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8388734457256583827787759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22369958552684223540767357 8388734457256583827787759)
  ·
    refine ⟨12583101685884875741681639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8388734457256583827787759 12583101685884875741681639)
    ·
      refine ⟨18874652528827313612522459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12583101685884875741681639 18874652528827313612522459)
      ·
        refine ⟨28311978793240970418783689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18874652528827313612522459 28311978793240970418783689)
        ·
          refine ⟨21233984094930727814087767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28311978793240970418783689 21233984094930727814087767)
          ·
            refine ⟨31850976142396091721131651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21233984094930727814087767 31850976142396091721131651)
            ·
              refine ⟨47776464213594137581697477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31850976142396091721131651 47776464213594137581697477)
              ·
                refine ⟨8958087040048900796568277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47776464213594137581697477 8958087040048900796568277)
                ·
                  refine ⟨209955165001146112419569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8958087040048900796568277 209955165001146112419569)
                  ·
                    rfl

theorem cell21_919994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_919994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_919994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_919994 prefixEnd_919994 := by exact prefixLift 919994
  have htrace : WordTrace (prefixWord ++ tailWord_919994) baseStart_919994 baseEnd_919994 := by
    simpa [prefixWord, tailWord_919994, baseEnd_919994] using wordTrace_append hprefix tailTrace_919994
  have hstable : (prefixWord ++ tailWord_919994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919994).length < 2 ^ (prefixWord ++ tailWord_919994).sum := by decide
  have hdescent : baseEnd_919994 < baseStart_919994 := by decide
  rcases family_descends (prefixWord ++ tailWord_919994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920115 : List Nat := [1, 1, 1, 2, 4, 2, 10]
def baseStart_920115 : Nat := 118140960795 + 920115 * 2 ^ 59
def prefixEnd_920115 : Nat := 4983230072969 + 3 ^ 40 * 920115 * 2
def baseEnd_920115 : Nat := 23331419872186310100295

theorem tailTrace_920115 : CollatzResearch.WordTrace tailWord_920115 prefixEnd_920115 23331419872186310100295 := by
  unfold tailWord_920115
  simp only [CollatzResearch.WordTrace]
  refine ⟨33559351061587972976305799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22372900707725315317537199 33559351061587972976305799)
  ·
    refine ⟨50339026592381959464458699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33559351061587972976305799 50339026592381959464458699)
    ·
      refine ⟨75508539888572939196688049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50339026592381959464458699 75508539888572939196688049)
      ·
        refine ⟨56631404916429704397516037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75508539888572939196688049 56631404916429704397516037)
        ·
          refine ⟨10618388421830569574534257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56631404916429704397516037 10618388421830569574534257)
          ·
            refine ⟨7963791316372927180900693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10618388421830569574534257 7963791316372927180900693)
            ·
              refine ⟨23331419872186310100295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7963791316372927180900693 23331419872186310100295)
              ·
                rfl

theorem cell21_920115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 10].length) (baseStart_920115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920115 prefixEnd_920115 := by exact prefixLift 920115
  have htrace : WordTrace (prefixWord ++ tailWord_920115) baseStart_920115 baseEnd_920115 := by
    simpa [prefixWord, tailWord_920115, baseEnd_920115] using wordTrace_append hprefix tailTrace_920115
  have hstable : (prefixWord ++ tailWord_920115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920115).length < 2 ^ (prefixWord ++ tailWord_920115).sum := by decide
  have hdescent : baseEnd_920115 < baseStart_920115 := by decide
  rcases family_descends (prefixWord ++ tailWord_920115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920135 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 4]
def baseStart_920135 : Nat := 118140960795 + 920135 * 2 ^ 59
def prefixEnd_920135 : Nat := 4983230072969 + 3 ^ 40 * 920135 * 2
def baseEnd_920135 : Nat := 209987343122161200569281

theorem tailTrace_920135 : CollatzResearch.WordTrace tailWord_920135 prefixEnd_920135 209987343122161200569281 := by
  unfold tailWord_920135
  simp only [CollatzResearch.WordTrace]
  refine ⟨33560080521515516392033859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22373387014343677594689239 33560080521515516392033859)
  ·
    refine ⟨50340120782273274588050789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33560080521515516392033859 50340120782273274588050789)
    ·
      refine ⟨9438772646676238985259523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50340120782273274588050789 9438772646676238985259523)
      ·
        refine ⟨14158158970014358477889285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9438772646676238985259523 14158158970014358477889285)
        ·
          refine ⟨2654654806877692214604241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14158158970014358477889285 2654654806877692214604241)
          ·
            refine ⟨1990991105158269160953181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2654654806877692214604241 1990991105158269160953181)
            ·
              refine ⟨746621664434350935357443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1990991105158269160953181 746621664434350935357443)
              ·
                refine ⟨1119932496651526403036165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746621664434350935357443 1119932496651526403036165)
                ·
                  refine ⟨209987343122161200569281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119932496651526403036165 209987343122161200569281)
                  ·
                    rfl

theorem cell21_920135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 4].length) (baseStart_920135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920135 prefixEnd_920135 := by exact prefixLift 920135
  have htrace : WordTrace (prefixWord ++ tailWord_920135) baseStart_920135 baseEnd_920135 := by
    simpa [prefixWord, tailWord_920135, baseEnd_920135] using wordTrace_append hprefix tailTrace_920135
  have hstable : (prefixWord ++ tailWord_920135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920135).length < 2 ^ (prefixWord ++ tailWord_920135).sum := by decide
  have hdescent : baseEnd_920135 < baseStart_920135 := by decide
  rcases family_descends (prefixWord ++ tailWord_920135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920231 : List Nat := [1, 1, 6, 3, 1, 2, 2, 2, 3]
def baseStart_920231 : Nat := 118140960795 + 920231 * 2 ^ 59
def prefixEnd_920231 : Nat := 4983230072969 + 3 ^ 40 * 920231 * 2
def baseEnd_920231 : Nat := 210009251630086366969085

theorem tailTrace_920231 : CollatzResearch.WordTrace tailWord_920231 prefixEnd_920231 210009251630086366969085 := by
  unfold tailWord_920231
  simp only [CollatzResearch.WordTrace]
  refine ⟨33563581929167724787528547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22375721286111816525019031 33563581929167724787528547)
  ·
    refine ⟨50345372893751587181292821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33563581929167724787528547 50345372893751587181292821)
    ·
      refine ⟨2359939354394605649123101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50345372893751587181292821 2359939354394605649123101)
      ·
        refine ⟨884977257897977118421163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2359939354394605649123101 884977257897977118421163)
        ·
          refine ⟨1327465886846965677631745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884977257897977118421163 1327465886846965677631745)
          ·
            refine ⟨995599415135224258223809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1327465886846965677631745 995599415135224258223809)
            ·
              refine ⟨746699561351418193667857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995599415135224258223809 746699561351418193667857)
              ·
                refine ⟨560024671013563645250893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746699561351418193667857 560024671013563645250893)
                ·
                  refine ⟨210009251630086366969085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560024671013563645250893 210009251630086366969085)
                  ·
                    rfl

theorem cell21_920231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 3].length) (baseStart_920231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920231 prefixEnd_920231 := by exact prefixLift 920231
  have htrace : WordTrace (prefixWord ++ tailWord_920231) baseStart_920231 baseEnd_920231 := by
    simpa [prefixWord, tailWord_920231, baseEnd_920231] using wordTrace_append hprefix tailTrace_920231
  have hstable : (prefixWord ++ tailWord_920231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920231).length < 2 ^ (prefixWord ++ tailWord_920231).sum := by decide
  have hdescent : baseEnd_920231 < baseStart_920231 := by decide
  rcases family_descends (prefixWord ++ tailWord_920231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920318 : List Nat := [4, 2, 2, 1, 2, 3, 2, 5]
def baseStart_920318 : Nat := 118140960795 + 920318 * 2 ^ 59
def prefixEnd_920318 : Nat := 4983230072969 + 3 ^ 40 * 920318 * 2
def baseEnd_920318 : Nat := 70009702071797849672969

theorem tailTrace_920318 : CollatzResearch.WordTrace tailWord_920318 prefixEnd_920318 70009702071797849672969 := by
  unfold tailWord_920318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4195844384981567330743201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22377836719901692430630405 4195844384981567330743201)
  ·
    refine ⟨3146883288736175498057401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4195844384981567330743201 3146883288736175498057401)
    ·
      refine ⟨2360162466552131623543051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3146883288736175498057401 2360162466552131623543051)
      ·
        refine ⟨3540243699828197435314577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360162466552131623543051 3540243699828197435314577)
        ·
          refine ⟨2655182774871148076485933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3540243699828197435314577 2655182774871148076485933)
          ·
            refine ⟨995693540576680528682225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2655182774871148076485933 995693540576680528682225)
            ·
              refine ⟨746770155432510396511669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995693540576680528682225 746770155432510396511669)
              ·
                refine ⟨70009702071797849672969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 746770155432510396511669 70009702071797849672969)
                ·
                  rfl

theorem cell21_920318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_920318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920318 prefixEnd_920318 := by exact prefixLift 920318
  have htrace : WordTrace (prefixWord ++ tailWord_920318) baseStart_920318 baseEnd_920318 := by
    simpa [prefixWord, tailWord_920318, baseEnd_920318] using wordTrace_append hprefix tailTrace_920318
  have hstable : (prefixWord ++ tailWord_920318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920318).length < 2 ^ (prefixWord ++ tailWord_920318).sum := by decide
  have hdescent : baseEnd_920318 < baseStart_920318 := by decide
  rcases family_descends (prefixWord ++ tailWord_920318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920349 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 5]
def baseStart_920349 : Nat := 118140960795 + 920349 * 2 ^ 59
def prefixEnd_920349 : Nat := 4983230072969 + 3 ^ 40 * 920349 * 2
def baseEnd_920349 : Nat := 210036180837744384002177

theorem tailTrace_920349 : CollatzResearch.WordTrace tailWord_920349 prefixEnd_920349 210036180837744384002177 := by
  unfold tailWord_920349
  simp only [CollatzResearch.WordTrace]
  refine ⟨33567885742740230940324101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22378590495160153960216067 33567885742740230940324101)
  ·
    refine ⟨6293978576763793301310769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33567885742740230940324101 6293978576763793301310769)
    ·
      refine ⟨4720483932572844975983077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6293978576763793301310769 4720483932572844975983077)
      ·
        refine ⟨885090737357408432996827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4720483932572844975983077 885090737357408432996827)
        ·
          refine ⟨1327636106036112649495241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885090737357408432996827 1327636106036112649495241)
          ·
            refine ⟨995727079527084487121431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1327636106036112649495241 995727079527084487121431)
            ·
              refine ⟨1493590619290626730682147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995727079527084487121431 1493590619290626730682147)
              ·
                refine ⟨2240385928935940096023221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493590619290626730682147 2240385928935940096023221)
                ·
                  refine ⟨210036180837744384002177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2240385928935940096023221 210036180837744384002177)
                  ·
                    rfl

theorem cell21_920349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_920349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920349 prefixEnd_920349 := by exact prefixLift 920349
  have htrace : WordTrace (prefixWord ++ tailWord_920349) baseStart_920349 baseEnd_920349 := by
    simpa [prefixWord, tailWord_920349, baseEnd_920349] using wordTrace_append hprefix tailTrace_920349
  have hstable : (prefixWord ++ tailWord_920349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920349).length < 2 ^ (prefixWord ++ tailWord_920349).sum := by decide
  have hdescent : baseEnd_920349 < baseStart_920349 := by decide
  rcases family_descends (prefixWord ++ tailWord_920349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920360 : List Nat := [2, 1, 5, 1, 1, 1, 4, 6]
def baseStart_920360 : Nat := 118140960795 + 920360 * 2 ^ 59
def prefixEnd_920360 : Nat := 4983230072969 + 3 ^ 40 * 920360 * 2
def baseEnd_920360 : Nat := 70012897062536936439607

theorem tailTrace_920360 : CollatzResearch.WordTrace tailWord_920360 prefixEnd_920360 70012897062536936439607 := by
  unfold tailWord_920360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16784143472850189909487267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22378857963800253212649689 16784143472850189909487267)
  ·
    refine ⟨25176215209275284864230901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16784143472850189909487267 25176215209275284864230901)
    ·
      refine ⟨2360270175869557956021647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25176215209275284864230901 2360270175869557956021647)
      ·
        refine ⟨3540405263804336934032471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360270175869557956021647 3540405263804336934032471)
        ·
          refine ⟨5310607895706505401048707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3540405263804336934032471 5310607895706505401048707)
          ·
            refine ⟨7965911843559758101573061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5310607895706505401048707 7965911843559758101573061)
            ·
              refine ⟨1493608470667454644044949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7965911843559758101573061 1493608470667454644044949)
              ·
                refine ⟨70012897062536936439607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1493608470667454644044949 70012897062536936439607)
                ·
                  rfl

theorem cell21_920360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_920360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920360 prefixEnd_920360 := by exact prefixLift 920360
  have htrace : WordTrace (prefixWord ++ tailWord_920360) baseStart_920360 baseEnd_920360 := by
    simpa [prefixWord, tailWord_920360, baseEnd_920360] using wordTrace_append hprefix tailTrace_920360
  have hstable : (prefixWord ++ tailWord_920360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920360).length < 2 ^ (prefixWord ++ tailWord_920360).sum := by decide
  have hdescent : baseEnd_920360 < baseStart_920360 := by decide
  rcases family_descends (prefixWord ++ tailWord_920360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920391 : List Nat := [1, 1, 4, 1, 2, 1, 1, 7, 3]
def baseStart_920391 : Nat := 118140960795 + 920391 * 2 ^ 59
def prefixEnd_920391 : Nat := 4983230072969 + 3 ^ 40 * 920391 * 2
def baseEnd_920391 : Nat := 210045765809961644302091

theorem tailTrace_920391 : CollatzResearch.WordTrace tailWord_920391 prefixEnd_920391 210045765809961644302091 := by
  unfold tailWord_920391
  simp only [CollatzResearch.WordTrace]
  refine ⟨33569417608588072113353027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22379611739058714742235351 33569417608588072113353027)
  ·
    refine ⟨50354126412882108170029541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33569417608588072113353027 50354126412882108170029541)
    ·
      refine ⟨9441398702415395281880539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50354126412882108170029541 9441398702415395281880539)
      ·
        refine ⟨14162098053623092922820809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9441398702415395281880539 14162098053623092922820809)
        ·
          refine ⟨10621573540217319692115607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14162098053623092922820809 10621573540217319692115607)
          ·
            refine ⟨15932360310325979538173411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10621573540217319692115607 15932360310325979538173411)
            ·
              refine ⟨23898540465488969307260117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15932360310325979538173411 23898540465488969307260117)
              ·
                refine ⟨560122042159897718138909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23898540465488969307260117 560122042159897718138909)
                ·
                  refine ⟨210045765809961644302091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560122042159897718138909 210045765809961644302091)
                  ·
                    rfl

theorem cell21_920391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 3].length) (baseStart_920391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920391 prefixEnd_920391 := by exact prefixLift 920391
  have htrace : WordTrace (prefixWord ++ tailWord_920391) baseStart_920391 baseEnd_920391 := by
    simpa [prefixWord, tailWord_920391, baseEnd_920391] using wordTrace_append hprefix tailTrace_920391
  have hstable : (prefixWord ++ tailWord_920391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920391).length < 2 ^ (prefixWord ++ tailWord_920391).sum := by decide
  have hdescent : baseEnd_920391 < baseStart_920391 := by decide
  rcases family_descends (prefixWord ++ tailWord_920391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920577 : List Nat := [1, 2, 4, 1, 2, 4, 2, 2, 3]
def baseStart_920577 : Nat := 118140960795 + 920577 * 2 ^ 59
def prefixEnd_920577 : Nat := 4983230072969 + 3 ^ 40 * 920577 * 2
def baseEnd_920577 : Nat := 210088213544066654201711

theorem tailTrace_920577 : CollatzResearch.WordTrace tailWord_920577 prefixEnd_920577 210088213544066654201711 := by
  unfold tailWord_920577
  simp only [CollatzResearch.WordTrace]
  refine ⟨33576201585914225879623985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22384134390609483919749323 33576201585914225879623985)
  ·
    refine ⟨25182151189435669409717989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33576201585914225879623985 25182151189435669409717989)
    ·
      refine ⟨4721653348019188014322123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25182151189435669409717989 4721653348019188014322123)
      ·
        refine ⟨7082480022028782021483185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4721653348019188014322123 7082480022028782021483185)
        ·
          refine ⟨5311860016521586516112389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7082480022028782021483185 5311860016521586516112389)
          ·
            refine ⟨995973753097797471771073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5311860016521586516112389 995973753097797471771073)
            ·
              refine ⟨746980314823348103828305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995973753097797471771073 746980314823348103828305)
              ·
                refine ⟨560235236117511077871229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746980314823348103828305 560235236117511077871229)
                ·
                  refine ⟨210088213544066654201711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560235236117511077871229 210088213544066654201711)
                  ·
                    rfl

theorem cell21_920577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 3].length) (baseStart_920577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920577 prefixEnd_920577 := by exact prefixLift 920577
  have htrace : WordTrace (prefixWord ++ tailWord_920577) baseStart_920577 baseEnd_920577 := by
    simpa [prefixWord, tailWord_920577, baseEnd_920577] using wordTrace_append hprefix tailTrace_920577
  have hstable : (prefixWord ++ tailWord_920577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920577).length < 2 ^ (prefixWord ++ tailWord_920577).sum := by decide
  have hdescent : baseEnd_920577 < baseStart_920577 := by decide
  rcases family_descends (prefixWord ++ tailWord_920577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920585 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 9]
def baseStart_920585 : Nat := 118140960795 + 920585 * 2 ^ 59
def prefixEnd_920585 : Nat := 4983230072969 + 3 ^ 40 * 920585 * 2
def baseEnd_920585 : Nat := 210090039253060418068361

theorem tailTrace_920585 : CollatzResearch.WordTrace tailWord_920585 prefixEnd_920585 210090039253060418068361 := by
  unfold tailWord_920585
  simp only [CollatzResearch.WordTrace]
  refine ⟨33576493369885243245915209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22384328913256828830610139 33576493369885243245915209)
  ·
    refine ⟨25182370027413932434436407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33576493369885243245915209 25182370027413932434436407)
    ·
      refine ⟨37773555041120898651654611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25182370027413932434436407 37773555041120898651654611)
      ·
        refine ⟨56660332561681347977481917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37773555041120898651654611 56660332561681347977481917)
        ·
          refine ⟨21247624710630505491555719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56660332561681347977481917 21247624710630505491555719)
          ·
            refine ⟨31871437065945758237333579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21247624710630505491555719 31871437065945758237333579)
            ·
              refine ⟨47807155598918637356000369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31871437065945758237333579 47807155598918637356000369)
              ·
                refine ⟨35855366699188978017000277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47807155598918637356000369 35855366699188978017000277)
                ·
                  refine ⟨210090039253060418068361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35855366699188978017000277 210090039253060418068361)
                  ·
                    rfl

theorem cell21_920585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_920585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920585 prefixEnd_920585 := by exact prefixLift 920585
  have htrace : WordTrace (prefixWord ++ tailWord_920585) baseStart_920585 baseEnd_920585 := by
    simpa [prefixWord, tailWord_920585, baseEnd_920585] using wordTrace_append hprefix tailTrace_920585
  have hstable : (prefixWord ++ tailWord_920585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920585).length < 2 ^ (prefixWord ++ tailWord_920585).sum := by decide
  have hdescent : baseEnd_920585 < baseStart_920585 := by decide
  rcases family_descends (prefixWord ++ tailWord_920585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920588 : List Nat := [2, 2, 1, 2, 3, 4, 1, 6]
def baseStart_920588 : Nat := 118140960795 + 920588 * 2 ^ 59
def prefixEnd_920588 : Nat := 4983230072969 + 3 ^ 40 * 920588 * 2
def baseEnd_920588 : Nat := 70030241297977693172785

theorem tailTrace_920588 : CollatzResearch.WordTrace tailWord_920588 prefixEnd_920588 70030241297977693172785 := by
  unfold tailWord_920588
  simp only [CollatzResearch.WordTrace]
  refine ⟨16788301394437187379137209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22384401859249583172182945 16788301394437187379137209)
  ·
    refine ⟨12591226045827890534352907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16788301394437187379137209 12591226045827890534352907)
    ·
      refine ⟨18886839068741835801529361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12591226045827890534352907 18886839068741835801529361)
      ·
        refine ⟨14165129301556376851147021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18886839068741835801529361 14165129301556376851147021)
        ·
          refine ⟨5311923488083641319180133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14165129301556376851147021 5311923488083641319180133)
          ·
            refine ⟨995985654015682747346275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5311923488083641319180133 995985654015682747346275)
            ·
              refine ⟨1493978481023524121019413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995985654015682747346275 1493978481023524121019413)
              ·
                refine ⟨70030241297977693172785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1493978481023524121019413 70030241297977693172785)
                ·
                  rfl

theorem cell21_920588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_920588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920588 prefixEnd_920588 := by exact prefixLift 920588
  have htrace : WordTrace (prefixWord ++ tailWord_920588) baseStart_920588 baseEnd_920588 := by
    simpa [prefixWord, tailWord_920588, baseEnd_920588] using wordTrace_append hprefix tailTrace_920588
  have hstable : (prefixWord ++ tailWord_920588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920588).length < 2 ^ (prefixWord ++ tailWord_920588).sum := by decide
  have hdescent : baseEnd_920588 < baseStart_920588 := by decide
  rcases family_descends (prefixWord ++ tailWord_920588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920602 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_920602 : Nat := 118140960795 + 920602 * 2 ^ 59
def prefixEnd_920602 : Nat := 4983230072969 + 3 ^ 40 * 920602 * 2
def baseEnd_920602 : Nat := 210093918884672166284993

theorem tailTrace_920602 : CollatzResearch.WordTrace tailWord_920602 prefixEnd_920602 210093918884672166284993 := by
  unfold tailWord_920602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8394278352705913787321015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22384742273882436766189373 8394278352705913787321015)
  ·
    refine ⟨12591417529058870680981523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8394278352705913787321015 12591417529058870680981523)
    ·
      refine ⟨18887126293588306021472285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12591417529058870680981523 18887126293588306021472285)
      ·
        refine ⟨7082672360095614758052107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18887126293588306021472285 7082672360095614758052107)
        ·
          refine ⟨10624008540143422137078161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7082672360095614758052107 10624008540143422137078161)
          ·
            refine ⟨7968006405107566602808621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10624008540143422137078161 7968006405107566602808621)
            ·
              refine ⟨2988002401915337476053233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7968006405107566602808621 2988002401915337476053233)
              ·
                refine ⟨2241001801436503107039925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2988002401915337476053233 2241001801436503107039925)
                ·
                  refine ⟨210093918884672166284993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2241001801436503107039925 210093918884672166284993)
                  ·
                    rfl

theorem cell21_920602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_920602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920602 prefixEnd_920602 := by exact prefixLift 920602
  have htrace : WordTrace (prefixWord ++ tailWord_920602) baseStart_920602 baseEnd_920602 := by
    simpa [prefixWord, tailWord_920602, baseEnd_920602] using wordTrace_append hprefix tailTrace_920602
  have hstable : (prefixWord ++ tailWord_920602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920602).length < 2 ^ (prefixWord ++ tailWord_920602).sum := by decide
  have hdescent : baseEnd_920602 < baseStart_920602 := by decide
  rcases family_descends (prefixWord ++ tailWord_920602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920605 : List Nat := [1, 4, 2, 2, 3, 1, 3, 5]
def baseStart_920605 : Nat := 118140960795 + 920605 * 2 ^ 59
def prefixEnd_920605 : Nat := 4983230072969 + 3 ^ 40 * 920605 * 2
def baseEnd_920605 : Nat := 70031534508514942578329

theorem tailTrace_920605 : CollatzResearch.WordTrace tailWord_920605 prefixEnd_920605 70031534508514942578329 := by
  unfold tailWord_920605
  simp only [CollatzResearch.WordTrace]
  refine ⟨33577222829812786661643269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22384815219875191107762179 33577222829812786661643269)
  ·
    refine ⟨6295729280589897499058113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33577222829812786661643269 6295729280589897499058113)
    ·
      refine ⟨4721796960442423124293585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6295729280589897499058113 4721796960442423124293585)
      ·
        refine ⟨3541347720331817343220189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4721796960442423124293585 3541347720331817343220189)
        ·
          refine ⟨1328005395124431503707571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3541347720331817343220189 1328005395124431503707571)
          ·
            refine ⟨1992008092686647255561357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328005395124431503707571 1992008092686647255561357)
            ·
              refine ⟨747003034757492720835509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1992008092686647255561357 747003034757492720835509)
              ·
                refine ⟨70031534508514942578329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 747003034757492720835509 70031534508514942578329)
                ·
                  rfl

theorem cell21_920605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 5].length) (baseStart_920605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920605 prefixEnd_920605 := by exact prefixLift 920605
  have htrace : WordTrace (prefixWord ++ tailWord_920605) baseStart_920605 baseEnd_920605 := by
    simpa [prefixWord, tailWord_920605, baseEnd_920605] using wordTrace_append hprefix tailTrace_920605
  have hstable : (prefixWord ++ tailWord_920605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920605).length < 2 ^ (prefixWord ++ tailWord_920605).sum := by decide
  have hdescent : baseEnd_920605 < baseStart_920605 := by decide
  rcases family_descends (prefixWord ++ tailWord_920605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920619 : List Nat := [1, 1, 1, 1, 2, 1, 8, 3, 3]
def baseStart_920619 : Nat := 118140960795 + 920619 * 2 ^ 59
def prefixEnd_920619 : Nat := 4983230072969 + 3 ^ 40 * 920619 * 2
def baseEnd_920619 : Nat := 210097798516283914501625

theorem tailTrace_920619 : CollatzResearch.WordTrace tailWord_920619 prefixEnd_920619 210097798516283914501625 := by
  unfold tailWord_920619
  simp only [CollatzResearch.WordTrace]
  refine ⟨33577733451762067052652911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22385155634508044701768607 33577733451762067052652911)
  ·
    refine ⟨50366600177643100578979367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33577733451762067052652911 50366600177643100578979367)
    ·
      refine ⟨75549900266464650868469051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50366600177643100578979367 75549900266464650868469051)
      ·
        refine ⟨113324850399696976302703577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75549900266464650868469051 113324850399696976302703577)
        ·
          refine ⟨84993637799772732227027683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113324850399696976302703577 84993637799772732227027683)
          ·
            refine ⟨127490456699659098340541525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84993637799772732227027683 127490456699659098340541525)
            ·
              refine ⟨1494028789449130058678221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 127490456699659098340541525 1494028789449130058678221)
              ·
                refine ⟨560260796043423772004333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1494028789449130058678221 560260796043423772004333)
                ·
                  refine ⟨210097798516283914501625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560260796043423772004333 210097798516283914501625)
                  ·
                    rfl

theorem cell21_920619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 3].length) (baseStart_920619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920619 prefixEnd_920619 := by exact prefixLift 920619
  have htrace : WordTrace (prefixWord ++ tailWord_920619) baseStart_920619 baseEnd_920619 := by
    simpa [prefixWord, tailWord_920619, baseEnd_920619] using wordTrace_append hprefix tailTrace_920619
  have hstable : (prefixWord ++ tailWord_920619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920619).length < 2 ^ (prefixWord ++ tailWord_920619).sum := by decide
  have hdescent : baseEnd_920619 < baseStart_920619 := by decide
  rcases family_descends (prefixWord ++ tailWord_920619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920633 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 6]
def baseStart_920633 : Nat := 118140960795 + 920633 * 2 ^ 59
def prefixEnd_920633 : Nat := 4983230072969 + 3 ^ 40 * 920633 * 2
def baseEnd_920633 : Nat := 210100993507023001268263

theorem tailTrace_920633 : CollatzResearch.WordTrace tailWord_920633 prefixEnd_920633 210100993507023001268263 := by
  unfold tailWord_920633
  simp only [CollatzResearch.WordTrace]
  refine ⟨33578244073711347443662553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22385496049140898295775035 33578244073711347443662553)
  ·
    refine ⟨25183683055283510582746915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33578244073711347443662553 25183683055283510582746915)
    ·
      refine ⟨37775524582925265874120373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25183683055283510582746915 37775524582925265874120373)
      ·
        refine ⟨3541455429649243675698785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37775524582925265874120373 3541455429649243675698785)
        ·
          refine ⟨2656091572236932756774089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3541455429649243675698785 2656091572236932756774089)
          ·
            refine ⟨1992068679177699567580567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2656091572236932756774089 1992068679177699567580567)
            ·
              refine ⟨2988103018766549351370851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992068679177699567580567 2988103018766549351370851)
              ·
                refine ⟨4482154528149824027056277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988103018766549351370851 4482154528149824027056277)
                ·
                  refine ⟨210100993507023001268263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4482154528149824027056277 210100993507023001268263)
                  ·
                    rfl

theorem cell21_920633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_920633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920633 prefixEnd_920633 := by exact prefixLift 920633
  have htrace : WordTrace (prefixWord ++ tailWord_920633) baseStart_920633 baseEnd_920633 := by
    simpa [prefixWord, tailWord_920633, baseEnd_920633] using wordTrace_append hprefix tailTrace_920633
  have hstable : (prefixWord ++ tailWord_920633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920633).length < 2 ^ (prefixWord ++ tailWord_920633).sum := by decide
  have hdescent : baseEnd_920633 < baseStart_920633 := by decide
  rcases family_descends (prefixWord ++ tailWord_920633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920670 : List Nat := [4, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_920670 : Nat := 118140960795 + 920670 * 2 ^ 59
def prefixEnd_920670 : Nat := 4983230072969 + 3 ^ 40 * 920670 * 2
def baseEnd_920670 : Nat := 210109437411119159151521

theorem tailTrace_920670 : CollatzResearch.WordTrace tailWord_920670 prefixEnd_920670 210109437411119159151521 := by
  unfold tailWord_920670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4197449196822162845344933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22386395716384868508506309 4197449196822162845344933)
  ·
    refine ⟨787021724404155533502175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4197449196822162845344933 787021724404155533502175)
    ·
      refine ⟨1180532586606233300253263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787021724404155533502175 1180532586606233300253263)
      ·
        refine ⟨1770798879909349950379895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180532586606233300253263 1770798879909349950379895)
        ·
          refine ⟨2656198319864024925569843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770798879909349950379895 2656198319864024925569843)
          ·
            refine ⟨3984297479796037388354765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656198319864024925569843 3984297479796037388354765)
            ·
              refine ⟨1494111554923514020633037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3984297479796037388354765 1494111554923514020633037)
              ·
                refine ⟨560291833096317757737389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1494111554923514020633037 560291833096317757737389)
                ·
                  refine ⟨210109437411119159151521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560291833096317757737389 210109437411119159151521)
                  ·
                    rfl

theorem cell21_920670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_920670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920670 prefixEnd_920670 := by exact prefixLift 920670
  have htrace : WordTrace (prefixWord ++ tailWord_920670) baseStart_920670 baseEnd_920670 := by
    simpa [prefixWord, tailWord_920670, baseEnd_920670] using wordTrace_append hprefix tailTrace_920670
  have hstable : (prefixWord ++ tailWord_920670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920670).length < 2 ^ (prefixWord ++ tailWord_920670).sum := by decide
  have hdescent : baseEnd_920670 < baseStart_920670 := by decide
  rcases family_descends (prefixWord ++ tailWord_920670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
