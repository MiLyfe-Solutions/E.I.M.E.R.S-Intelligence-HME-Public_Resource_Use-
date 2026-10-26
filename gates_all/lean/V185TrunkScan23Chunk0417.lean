import V185TrunkScan23Chunk0416

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2464907 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 1, 4, 2]
def baseStart_2464907 : Nat := 118140960795 + 2464907 * 2 ^ 59
def prefixEnd_2464907 : Nat := 4983230072969 + 3 ^ 40 * 2464907 * 2
def baseEnd_2464907 : Nat := 1265682059632092773726605

theorem tailTrace_2464907 : CollatzResearch.WordTrace tailWord_2464907 prefixEnd_2464907 1265682059632092773726605 := by
  unfold tailWord_2464907
  simp only [CollatzResearch.WordTrace]
  refine ⟨89902544081070386445368975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59935029387380257630245983 89902544081070386445368975)
  ·
    refine ⟨134853816121605579668053463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89902544081070386445368975 134853816121605579668053463)
    ·
      refine ⟨202280724182408369502080195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134853816121605579668053463 202280724182408369502080195)
      ·
        refine ⟨303421086273612554253120293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202280724182408369502080195 303421086273612554253120293)
        ·
          refine ⟨56891453676302353922460055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 303421086273612554253120293 56891453676302353922460055)
          ·
            refine ⟨85337180514453530883690083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56891453676302353922460055 85337180514453530883690083)
            ·
              refine ⟨128005770771680296325535125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85337180514453530883690083 128005770771680296325535125)
              ·
                refine ⟨6000270504922513890259459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128005770771680296325535125 6000270504922513890259459)
                ·
                  refine ⟨9000405757383770835389189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6000270504922513890259459 9000405757383770835389189)
                  ·
                    refine ⟨1687576079509457031635473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9000405757383770835389189 1687576079509457031635473)
                    ·
                      refine ⟨1265682059632092773726605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1687576079509457031635473 1265682059632092773726605)
                      ·
                        rfl

theorem cell23_2464907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 4, 2].length) (baseStart_2464907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464907 prefixEnd_2464907 := by exact prefixLift 2464907
  have htrace : WordTrace (prefixWord ++ tailWord_2464907) baseStart_2464907 baseEnd_2464907 := by
    simpa [prefixWord, tailWord_2464907, baseEnd_2464907] using wordTrace_append hprefix tailTrace_2464907
  have hstable : (prefixWord ++ tailWord_2464907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464907).length < 2 ^ (prefixWord ++ tailWord_2464907).sum := by decide
  have hdescent : baseEnd_2464907 < baseStart_2464907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464962 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_2464962 : Nat := 118140960795 + 2464962 * 2 ^ 59
def prefixEnd_2464962 : Nat := 4983230072969 + 3 ^ 40 * 2464962 * 2
def baseEnd_2464962 : Nat := 1265710301068090058538853

theorem tailTrace_2464962 : CollatzResearch.WordTrace tailWord_2464962 prefixEnd_2464962 1265710301068090058538853 := by
  unfold tailWord_2464962
  simp only [CollatzResearch.WordTrace]
  refine ⟨22476137523967782709655285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59936366730580753892414093 22476137523967782709655285)
  ·
    refine ⟨2107137892871979629030183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22476137523967782709655285 2107137892871979629030183)
    ·
      refine ⟨3160706839307969443545275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2107137892871979629030183 3160706839307969443545275)
      ·
        refine ⟨4741060258961954165317913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3160706839307969443545275 4741060258961954165317913)
        ·
          refine ⟨3555795194221465623988435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4741060258961954165317913 3555795194221465623988435)
          ·
            refine ⟨5333692791332198435982653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3555795194221465623988435 5333692791332198435982653)
            ·
              refine ⟨2000134796749574413493495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5333692791332198435982653 2000134796749574413493495)
              ·
                refine ⟨3000202195124361620240243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2000134796749574413493495 3000202195124361620240243)
                ·
                  refine ⟨4500303292686542430360365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000202195124361620240243 4500303292686542430360365)
                  ·
                    refine ⟨1687613734757453411385137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4500303292686542430360365 1687613734757453411385137)
                    ·
                      refine ⟨1265710301068090058538853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1687613734757453411385137 1265710301068090058538853)
                      ·
                        rfl

theorem cell23_2464962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_2464962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464962 prefixEnd_2464962 := by exact prefixLift 2464962
  have htrace : WordTrace (prefixWord ++ tailWord_2464962) baseStart_2464962 baseEnd_2464962 := by
    simpa [prefixWord, tailWord_2464962, baseEnd_2464962] using wordTrace_append hprefix tailTrace_2464962
  have hstable : (prefixWord ++ tailWord_2464962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464962).length < 2 ^ (prefixWord ++ tailWord_2464962).sum := by decide
  have hdescent : baseEnd_2464962 < baseStart_2464962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464967 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 4, 5, 2]
def baseStart_2464967 : Nat := 118140960795 + 2464967 * 2 ^ 59
def prefixEnd_2464967 : Nat := 4983230072969 + 3 ^ 40 * 2464967 * 2
def baseEnd_2464967 : Nat := 1265712868471362538976329

theorem tailTrace_2464967 : CollatzResearch.WordTrace tailWord_2464967 prefixEnd_2464967 1265712868471362538976329 := by
  unfold tailWord_2464967
  simp only [CollatzResearch.WordTrace]
  refine ⟨89904732460853016692553155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59936488307235344461702103 89904732460853016692553155)
  ·
    refine ⟨134857098691279525038829733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89904732460853016692553155 134857098691279525038829733)
    ·
      refine ⟨25285706004614910944780575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134857098691279525038829733 25285706004614910944780575)
      ·
        refine ⟨37928559006922366417170863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25285706004614910944780575 37928559006922366417170863)
        ·
          refine ⟨56892838510383549625756295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37928559006922366417170863 56892838510383549625756295)
          ·
            refine ⟨85339257765575324438634443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56892838510383549625756295 85339257765575324438634443)
            ·
              refine ⟨128008886648362986657951665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85339257765575324438634443 128008886648362986657951665)
              ·
                refine ⟨96006664986272239993463749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128008886648362986657951665 96006664986272239993463749)
                ·
                  refine ⟨18001249684926044998774453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96006664986272239993463749 18001249684926044998774453)
                  ·
                    refine ⟨1687617157961816718635105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18001249684926044998774453 1687617157961816718635105)
                    ·
                      refine ⟨1265712868471362538976329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1687617157961816718635105 1265712868471362538976329)
                      ·
                        rfl

theorem cell23_2464967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_2464967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464967 prefixEnd_2464967 := by exact prefixLift 2464967
  have htrace : WordTrace (prefixWord ++ tailWord_2464967) baseStart_2464967 baseEnd_2464967 := by
    simpa [prefixWord, tailWord_2464967, baseEnd_2464967] using wordTrace_append hprefix tailTrace_2464967
  have hstable : (prefixWord ++ tailWord_2464967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464967).length < 2 ^ (prefixWord ++ tailWord_2464967).sum := by decide
  have hdescent : baseEnd_2464967 < baseStart_2464967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464981 : List Nat := [1, 3, 2, 4, 1, 1, 4, 2, 5]
def baseStart_2464981 : Nat := 118140960795 + 2464981 * 2 ^ 59
def prefixEnd_2464981 : Nat := 4983230072969 + 3 ^ 40 * 2464981 * 2
def baseEnd_2464981 : Nat := 140635561911169498244585

theorem tailTrace_2464981 : CollatzResearch.WordTrace tailWord_2464981 prefixEnd_2464981 140635561911169498244585 := by
  unfold tailWord_2464981
  simp only [CollatzResearch.WordTrace]
  refine ⟨89905243082802297083562797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59936828721868198055708531 89905243082802297083562797)
  ·
    refine ⟨33714466156050861406336049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89905243082802297083562797 33714466156050861406336049)
    ·
      refine ⟨25285849617038146054752037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33714466156050861406336049 25285849617038146054752037)
      ·
        refine ⟨4741096803194652385266007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25285849617038146054752037 4741096803194652385266007)
        ·
          refine ⟨7111645204791978577899011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4741096803194652385266007 7111645204791978577899011)
          ·
            refine ⟨10667467807187967866848517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7111645204791978577899011 10667467807187967866848517)
            ·
              refine ⟨2000150213847743975034097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10667467807187967866848517 2000150213847743975034097)
              ·
                refine ⟨1500112660385807981275573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2000150213847743975034097 1500112660385807981275573)
                ·
                  refine ⟨140635561911169498244585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1500112660385807981275573 140635561911169498244585)
                  ·
                    rfl

theorem cell23_2464981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_2464981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464981 prefixEnd_2464981 := by exact prefixLift 2464981
  have htrace : WordTrace (prefixWord ++ tailWord_2464981) baseStart_2464981 baseEnd_2464981 := by
    simpa [prefixWord, tailWord_2464981, baseEnd_2464981] using wordTrace_append hprefix tailTrace_2464981
  have hstable : (prefixWord ++ tailWord_2464981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464981).length < 2 ^ (prefixWord ++ tailWord_2464981).sum := by decide
  have hdescent : baseEnd_2464981 < baseStart_2464981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465014 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_2465014 : Nat := 118140960795 + 2465014 * 2 ^ 59
def prefixEnd_2465014 : Nat := 4983230072969 + 3 ^ 40 * 2465014 * 2
def baseEnd_2465014 : Nat := 1265737002062123855088613

theorem tailTrace_2465014 : CollatzResearch.WordTrace tailWord_2465014 prefixEnd_2465014 1265737002062123855088613 := by
  unfold tailWord_2465014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5619152918230171482469631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59937631127788495813009397 5619152918230171482469631)
  ·
    refine ⟨8428729377345257223704447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5619152918230171482469631 8428729377345257223704447)
    ·
      refine ⟨12643094066017885835556671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8428729377345257223704447 12643094066017885835556671)
      ·
        refine ⟨18964641099026828753335007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12643094066017885835556671 18964641099026828753335007)
        ·
          refine ⟨28446961648540243130002511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18964641099026828753335007 28446961648540243130002511)
          ·
            refine ⟨42670442472810364695003767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28446961648540243130002511 42670442472810364695003767)
            ·
              refine ⟨64005663709215547042505651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42670442472810364695003767 64005663709215547042505651)
              ·
                refine ⟨96008495563823320563758477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64005663709215547042505651 96008495563823320563758477)
                ·
                  refine ⟨36003185836433745211409429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96008495563823320563758477 36003185836433745211409429)
                  ·
                    refine ⟨1687649336082831806784817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36003185836433745211409429 1687649336082831806784817)
                    ·
                      refine ⟨1265737002062123855088613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1687649336082831806784817 1265737002062123855088613)
                      ·
                        rfl

theorem cell23_2465014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_2465014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465014 prefixEnd_2465014 := by exact prefixLift 2465014
  have htrace : WordTrace (prefixWord ++ tailWord_2465014) baseStart_2465014 baseEnd_2465014 := by
    simpa [prefixWord, tailWord_2465014, baseEnd_2465014] using wordTrace_append hprefix tailTrace_2465014
  have hstable : (prefixWord ++ tailWord_2465014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465014).length < 2 ^ (prefixWord ++ tailWord_2465014).sum := by decide
  have hdescent : baseEnd_2465014 < baseStart_2465014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465017 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 1, 4, 3]
def baseStart_2465017 : Nat := 118140960795 + 2465017 * 2 ^ 59
def prefixEnd_2465017 : Nat := 4983230072969 + 3 ^ 40 * 2465017 * 2
def baseEnd_2465017 : Nat := 1265738542504087343351099

theorem tailTrace_2465017 : CollatzResearch.WordTrace tailWord_2465017 prefixEnd_2465017 1265738542504087343351099 := by
  unfold tailWord_2465017
  simp only [CollatzResearch.WordTrace]
  refine ⟨89906556110671875231873305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59937704073781250154582203 89906556110671875231873305)
  ·
    refine ⟨67429917083003906423904979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89906556110671875231873305 67429917083003906423904979)
    ·
      refine ⟨101144875624505859635857469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67429917083003906423904979 101144875624505859635857469)
      ·
        refine ⟨37929328359189697363446551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101144875624505859635857469 37929328359189697363446551)
        ·
          refine ⟨56893992538784546045169827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37929328359189697363446551 56893992538784546045169827)
          ·
            refine ⟨85340988808176819067754741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56893992538784546045169827 85340988808176819067754741)
            ·
              refine ⟨8000717700766576787602007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85340988808176819067754741 8000717700766576787602007)
              ·
                refine ⟨12001076551149865181403011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8000717700766576787602007 12001076551149865181403011)
                ·
                  refine ⟨18001614826724797772104517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12001076551149865181403011 18001614826724797772104517)
                  ·
                    refine ⟨3375302780010899582269597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18001614826724797772104517 3375302780010899582269597)
                    ·
                      refine ⟨1265738542504087343351099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3375302780010899582269597 1265738542504087343351099)
                      ·
                        rfl

theorem cell23_2465017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_2465017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465017 prefixEnd_2465017 := by exact prefixLift 2465017
  have htrace : WordTrace (prefixWord ++ tailWord_2465017) baseStart_2465017 baseEnd_2465017 := by
    simpa [prefixWord, tailWord_2465017, baseEnd_2465017] using wordTrace_append hprefix tailTrace_2465017
  have hstable : (prefixWord ++ tailWord_2465017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465017).length < 2 ^ (prefixWord ++ tailWord_2465017).sum := by decide
  have hdescent : baseEnd_2465017 < baseStart_2465017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465084 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 1, 5]
def baseStart_2465084 : Nat := 118140960795 + 2465084 * 2 ^ 59
def prefixEnd_2465084 : Nat := 4983230072969 + 3 ^ 40 * 2465084 * 2
def baseEnd_2465084 : Nat := 421924315235979527071097

theorem tailTrace_2465084 : CollatzResearch.WordTrace tailWord_2465084 prefixEnd_2465084 421924315235979527071097 := by
  unfold tailWord_2465084
  simp only [CollatzResearch.WordTrace]
  refine ⟨44954499900714572837281153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59939333200952763783041537 44954499900714572837281153)
  ·
    refine ⟨33715874925535929627960865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44954499900714572837281153 33715874925535929627960865)
    ·
      refine ⟨25286906194151947220970649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33715874925535929627960865 25286906194151947220970649)
      ·
        refine ⟨18965179645613960415727987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25286906194151947220970649 18965179645613960415727987)
        ·
          refine ⟨28447769468420940623591981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18965179645613960415727987 28447769468420940623591981)
          ·
            refine ⟨10667913550657852733846993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28447769468420940623591981 10667913550657852733846993)
            ·
              refine ⟨8000935162993389550385245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10667913550657852733846993 8000935162993389550385245)
              ·
                refine ⟨3000350686122521081394467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8000935162993389550385245 3000350686122521081394467)
                ·
                  refine ⟨4500526029183781622091701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000350686122521081394467 4500526029183781622091701)
                  ·
                    refine ⟨421924315235979527071097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4500526029183781622091701 421924315235979527071097)
                    ·
                      rfl

theorem cell23_2465084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_2465084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465084 prefixEnd_2465084 := by exact prefixLift 2465084
  have htrace : WordTrace (prefixWord ++ tailWord_2465084) baseStart_2465084 baseEnd_2465084 := by
    simpa [prefixWord, tailWord_2465084, baseEnd_2465084] using wordTrace_append hprefix tailTrace_2465084
  have hstable : (prefixWord ++ tailWord_2465084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465084).length < 2 ^ (prefixWord ++ tailWord_2465084).sum := by decide
  have hdescent : baseEnd_2465084 < baseStart_2465084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465107 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 5]
def baseStart_2465107 : Nat := 118140960795 + 2465107 * 2 ^ 59
def prefixEnd_2465107 : Nat := 4983230072969 + 3 ^ 40 * 2465107 * 2
def baseEnd_2465107 : Nat := 1265784755762991991225685

theorem tailTrace_2465107 : CollatzResearch.WordTrace tailWord_2465107 prefixEnd_2465107 1265784755762991991225685 := by
  unfold tailWord_2465107
  simp only [CollatzResearch.WordTrace]
  refine ⟨89909838680345820602649575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59939892453563880401766383 89909838680345820602649575)
  ·
    refine ⟨134864758020518730903974363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89909838680345820602649575 134864758020518730903974363)
    ·
      refine ⟨202297137030778096355961545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134864758020518730903974363 202297137030778096355961545)
      ·
        refine ⟨151722852773083572266971159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202297137030778096355961545 151722852773083572266971159)
        ·
          refine ⟨227584279159625358400456739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151722852773083572266971159 227584279159625358400456739)
          ·
            refine ⟨341376418739438037600685109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227584279159625358400456739 341376418739438037600685109)
            ·
              refine ⟨32004039256822316025064229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 341376418739438037600685109 32004039256822316025064229)
              ·
                refine ⟨6000757360654184254699543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32004039256822316025064229 6000757360654184254699543)
                ·
                  refine ⟨9001136040981276382049315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6000757360654184254699543 9001136040981276382049315)
                  ·
                    refine ⟨13501704061471914573073973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9001136040981276382049315 13501704061471914573073973)
                    ·
                      refine ⟨1265784755762991991225685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13501704061471914573073973 1265784755762991991225685)
                      ·
                        rfl

theorem cell23_2465107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_2465107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465107 prefixEnd_2465107 := by exact prefixLift 2465107
  have htrace : WordTrace (prefixWord ++ tailWord_2465107) baseStart_2465107 baseEnd_2465107 := by
    simpa [prefixWord, tailWord_2465107, baseEnd_2465107] using wordTrace_append hprefix tailTrace_2465107
  have hstable : (prefixWord ++ tailWord_2465107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465107).length < 2 ^ (prefixWord ++ tailWord_2465107).sum := by decide
  have hdescent : baseEnd_2465107 < baseStart_2465107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465121 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 3, 2, 2]
def baseStart_2465121 : Nat := 118140960795 + 2465121 * 2 ^ 59
def prefixEnd_2465121 : Nat := 4983230072969 + 3 ^ 40 * 2465121 * 2
def baseEnd_2465121 : Nat := 1265791944492154936450621

theorem tailTrace_2465121 : CollatzResearch.WordTrace tailWord_2465121 prefixEnd_2465121 1265791944492154936450621 := by
  unfold tailWord_2465121
  simp only [CollatzResearch.WordTrace]
  refine ⟨89910349302295100993659217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59940232868196733995772811 89910349302295100993659217)
  ·
    refine ⟨67432761976721325745244413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89910349302295100993659217 67432761976721325745244413)
    ·
      refine ⟨25287285741270497154466655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67432761976721325745244413 25287285741270497154466655)
      ·
        refine ⟨37930928611905745731699983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25287285741270497154466655 37930928611905745731699983)
        ·
          refine ⟨56896392917858618597549975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37930928611905745731699983 56896392917858618597549975)
          ·
            refine ⟨85344589376787927896324963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56896392917858618597549975 85344589376787927896324963)
            ·
              refine ⟨128016884065181891844487445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85344589376787927896324963 128016884065181891844487445)
              ·
                refine ⟨6000791440555401180210349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128016884065181891844487445 6000791440555401180210349)
                ·
                  refine ⟨2250296790208275442578881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6000791440555401180210349 2250296790208275442578881)
                  ·
                    refine ⟨1687722592656206581934161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2250296790208275442578881 1687722592656206581934161)
                    ·
                      refine ⟨1265791944492154936450621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1687722592656206581934161 1265791944492154936450621)
                      ·
                        rfl

theorem cell23_2465121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_2465121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465121 prefixEnd_2465121 := by exact prefixLift 2465121
  have htrace : WordTrace (prefixWord ++ tailWord_2465121) baseStart_2465121 baseEnd_2465121 := by
    simpa [prefixWord, tailWord_2465121, baseEnd_2465121] using wordTrace_append hprefix tailTrace_2465121
  have hstable : (prefixWord ++ tailWord_2465121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465121).length < 2 ^ (prefixWord ++ tailWord_2465121).sum := by decide
  have hdescent : baseEnd_2465121 < baseStart_2465121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465155 : List Nat := [1, 1, 1, 3, 5, 2, 1, 4, 1, 2, 2]
def baseStart_2465155 : Nat := 118140960795 + 2465155 * 2 ^ 59
def prefixEnd_2465155 : Nat := 4983230072969 + 3 ^ 40 * 2465155 * 2
def baseEnd_2465155 : Nat := 1265809402834407803425465

theorem tailTrace_2465155 : CollatzResearch.WordTrace tailWord_2465155 prefixEnd_2465155 1265809402834407803425465 := by
  unfold tailWord_2465155
  simp only [CollatzResearch.WordTrace]
  refine ⟨89911589384171924800396919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59941059589447949866931279 89911589384171924800396919)
  ·
    refine ⟨134867384076257887200595379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89911589384171924800396919 134867384076257887200595379)
    ·
      refine ⟨202301076114386830800893069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134867384076257887200595379 202301076114386830800893069)
      ·
        refine ⟨75862903542895061550334901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202301076114386830800893069 75862903542895061550334901)
        ·
          refine ⟨7112147207146412020343897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75862903542895061550334901 7112147207146412020343897)
          ·
            refine ⟨5334110405359809015257923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7112147207146412020343897 5334110405359809015257923)
            ·
              refine ⟨8001165608039713522886885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5334110405359809015257923 8001165608039713522886885)
              ·
                refine ⟨1500218551507446285541291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8001165608039713522886885 1500218551507446285541291)
                ·
                  refine ⟨2250327827261169428311937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500218551507446285541291 2250327827261169428311937)
                  ·
                    refine ⟨1687745870445877071233953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2250327827261169428311937 1687745870445877071233953)
                    ·
                      refine ⟨1265809402834407803425465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1687745870445877071233953 1265809402834407803425465)
                      ·
                        rfl

theorem cell23_2465155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 1, 2, 2].length) (baseStart_2465155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465155 prefixEnd_2465155 := by exact prefixLift 2465155
  have htrace : WordTrace (prefixWord ++ tailWord_2465155) baseStart_2465155 baseEnd_2465155 := by
    simpa [prefixWord, tailWord_2465155, baseEnd_2465155] using wordTrace_append hprefix tailTrace_2465155
  have hstable : (prefixWord ++ tailWord_2465155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465155).length < 2 ^ (prefixWord ++ tailWord_2465155).sum := by decide
  have hdescent : baseEnd_2465155 < baseStart_2465155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465157 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_2465157 : Nat := 118140960795 + 2465157 * 2 ^ 59
def prefixEnd_2465157 : Nat := 4983230072969 + 3 ^ 40 * 2465157 * 2
def baseEnd_2465157 : Nat := 421936809931905598533485

theorem tailTrace_2465157 : CollatzResearch.WordTrace tailWord_2465157 prefixEnd_2465157 421936809931905598533485 := by
  unfold tailWord_2465157
  simp only [CollatzResearch.WordTrace]
  refine ⟨89911662330164679141969725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59941108220109786094646483 89911662330164679141969725)
  ·
    refine ⟨33716873373811754678238647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89911662330164679141969725 33716873373811754678238647)
    ·
      refine ⟨50575310060717632017357971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33716873373811754678238647 50575310060717632017357971)
      ·
        refine ⟨75862965091076448026036957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50575310060717632017357971 75862965091076448026036957)
        ·
          refine ⟨28448611909153668009763859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75862965091076448026036957 28448611909153668009763859)
          ·
            refine ⟨42672917863730502014645789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28448611909153668009763859 42672917863730502014645789)
            ·
              refine ⟨16002344198898938255492171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42672917863730502014645789 16002344198898938255492171)
              ·
                refine ⟨24003516298348407383238257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16002344198898938255492171 24003516298348407383238257)
                ·
                  refine ⟨18002637223761305537428693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24003516298348407383238257 18002637223761305537428693)
                  ·
                    refine ⟨421936809931905598533485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18002637223761305537428693 421936809931905598533485)
                    ·
                      rfl

theorem cell23_2465157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_2465157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465157 prefixEnd_2465157 := by exact prefixLift 2465157
  have htrace : WordTrace (prefixWord ++ tailWord_2465157) baseStart_2465157 baseEnd_2465157 := by
    simpa [prefixWord, tailWord_2465157, baseEnd_2465157] using wordTrace_append hprefix tailTrace_2465157
  have hstable : (prefixWord ++ tailWord_2465157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465157).length < 2 ^ (prefixWord ++ tailWord_2465157).sum := by decide
  have hdescent : baseEnd_2465157 < baseStart_2465157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465161 : List Nat := [1, 2, 1, 1, 8, 1, 1, 8]
def baseStart_2465161 : Nat := 118140960795 + 2465161 * 2 ^ 59
def prefixEnd_2465161 : Nat := 4983230072969 + 3 ^ 40 * 2465161 * 2
def baseEnd_2465161 : Nat := 46881943841419806664831

theorem tailTrace_2465161 : CollatzResearch.WordTrace tailWord_2465161 prefixEnd_2465161 46881943841419806664831 := by
  unfold tailWord_2465161
  simp only [CollatzResearch.WordTrace]
  refine ⟨89911808222150187825115337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59941205481433458550076891 89911808222150187825115337)
  ·
    refine ⟨67433856166612640868836503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89911808222150187825115337 67433856166612640868836503)
    ·
      refine ⟨101150784249918961303254755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67433856166612640868836503 101150784249918961303254755)
      ·
        refine ⟨151726176374878441954882133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101150784249918961303254755 151726176374878441954882133)
        ·
          refine ⟨1778041129393106741658775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 151726176374878441954882133 1778041129393106741658775)
          ·
            refine ⟨2667061694089660112488163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778041129393106741658775 2667061694089660112488163)
            ·
              refine ⟨4000592541134490168732245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2667061694089660112488163 4000592541134490168732245)
              ·
                refine ⟨46881943841419806664831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4000592541134490168732245 46881943841419806664831)
                ·
                  rfl

theorem cell23_2465161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 8].length) (baseStart_2465161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465161 prefixEnd_2465161 := by exact prefixLift 2465161
  have htrace : WordTrace (prefixWord ++ tailWord_2465161) baseStart_2465161 baseEnd_2465161 := by
    simpa [prefixWord, tailWord_2465161, baseEnd_2465161] using wordTrace_append hprefix tailTrace_2465161
  have hstable : (prefixWord ++ tailWord_2465161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465161).length < 2 ^ (prefixWord ++ tailWord_2465161).sum := by decide
  have hdescent : baseEnd_2465161 < baseStart_2465161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465187 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 1, 8]
def baseStart_2465187 : Nat := 118140960795 + 2465187 * 2 ^ 59
def prefixEnd_2465187 : Nat := 4983230072969 + 3 ^ 40 * 2465187 * 2
def baseEnd_2465187 : Nat := 421941944738450559408439

theorem tailTrace_2465187 : CollatzResearch.WordTrace tailWord_2465187 prefixEnd_2465187 421941944738450559408439 := by
  unfold tailWord_2465187
  simp only [CollatzResearch.WordTrace]
  refine ⟨89912756520055994265561815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59941837680037329510374543 89912756520055994265561815)
  ·
    refine ⟨134869134780083991398342723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89912756520055994265561815 134869134780083991398342723)
    ·
      refine ⟨202303702170125987097514085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134869134780083991398342723 202303702170125987097514085)
      ·
        refine ⟨37931944156898622580783891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202303702170125987097514085 37931944156898622580783891)
        ·
          refine ⟨56897916235347933871175837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37931944156898622580783891 56897916235347933871175837)
          ·
            refine ⟨21336718588255475201690939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56897916235347933871175837 21336718588255475201690939)
            ·
              refine ⟨32005077882383212802536409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21336718588255475201690939 32005077882383212802536409)
              ·
                refine ⟨24003808411787409601902307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32005077882383212802536409 24003808411787409601902307)
                ·
                  refine ⟨36005712617681114402853461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24003808411787409601902307 36005712617681114402853461)
                  ·
                    refine ⟨421941944738450559408439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36005712617681114402853461 421941944738450559408439)
                    ·
                      rfl

theorem cell23_2465187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 8].length) (baseStart_2465187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465187 prefixEnd_2465187 := by exact prefixLift 2465187
  have htrace : WordTrace (prefixWord ++ tailWord_2465187) baseStart_2465187 baseEnd_2465187 := by
    simpa [prefixWord, tailWord_2465187, baseEnd_2465187] using wordTrace_append hprefix tailTrace_2465187
  have hstable : (prefixWord ++ tailWord_2465187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465187).length < 2 ^ (prefixWord ++ tailWord_2465187).sum := by decide
  have hdescent : baseEnd_2465187 < baseStart_2465187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465192 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_2465192 : Nat := 118140960795 + 2465192 * 2 ^ 59
def prefixEnd_2465192 : Nat := 4983230072969 + 3 ^ 40 * 2465192 * 2
def baseEnd_2465192 : Nat := 1265828401618624158662795

theorem tailTrace_2465192 : CollatzResearch.WordTrace tailWord_2465192 prefixEnd_2465192 1265828401618624158662795 := by
  unfold tailWord_2465192
  simp only [CollatzResearch.WordTrace]
  refine ⟨44956469442518940059746915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59941959256691920079662553 44956469442518940059746915)
  ·
    refine ⟨67434704163778410089620373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44956469442518940059746915 67434704163778410089620373)
    ·
      refine ⟨3161001757677112972950955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67434704163778410089620373 3161001757677112972950955)
      ·
        refine ⟨4741502636515669459426433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3161001757677112972950955 4741502636515669459426433)
        ·
          refine ⟨3556126977386752094569825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4741502636515669459426433 3556126977386752094569825)
          ·
            refine ⟨2667095233040064070927369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3556126977386752094569825 2667095233040064070927369)
            ·
              refine ⟨2000321424780048053195527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2667095233040064070927369 2000321424780048053195527)
              ·
                refine ⟨3000482137170072079793291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2000321424780048053195527 3000482137170072079793291)
                ·
                  refine ⟨4500723205755108119689937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000482137170072079793291 4500723205755108119689937)
                  ·
                    refine ⟨3375542404316331089767453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4500723205755108119689937 3375542404316331089767453)
                    ·
                      refine ⟨1265828401618624158662795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3375542404316331089767453 1265828401618624158662795)
                      ·
                        rfl

theorem cell23_2465192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_2465192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465192 prefixEnd_2465192 := by exact prefixLift 2465192
  have htrace : WordTrace (prefixWord ++ tailWord_2465192) baseStart_2465192 baseEnd_2465192 := by
    simpa [prefixWord, tailWord_2465192, baseEnd_2465192] using wordTrace_append hprefix tailTrace_2465192
  have hstable : (prefixWord ++ tailWord_2465192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465192).length < 2 ^ (prefixWord ++ tailWord_2465192).sum := by decide
  have hdescent : baseEnd_2465192 < baseStart_2465192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465205 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_2465205 : Nat := 118140960795 + 2465205 * 2 ^ 59
def prefixEnd_2465205 : Nat := 4983230072969 + 3 ^ 40 * 2465205 * 2
def baseEnd_2465205 : Nat := 1265835076867132607800235

theorem tailTrace_2465205 : CollatzResearch.WordTrace tailWord_2465205 prefixEnd_2465205 1265835076867132607800235 := by
  unfold tailWord_2465205
  simp only [CollatzResearch.WordTrace]
  refine ⟨89913413033990783339717069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59942275355993855559811379 89913413033990783339717069)
  ·
    refine ⟨33717529887746543752393901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89913413033990783339717069 33717529887746543752393901)
    ·
      refine ⟨12644073707904953907147713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33717529887746543752393901 12644073707904953907147713)
      ·
        refine ⟨9483055280928715430360785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12644073707904953907147713 9483055280928715430360785)
        ·
          refine ⟨7112291460696536572770589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9483055280928715430360785 7112291460696536572770589)
          ·
            refine ⟨2667109297761201214788971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7112291460696536572770589 2667109297761201214788971)
            ·
              refine ⟨4000663946641801822183457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2667109297761201214788971 4000663946641801822183457)
              ·
                refine ⟨3000497959981351366637593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4000663946641801822183457 3000497959981351366637593)
                ·
                  refine ⟨2250373469986013524978195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3000497959981351366637593 2250373469986013524978195)
                  ·
                    refine ⟨3375560204979020287467293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2250373469986013524978195 3375560204979020287467293)
                    ·
                      refine ⟨1265835076867132607800235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3375560204979020287467293 1265835076867132607800235)
                      ·
                        rfl

theorem cell23_2465205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_2465205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465205 prefixEnd_2465205 := by exact prefixLift 2465205
  have htrace : WordTrace (prefixWord ++ tailWord_2465205) baseStart_2465205 baseEnd_2465205 := by
    simpa [prefixWord, tailWord_2465205, baseEnd_2465205] using wordTrace_append hprefix tailTrace_2465205
  have hstable : (prefixWord ++ tailWord_2465205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465205).length < 2 ^ (prefixWord ++ tailWord_2465205).sum := by decide
  have hdescent : baseEnd_2465205 < baseStart_2465205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465214 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_2465214 : Nat := 118140960795 + 2465214 * 2 ^ 59
def prefixEnd_2465214 : Nat := 4983230072969 + 3 ^ 40 * 2465214 * 2
def baseEnd_2465214 : Nat := 1265839698193023072587693

theorem tailTrace_2465214 : CollatzResearch.WordTrace tailWord_2465214 prefixEnd_2465214 1265839698193023072587693 := by
  unfold tailWord_2465214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11239217661369772234599337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59942494193972118584529797 11239217661369772234599337)
  ·
    refine ⟨8429413246027329175949503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11239217661369772234599337 8429413246027329175949503)
    ·
      refine ⟨12644119869040993763924255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8429413246027329175949503 12644119869040993763924255)
      ·
        refine ⟨18966179803561490645886383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12644119869040993763924255 18966179803561490645886383)
        ·
          refine ⟨28449269705342235968829575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18966179803561490645886383 28449269705342235968829575)
          ·
            refine ⟨42673904558013353953244363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28449269705342235968829575 42673904558013353953244363)
            ·
              refine ⟨64010856837020030929866545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42673904558013353953244363 64010856837020030929866545)
              ·
                refine ⟨48008142627765023197399909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64010856837020030929866545 48008142627765023197399909)
                ·
                  refine ⟨9001526742705941849512483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48008142627765023197399909 9001526742705941849512483)
                  ·
                    refine ⟨13502290114058912774268725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9001526742705941849512483 13502290114058912774268725)
                    ·
                      refine ⟨1265839698193023072587693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13502290114058912774268725 1265839698193023072587693)
                      ·
                        rfl

theorem cell23_2465214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_2465214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465214 prefixEnd_2465214 := by exact prefixLift 2465214
  have htrace : WordTrace (prefixWord ++ tailWord_2465214) baseStart_2465214 baseEnd_2465214 := by
    simpa [prefixWord, tailWord_2465214, baseEnd_2465214] using wordTrace_append hprefix tailTrace_2465214
  have hstable : (prefixWord ++ tailWord_2465214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465214).length < 2 ^ (prefixWord ++ tailWord_2465214).sum := by decide
  have hdescent : baseEnd_2465214 < baseStart_2465214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465224 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_2465224 : Nat := 118140960795 + 2465224 * 2 ^ 59
def prefixEnd_2465224 : Nat := 4983230072969 + 3 ^ 40 * 2465224 * 2
def baseEnd_2465224 : Nat := 1265844832999568033462647

theorem tailTrace_2465224 : CollatzResearch.WordTrace tailWord_2465224 prefixEnd_2465224 1265844832999568033462647 := by
  unfold tailWord_2465224
  simp only [CollatzResearch.WordTrace]
  refine ⟨44957053010460974792329363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59942737347281299723105817 44957053010460974792329363)
  ·
    refine ⟨67435579515691462188494045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44957053010460974792329363 67435579515691462188494045)
    ·
      refine ⟨25288342318384298320685267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67435579515691462188494045 25288342318384298320685267)
      ·
        refine ⟨37932513477576447481027901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25288342318384298320685267 37932513477576447481027901)
        ·
          refine ⟨14224692554091167805385463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37932513477576447481027901 14224692554091167805385463)
          ·
            refine ⟨21337038831136751708078195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14224692554091167805385463 21337038831136751708078195)
            ·
              refine ⟨32005558246705127562117293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21337038831136751708078195 32005558246705127562117293)
              ·
                refine ⟨12002084342514422835793985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32005558246705127562117293 12002084342514422835793985)
                ·
                  refine ⟨9001563256885817126845489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12002084342514422835793985 9001563256885817126845489)
                  ·
                    refine ⟨6751172442664362845134117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9001563256885817126845489 6751172442664362845134117)
                    ·
                      refine ⟨1265844832999568033462647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6751172442664362845134117 1265844832999568033462647)
                      ·
                        rfl

theorem cell23_2465224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_2465224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465224 prefixEnd_2465224 := by exact prefixLift 2465224
  have htrace : WordTrace (prefixWord ++ tailWord_2465224) baseStart_2465224 baseEnd_2465224 := by
    simpa [prefixWord, tailWord_2465224, baseEnd_2465224] using wordTrace_append hprefix tailTrace_2465224
  have hstable : (prefixWord ++ tailWord_2465224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465224).length < 2 ^ (prefixWord ++ tailWord_2465224).sum := by decide
  have hdescent : baseEnd_2465224 < baseStart_2465224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465228 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 1, 4, 2]
def baseStart_2465228 : Nat := 118140960795 + 2465228 * 2 ^ 59
def prefixEnd_2465228 : Nat := 4983230072969 + 3 ^ 40 * 2465228 * 2
def baseEnd_2465228 : Nat := 1265846886922186017812629

theorem tailTrace_2465228 : CollatzResearch.WordTrace tailWord_2465228 prefixEnd_2465228 1265846886922186017812629 := by
  unfold tailWord_2465228
  simp only [CollatzResearch.WordTrace]
  refine ⟨44957125956453729133902169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59942834608604972178536225 44957125956453729133902169)
  ·
    refine ⟨33717844467340296850426627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44957125956453729133902169 33717844467340296850426627)
    ·
      refine ⟨50576766701010445275639941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33717844467340296850426627 50576766701010445275639941)
      ·
        refine ⟨9483143756439458489182489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50576766701010445275639941 9483143756439458489182489)
        ·
          refine ⟨7112357817329593866886867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9483143756439458489182489 7112357817329593866886867)
          ·
            refine ⟨10668536725994390800330301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7112357817329593866886867 10668536725994390800330301)
            ·
              refine ⟨4000701272247896550123863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10668536725994390800330301 4000701272247896550123863)
              ·
                refine ⟨6001051908371844825185795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4000701272247896550123863 6001051908371844825185795)
                ·
                  refine ⟨9001577862557767237778693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6001051908371844825185795 9001577862557767237778693)
                  ·
                    refine ⟨1687795849229581357083505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9001577862557767237778693 1687795849229581357083505)
                    ·
                      refine ⟨1265846886922186017812629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1687795849229581357083505 1265846886922186017812629)
                      ·
                        rfl

theorem cell23_2465228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_2465228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465228 prefixEnd_2465228 := by exact prefixLift 2465228
  have htrace : WordTrace (prefixWord ++ tailWord_2465228) baseStart_2465228 baseEnd_2465228 := by
    simpa [prefixWord, tailWord_2465228, baseEnd_2465228] using wordTrace_append hprefix tailTrace_2465228
  have hstable : (prefixWord ++ tailWord_2465228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465228).length < 2 ^ (prefixWord ++ tailWord_2465228).sum := by decide
  have hdescent : baseEnd_2465228 < baseStart_2465228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465264 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 4, 5]
def baseStart_2465264 : Nat := 118140960795 + 2465264 * 2 ^ 59
def prefixEnd_2465264 : Nat := 4983230072969 + 3 ^ 40 * 2465264 * 2
def baseEnd_2465264 : Nat := 421955124075249292320821

theorem tailTrace_2465264 : CollatzResearch.WordTrace tailWord_2465264 prefixEnd_2465264 421955124075249292320821 := by
  unfold tailWord_2465264
  simp only [CollatzResearch.WordTrace]
  refine ⟨44957782470388518208057423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59943709960518024277409897 44957782470388518208057423)
  ·
    refine ⟨67436673705582777312086135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44957782470388518208057423 67436673705582777312086135)
    ·
      refine ⟨101155010558374165968129203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67436673705582777312086135 101155010558374165968129203)
      ·
        refine ⟨151732515837561248952193805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101155010558374165968129203 151732515837561248952193805)
        ·
          refine ⟨56899693439085468357072677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151732515837561248952193805 56899693439085468357072677)
          ·
            refine ⟨10668692519828525316951127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56899693439085468357072677 10668692519828525316951127)
            ·
              refine ⟨16003038779742787975426691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10668692519828525316951127 16003038779742787975426691)
              ·
                refine ⟨24004558169614181963140037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16003038779742787975426691 24004558169614181963140037)
                ·
                  refine ⟨4500854656802659118088757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24004558169614181963140037 4500854656802659118088757)
                  ·
                    refine ⟨421955124075249292320821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4500854656802659118088757 421955124075249292320821)
                    ·
                      rfl

theorem cell23_2465264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_2465264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465264 prefixEnd_2465264 := by exact prefixLift 2465264
  have htrace : WordTrace (prefixWord ++ tailWord_2465264) baseStart_2465264 baseEnd_2465264 := by
    simpa [prefixWord, tailWord_2465264, baseEnd_2465264] using wordTrace_append hprefix tailTrace_2465264
  have hstable : (prefixWord ++ tailWord_2465264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465264).length < 2 ^ (prefixWord ++ tailWord_2465264).sum := by decide
  have hdescent : baseEnd_2465264 < baseStart_2465264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465274 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_2465274 : Nat := 118140960795 + 2465274 * 2 ^ 59
def prefixEnd_2465274 : Nat := 4983230072969 + 3 ^ 40 * 2465274 * 2
def baseEnd_2465274 : Nat := 1265870507032292837837417

theorem tailTrace_2465274 : CollatzResearch.WordTrace tailWord_2465274 prefixEnd_2465274 1265870507032292837837417 := by
  unfold tailWord_2465274
  simp only [CollatzResearch.WordTrace]
  refine ⟨22478982417685202030994719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59943953113827205415985917 22478982417685202030994719)
  ·
    refine ⟨33718473626527803046492079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22478982417685202030994719 33718473626527803046492079)
    ·
      refine ⟨50577710439791704569738119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33718473626527803046492079 50577710439791704569738119)
      ·
        refine ⟨75866565659687556854607179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50577710439791704569738119 75866565659687556854607179)
        ·
          refine ⟨113799848489531335281910769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75866565659687556854607179 113799848489531335281910769)
          ·
            refine ⟨85349886367148501461433077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113799848489531335281910769 85349886367148501461433077)
            ·
              refine ⟨8001551846920172012009351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85349886367148501461433077 8001551846920172012009351)
              ·
                refine ⟨12002327770380258018014027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8001551846920172012009351 12002327770380258018014027)
                ·
                  refine ⟨18003491655570387027021041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12002327770380258018014027 18003491655570387027021041)
                  ·
                    refine ⟨13502618741677790270265781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18003491655570387027021041 13502618741677790270265781)
                    ·
                      refine ⟨1265870507032292837837417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13502618741677790270265781 1265870507032292837837417)
                      ·
                        rfl

theorem cell23_2465274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_2465274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465274 prefixEnd_2465274 := by exact prefixLift 2465274
  have htrace : WordTrace (prefixWord ++ tailWord_2465274) baseStart_2465274 baseEnd_2465274 := by
    simpa [prefixWord, tailWord_2465274, baseEnd_2465274] using wordTrace_append hprefix tailTrace_2465274
  have hstable : (prefixWord ++ tailWord_2465274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465274).length < 2 ^ (prefixWord ++ tailWord_2465274).sum := by decide
  have hdescent : baseEnd_2465274 < baseStart_2465274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465301 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_2465301 : Nat := 118140960795 + 2465301 * 2 ^ 59
def prefixEnd_2465301 : Nat := 4983230072969 + 3 ^ 40 * 2465301 * 2
def baseEnd_2465301 : Nat := 1265884371009964232199793

theorem tailTrace_2465301 : CollatzResearch.WordTrace tailWord_2465301 prefixEnd_2465301 1265884371009964232199793 := by
  unfold tailWord_2465301
  simp only [CollatzResearch.WordTrace]
  refine ⟨89916914441642991735211757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59944609627761994490141171 89916914441642991735211757)
  ·
    refine ⟨33718842915616121900704409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89916914441642991735211757 33718842915616121900704409)
    ·
      refine ⟨25289132186712091425528307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33718842915616121900704409 25289132186712091425528307)
      ·
        refine ⟨37933698280068137138292461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25289132186712091425528307 37933698280068137138292461)
        ·
          refine ⟨14225136855025551426859673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37933698280068137138292461 14225136855025551426859673)
          ·
            refine ⟨10668852641269163570144755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14225136855025551426859673 10668852641269163570144755)
            ·
              refine ⟨16003278961903745355217133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10668852641269163570144755 16003278961903745355217133)
              ·
                refine ⟨6001229610713904508206425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16003278961903745355217133 6001229610713904508206425)
                ·
                  refine ⟨4500922208035428381154819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6001229610713904508206425 4500922208035428381154819)
                  ·
                    refine ⟨6751383312053142571732229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4500922208035428381154819 6751383312053142571732229)
                    ·
                      refine ⟨1265884371009964232199793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6751383312053142571732229 1265884371009964232199793)
                      ·
                        rfl

theorem cell23_2465301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_2465301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465301 prefixEnd_2465301 := by exact prefixLift 2465301
  have htrace : WordTrace (prefixWord ++ tailWord_2465301) baseStart_2465301 baseEnd_2465301 := by
    simpa [prefixWord, tailWord_2465301, baseEnd_2465301] using wordTrace_append hprefix tailTrace_2465301
  have hstable : (prefixWord ++ tailWord_2465301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465301).length < 2 ^ (prefixWord ++ tailWord_2465301).sum := by decide
  have hdescent : baseEnd_2465301 < baseStart_2465301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465385 : List Nat := [1, 2, 1, 1, 1, 4, 4, 4, 1, 1, 3]
def baseStart_2465385 : Nat := 118140960795 + 2465385 * 2 ^ 59
def prefixEnd_2465385 : Nat := 4983230072969 + 3 ^ 40 * 2465385 * 2
def baseEnd_2465385 : Nat := 1265927503384941903549407

theorem tailTrace_2465385 : CollatzResearch.WordTrace tailWord_2465385 prefixEnd_2465385 1265927503384941903549407 := by
  unfold tailWord_2465385
  simp only [CollatzResearch.WordTrace]
  refine ⟨89919978173338674081269609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59946652115559116054179739 89919978173338674081269609)
  ·
    refine ⟨67439983630004005560952207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89919978173338674081269609 67439983630004005560952207)
    ·
      refine ⟨101159975445006008341428311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67439983630004005560952207 101159975445006008341428311)
      ·
        refine ⟨151739963167509012512142467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101159975445006008341428311 151739963167509012512142467)
        ·
          refine ⟨227609944751263518768213701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151739963167509012512142467 227609944751263518768213701)
          ·
            refine ⟨42676864640861909769040069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227609944751263518768213701 42676864640861909769040069)
            ·
              refine ⟨8001912120161608081695013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42676864640861909769040069 8001912120161608081695013)
              ·
                refine ⟨1500358522530301515317815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8001912120161608081695013 1500358522530301515317815)
                ·
                  refine ⟨2250537783795452272976723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500358522530301515317815 2250537783795452272976723)
                  ·
                    refine ⟨3375806675693178409465085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2250537783795452272976723 3375806675693178409465085)
                    ·
                      refine ⟨1265927503384941903549407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3375806675693178409465085 1265927503384941903549407)
                      ·
                        rfl

theorem cell23_2465385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 1, 1, 3].length) (baseStart_2465385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465385 prefixEnd_2465385 := by exact prefixLift 2465385
  have htrace : WordTrace (prefixWord ++ tailWord_2465385) baseStart_2465385 baseEnd_2465385 := by
    simpa [prefixWord, tailWord_2465385, baseEnd_2465385] using wordTrace_append hprefix tailTrace_2465385
  have hstable : (prefixWord ++ tailWord_2465385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465385).length < 2 ^ (prefixWord ++ tailWord_2465385).sum := by decide
  have hdescent : baseEnd_2465385 < baseStart_2465385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465408 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 4]
def baseStart_2465408 : Nat := 118140960795 + 2465408 * 2 ^ 59
def prefixEnd_2465408 : Nat := 4983230072969 + 3 ^ 40 * 2465408 * 2
def baseEnd_2465408 : Nat := 1265939313439995313561801

theorem tailTrace_2465408 : CollatzResearch.WordTrace tailWord_2465408 prefixEnd_2465408 1265939313439995313561801 := by
  unfold tailWord_2465408
  simp only [CollatzResearch.WordTrace]
  refine ⟨44960408526127674504678439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59947211368170232672904585 44960408526127674504678439)
  ·
    refine ⟨67440612789191511757017659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44960408526127674504678439 67440612789191511757017659)
    ·
      refine ⟨101160919183787267635526489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67440612789191511757017659 101160919183787267635526489)
      ·
        refine ⟨75870689387840450726644867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101160919183787267635526489 75870689387840450726644867)
        ·
          refine ⟨113806034081760676089967301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75870689387840450726644867 113806034081760676089967301)
          ·
            refine ⟨21338631390330126766868869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113806034081760676089967301 21338631390330126766868869)
            ·
              refine ⟨4000993385686898768787913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21338631390330126766868869 4000993385686898768787913)
              ·
                refine ⟨3000745039265174076590935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4000993385686898768787913 3000745039265174076590935)
                ·
                  refine ⟨4501117558897761114886403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000745039265174076590935 4501117558897761114886403)
                  ·
                    refine ⟨6751676338346641672329605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4501117558897761114886403 6751676338346641672329605)
                    ·
                      refine ⟨1265939313439995313561801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6751676338346641672329605 1265939313439995313561801)
                      ·
                        rfl

theorem cell23_2465408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_2465408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465408 prefixEnd_2465408 := by exact prefixLift 2465408
  have htrace : WordTrace (prefixWord ++ tailWord_2465408) baseStart_2465408 baseEnd_2465408 := by
    simpa [prefixWord, tailWord_2465408, baseEnd_2465408] using wordTrace_append hprefix tailTrace_2465408
  have hstable : (prefixWord ++ tailWord_2465408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465408).length < 2 ^ (prefixWord ++ tailWord_2465408).sum := by decide
  have hdescent : baseEnd_2465408 < baseStart_2465408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465418 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 4, 4]
def baseStart_2465418 : Nat := 118140960795 + 2465418 * 2 ^ 59
def prefixEnd_2465418 : Nat := 4983230072969 + 3 ^ 40 * 2465418 * 2
def baseEnd_2465418 : Nat := 421981482748846758145585

theorem tailTrace_2465418 : CollatzResearch.WordTrace tailWord_2465418 prefixEnd_2465418 421981482748846758145585 := by
  unfold tailWord_2465418
  simp only [CollatzResearch.WordTrace]
  refine ⟨22480295445554780179305227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59947454521479413811480605 22480295445554780179305227)
  ·
    refine ⟨33720443168332170268957841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22480295445554780179305227 33720443168332170268957841)
    ·
      refine ⟨25290332376249127701718381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33720443168332170268957841 25290332376249127701718381)
      ·
        refine ⟨9483874641093422888144393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25290332376249127701718381 9483874641093422888144393)
        ·
          refine ⟨7112905980820067166108295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9483874641093422888144393 7112905980820067166108295)
          ·
            refine ⟨10669358971230100749162443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7112905980820067166108295 10669358971230100749162443)
            ·
              refine ⟨16004038456845151123743665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10669358971230100749162443 16004038456845151123743665)
              ·
                refine ⟨12003028842633863342807749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16004038456845151123743665 12003028842633863342807749)
                ·
                  refine ⟨2250567907993849376776453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12003028842633863342807749 2250567907993849376776453)
                  ·
                    refine ⟨421981482748846758145585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2250567907993849376776453 421981482748846758145585)
                    ·
                      rfl

theorem cell23_2465418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_2465418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465418 prefixEnd_2465418 := by exact prefixLift 2465418
  have htrace : WordTrace (prefixWord ++ tailWord_2465418) baseStart_2465418 baseEnd_2465418 := by
    simpa [prefixWord, tailWord_2465418, baseEnd_2465418] using wordTrace_append hprefix tailTrace_2465418
  have hstable : (prefixWord ++ tailWord_2465418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465418).length < 2 ^ (prefixWord ++ tailWord_2465418).sum := by decide
  have hdescent : baseEnd_2465418 < baseStart_2465418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465431 : List Nat := [1, 1, 3, 3, 2, 4, 9]
def baseStart_2465431 : Nat := 118140960795 + 2465431 * 2 ^ 59
def prefixEnd_2465431 : Nat := 4983230072969 + 3 ^ 40 * 2465431 * 2
def baseEnd_2465431 : Nat := 15629026215988255846595

theorem tailTrace_2465431 : CollatzResearch.WordTrace tailWord_2465431 prefixEnd_2465431 15629026215988255846595 := by
  unfold tailWord_2465431
  simp only [CollatzResearch.WordTrace]
  refine ⟨89921655931172023937444147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59947770620781349291629431 89921655931172023937444147)
  ·
    refine ⟨134882483896758035906166221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89921655931172023937444147 134882483896758035906166221)
    ·
      refine ⟨50580931461284263464812333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134882483896758035906166221 50580931461284263464812333)
      ·
        refine ⟨18967849297981598799304625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50580931461284263464812333 18967849297981598799304625)
        ·
          refine ⟨14225886973486199099478469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18967849297981598799304625 14225886973486199099478469)
          ·
            refine ⟨2667353807528662331152213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14225886973486199099478469 2667353807528662331152213)
            ·
              refine ⟨15629026215988255846595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2667353807528662331152213 15629026215988255846595)
              ·
                rfl

theorem cell23_2465431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 9].length) (baseStart_2465431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465431 prefixEnd_2465431 := by exact prefixLift 2465431
  have htrace : WordTrace (prefixWord ++ tailWord_2465431) baseStart_2465431 baseEnd_2465431 := by
    simpa [prefixWord, tailWord_2465431, baseEnd_2465431] using wordTrace_append hprefix tailTrace_2465431
  have hstable : (prefixWord ++ tailWord_2465431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465431).length < 2 ^ (prefixWord ++ tailWord_2465431).sum := by decide
  have hdescent : baseEnd_2465431 < baseStart_2465431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465438 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2465438 : Nat := 118140960795 + 2465438 * 2 ^ 59
def prefixEnd_2465438 : Nat := 4983230072969 + 3 ^ 40 * 2465438 * 2
def baseEnd_2465438 : Nat := 1265954717859630196186663

theorem tailTrace_2465438 : CollatzResearch.WordTrace tailWord_2465438 prefixEnd_2465438 1265954717859630196186663 := by
  unfold tailWord_2465438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11240238905268333016618621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59947940828097776088632645 11240238905268333016618621)
  ·
    refine ⟨4215089589475624881231983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11240238905268333016618621 4215089589475624881231983)
    ·
      refine ⟨6322634384213437321847975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4215089589475624881231983 6322634384213437321847975)
      ·
        refine ⟨9483951576320155982771963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6322634384213437321847975 9483951576320155982771963)
        ·
          refine ⟨14225927364480233974157945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9483951576320155982771963 14225927364480233974157945)
          ·
            refine ⟨10669445523360175480618459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14225927364480233974157945 10669445523360175480618459)
            ·
              refine ⟨16004168285040263220927689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10669445523360175480618459 16004168285040263220927689)
              ·
                refine ⟨12003126213780197415695767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16004168285040263220927689 12003126213780197415695767)
                ·
                  refine ⟨18004689320670296123543651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12003126213780197415695767 18004689320670296123543651)
                  ·
                    refine ⟨27007033981005444185315477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18004689320670296123543651 27007033981005444185315477)
                    ·
                      refine ⟨1265954717859630196186663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27007033981005444185315477 1265954717859630196186663)
                      ·
                        rfl

theorem cell23_2465438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2465438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465438 prefixEnd_2465438 := by exact prefixLift 2465438
  have htrace : WordTrace (prefixWord ++ tailWord_2465438) baseStart_2465438 baseEnd_2465438 := by
    simpa [prefixWord, tailWord_2465438, baseEnd_2465438] using wordTrace_append hprefix tailTrace_2465438
  have hstable : (prefixWord ++ tailWord_2465438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465438).length < 2 ^ (prefixWord ++ tailWord_2465438).sum := by decide
  have hdescent : baseEnd_2465438 < baseStart_2465438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465462 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2465462 : Nat := 118140960795 + 2465462 * 2 ^ 59
def prefixEnd_2465462 : Nat := 4983230072969 + 3 ^ 40 * 2465462 * 2
def baseEnd_2465462 : Nat := 1265967041395338102286553

theorem tailTrace_2465462 : CollatzResearch.WordTrace tailWord_2465462 prefixEnd_2465462 1265967041395338102286553 := by
  unfold tailWord_2465462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5620174162128732264488915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59948524396039810821215093 5620174162128732264488915)
  ·
    refine ⟨8430261243193098396733373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5620174162128732264488915 8430261243193098396733373)
    ·
      refine ⟨3161347966197411898775015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8430261243193098396733373 3161347966197411898775015)
      ·
        refine ⟨4742021949296117848162523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3161347966197411898775015 4742021949296117848162523)
        ·
          refine ⟨7113032923944176772243785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4742021949296117848162523 7113032923944176772243785)
          ·
            refine ⟨5334774692958132579182839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7113032923944176772243785 5334774692958132579182839)
            ·
              refine ⟨8002162039437198868774259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5334774692958132579182839 8002162039437198868774259)
              ·
                refine ⟨12003243059155798303161389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8002162039437198868774259 12003243059155798303161389)
                ·
                  refine ⟨4501216147183424363685521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12003243059155798303161389 4501216147183424363685521)
                  ·
                    refine ⟨3375912110387568272764141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4501216147183424363685521 3375912110387568272764141)
                    ·
                      refine ⟨1265967041395338102286553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3375912110387568272764141 1265967041395338102286553)
                      ·
                        rfl

theorem cell23_2465462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2465462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465462 prefixEnd_2465462 := by exact prefixLift 2465462
  have htrace : WordTrace (prefixWord ++ tailWord_2465462) baseStart_2465462 baseEnd_2465462 := by
    simpa [prefixWord, tailWord_2465462, baseEnd_2465462] using wordTrace_append hprefix tailTrace_2465462
  have hstable : (prefixWord ++ tailWord_2465462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465462).length < 2 ^ (prefixWord ++ tailWord_2465462).sum := by decide
  have hdescent : baseEnd_2465462 < baseStart_2465462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465492 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2465492 : Nat := 118140960795 + 2465492 * 2 ^ 59
def prefixEnd_2465492 : Nat := 4983230072969 + 3 ^ 40 * 2465492 * 2
def baseEnd_2465492 : Nat := 1265982445814972984911415

theorem tailTrace_2465492 : CollatzResearch.WordTrace tailWord_2465492 prefixEnd_2465492 1265982445814972984911415 := by
  unfold tailWord_2465492
  simp only [CollatzResearch.WordTrace]
  refine ⟨44961940391975515677707365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59949253855967354236943153 44961940391975515677707365)
  ·
    refine ⟨8430363823495409189570131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44961940391975515677707365 8430363823495409189570131)
    ·
      refine ⟨12645545735243113784355197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8430363823495409189570131 12645545735243113784355197)
      ·
        refine ⟨4742079650716167669133199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12645545735243113784355197 4742079650716167669133199)
        ·
          refine ⟨7113119476074251503699799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4742079650716167669133199 7113119476074251503699799)
          ·
            refine ⟨10669679214111377255549699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7113119476074251503699799 10669679214111377255549699)
            ·
              refine ⟨16004518821167065883324549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10669679214111377255549699 16004518821167065883324549)
              ·
                refine ⟨3000847278968824853123353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16004518821167065883324549 3000847278968824853123353)
                ·
                  refine ⟨2250635459226618639842515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3000847278968824853123353 2250635459226618639842515)
                  ·
                    refine ⟨3375953188839927959763773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2250635459226618639842515 3375953188839927959763773)
                    ·
                      refine ⟨1265982445814972984911415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3375953188839927959763773 1265982445814972984911415)
                      ·
                        rfl

theorem cell23_2465492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2465492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465492 prefixEnd_2465492 := by exact prefixLift 2465492
  have htrace : WordTrace (prefixWord ++ tailWord_2465492) baseStart_2465492 baseEnd_2465492 := by
    simpa [prefixWord, tailWord_2465492, baseEnd_2465492] using wordTrace_append hprefix tailTrace_2465492
  have hstable : (prefixWord ++ tailWord_2465492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465492).length < 2 ^ (prefixWord ++ tailWord_2465492).sum := by decide
  have hdescent : baseEnd_2465492 < baseStart_2465492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465518 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_2465518 : Nat := 118140960795 + 2465518 * 2 ^ 59
def prefixEnd_2465518 : Nat := 4983230072969 + 3 ^ 40 * 2465518 * 2
def baseEnd_2465518 : Nat := 1265995796311989883186295

theorem tailTrace_2465518 : CollatzResearch.WordTrace tailWord_2465518 prefixEnd_2465518 1265995796311989883186295 := by
  unfold tailWord_2465518
  simp only [CollatzResearch.WordTrace]
  refine ⟨11240603635232104724482651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59949886054571225197240805 11240603635232104724482651)
  ·
    refine ⟨16860905452848157086723977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11240603635232104724482651 16860905452848157086723977)
    ·
      refine ⟨12645679089636117815042983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16860905452848157086723977 12645679089636117815042983)
      ·
        refine ⟨18968518634454176722564475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12645679089636117815042983 18968518634454176722564475)
        ·
          refine ⟨28452777951681265083846713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18968518634454176722564475 28452777951681265083846713)
          ·
            refine ⟨21339583463760948812885035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28452777951681265083846713 21339583463760948812885035)
            ·
              refine ⟨32009375195641423219327553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21339583463760948812885035 32009375195641423219327553)
              ·
                refine ⟨24007031396731067414495665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32009375195641423219327553 24007031396731067414495665)
                ·
                  refine ⟨18005273547548300560871749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24007031396731067414495665 18005273547548300560871749)
                  ·
                    refine ⟨3375988790165306355163453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18005273547548300560871749 3375988790165306355163453)
                    ·
                      refine ⟨1265995796311989883186295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3375988790165306355163453 1265995796311989883186295)
                      ·
                        rfl

theorem cell23_2465518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_2465518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465518 prefixEnd_2465518 := by exact prefixLift 2465518
  have htrace : WordTrace (prefixWord ++ tailWord_2465518) baseStart_2465518 baseEnd_2465518 := by
    simpa [prefixWord, tailWord_2465518, baseEnd_2465518] using wordTrace_append hprefix tailTrace_2465518
  have hstable : (prefixWord ++ tailWord_2465518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465518).length < 2 ^ (prefixWord ++ tailWord_2465518).sum := by decide
  have hdescent : baseEnd_2465518 < baseStart_2465518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465521 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 9]
def baseStart_2465521 : Nat := 118140960795 + 2465521 * 2 ^ 59
def prefixEnd_2465521 : Nat := 4983230072969 + 3 ^ 40 * 2465521 * 2
def baseEnd_2465521 : Nat := 140666370750439263494309

theorem tailTrace_2465521 : CollatzResearch.WordTrace tailWord_2465521 prefixEnd_2465521 140666370750439263494309 := by
  unfold tailWord_2465521
  simp only [CollatzResearch.WordTrace]
  refine ⟨89924938500845969308220417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59949959000563979538813611 89924938500845969308220417)
  ·
    refine ⟨67443703875634476981165313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89924938500845969308220417 67443703875634476981165313)
    ·
      refine ⟨50582777906725857735873985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67443703875634476981165313 50582777906725857735873985)
      ·
        refine ⟨37937083430044393301905489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50582777906725857735873985 37937083430044393301905489)
        ·
          refine ⟨28452812572533294976429117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37937083430044393301905489 28452812572533294976429117)
          ·
            refine ⟨10669804714699985616160919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28452812572533294976429117 10669804714699985616160919)
            ·
              refine ⟨16004707072049978424241379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10669804714699985616160919 16004707072049978424241379)
              ·
                refine ⟨24007060608074967636362069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16004707072049978424241379 24007060608074967636362069)
                ·
                  refine ⟨140666370750439263494309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24007060608074967636362069 140666370750439263494309)
                  ·
                    rfl

theorem cell23_2465521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 9].length) (baseStart_2465521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465521 prefixEnd_2465521 := by exact prefixLift 2465521
  have htrace : WordTrace (prefixWord ++ tailWord_2465521) baseStart_2465521 baseEnd_2465521 := by
    simpa [prefixWord, tailWord_2465521, baseEnd_2465521] using wordTrace_append hprefix tailTrace_2465521
  have hstable : (prefixWord ++ tailWord_2465521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465521).length < 2 ^ (prefixWord ++ tailWord_2465521).sum := by decide
  have hdescent : baseEnd_2465521 < baseStart_2465521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465538 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 9]
def baseStart_2465538 : Nat := 118140960795 + 2465538 * 2 ^ 59
def prefixEnd_2465538 : Nat := 4983230072969 + 3 ^ 40 * 2465538 * 2
def baseEnd_2465538 : Nat := 140667340658342200548467

theorem tailTrace_2465538 : CollatzResearch.WordTrace tailWord_2465538 prefixEnd_2465538 140667340658342200548467 := by
  unfold tailWord_2465538
  simp only [CollatzResearch.WordTrace]
  refine ⟨22481389635446095302897317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59950372361189587474392845 22481389635446095302897317)
  ·
    refine ⟨4215260556646142869293247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22481389635446095302897317 4215260556646142869293247)
    ·
      refine ⟨6322890834969214303939871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4215260556646142869293247 6322890834969214303939871)
      ·
        refine ⟨9484336252453821455909807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6322890834969214303939871 9484336252453821455909807)
        ·
          refine ⟨14226504378680732183864711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9484336252453821455909807 14226504378680732183864711)
          ·
            refine ⟨21339756568021098275797067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14226504378680732183864711 21339756568021098275797067)
            ·
              refine ⟨32009634852031647413695601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21339756568021098275797067 32009634852031647413695601)
              ·
                refine ⟨24007226139023735560271701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32009634852031647413695601 24007226139023735560271701)
                ·
                  refine ⟨140667340658342200548467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24007226139023735560271701 140667340658342200548467)
                  ·
                    rfl

theorem cell23_2465538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_2465538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465538 prefixEnd_2465538 := by exact prefixLift 2465538
  have htrace : WordTrace (prefixWord ++ tailWord_2465538) baseStart_2465538 baseEnd_2465538 := by
    simpa [prefixWord, tailWord_2465538, baseEnd_2465538] using wordTrace_append hprefix tailTrace_2465538
  have hstable : (prefixWord ++ tailWord_2465538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465538).length < 2 ^ (prefixWord ++ tailWord_2465538).sum := by decide
  have hdescent : baseEnd_2465538 < baseStart_2465538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465548 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 2, 3, 3]
def baseStart_2465548 : Nat := 118140960795 + 2465548 * 2 ^ 59
def prefixEnd_2465548 : Nat := 4983230072969 + 3 ^ 40 * 2465548 * 2
def baseEnd_2465548 : Nat := 1266011200731624765811157

theorem tailTrace_2465548 : CollatzResearch.WordTrace tailWord_2465548 prefixEnd_2465548 1266011200731624765811157 := by
  unfold tailWord_2465548
  simp only [CollatzResearch.WordTrace]
  refine ⟨44962961635874076459726649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59950615514498768612968865 44962961635874076459726649)
  ·
    refine ⟨33722221226905557344794987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44962961635874076459726649 33722221226905557344794987)
    ·
      refine ⟨50583331840358336017192481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33722221226905557344794987 50583331840358336017192481)
      ·
        refine ⟨37937498880268752012894361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50583331840358336017192481 37937498880268752012894361)
        ·
          refine ⟨28453124160201564009670771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37937498880268752012894361 28453124160201564009670771)
          ·
            refine ⟨42679686240302346014506157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28453124160201564009670771 42679686240302346014506157)
            ·
              refine ⟨16004882340113379755439809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42679686240302346014506157 16004882340113379755439809)
              ·
                refine ⟨12003661755085034816579857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16004882340113379755439809 12003661755085034816579857)
                ·
                  refine ⟨9002746316313776112434893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12003661755085034816579857 9002746316313776112434893)
                  ·
                    refine ⟨3376029868617666042163085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9002746316313776112434893 3376029868617666042163085)
                    ·
                      refine ⟨1266011200731624765811157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3376029868617666042163085 1266011200731624765811157)
                      ·
                        rfl

theorem cell23_2465548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_2465548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465548 prefixEnd_2465548 := by exact prefixLift 2465548
  have htrace : WordTrace (prefixWord ++ tailWord_2465548) baseStart_2465548 baseEnd_2465548 := by
    simpa [prefixWord, tailWord_2465548, baseEnd_2465548] using wordTrace_append hprefix tailTrace_2465548
  have hstable : (prefixWord ++ tailWord_2465548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465548).length < 2 ^ (prefixWord ++ tailWord_2465548).sum := by decide
  have hdescent : baseEnd_2465548 < baseStart_2465548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465561 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_2465561 : Nat := 118140960795 + 2465561 * 2 ^ 59
def prefixEnd_2465561 : Nat := 4983230072969 + 3 ^ 40 * 2465561 * 2
def baseEnd_2465561 : Nat := 1266017875980133214948597

theorem tailTrace_2465561 : CollatzResearch.WordTrace tailWord_2465561 prefixEnd_2465561 1266017875980133214948597 := by
  unfold tailWord_2465561
  simp only [CollatzResearch.WordTrace]
  refine ⟨89926397420701056139676537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59950931613800704093117691 89926397420701056139676537)
  ·
    refine ⟨67444798065525792104757403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89926397420701056139676537 67444798065525792104757403)
    ·
      refine ⟨101167197098288688157136105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67444798065525792104757403 101167197098288688157136105)
      ·
        refine ⟨75875397823716516117852079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101167197098288688157136105 75875397823716516117852079)
        ·
          refine ⟨113813096735574774176778119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75875397823716516117852079 113813096735574774176778119)
          ·
            refine ⟨170719645103362161265167179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113813096735574774176778119 170719645103362161265167179)
            ·
              refine ⟨256079467655043241897750769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170719645103362161265167179 256079467655043241897750769)
              ·
                refine ⟨192059600741282431423313077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256079467655043241897750769 192059600741282431423313077)
                ·
                  refine ⟨18005587569495227945935601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192059600741282431423313077 18005587569495227945935601)
                  ·
                    refine ⟨13504190677121420959451701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18005587569495227945935601 13504190677121420959451701)
                    ·
                      refine ⟨1266017875980133214948597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13504190677121420959451701 1266017875980133214948597)
                      ·
                        rfl

theorem cell23_2465561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_2465561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465561 prefixEnd_2465561 := by exact prefixLift 2465561
  have htrace : WordTrace (prefixWord ++ tailWord_2465561) baseStart_2465561 baseEnd_2465561 := by
    simpa [prefixWord, tailWord_2465561, baseEnd_2465561] using wordTrace_append hprefix tailTrace_2465561
  have hstable : (prefixWord ++ tailWord_2465561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465561).length < 2 ^ (prefixWord ++ tailWord_2465561).sum := by decide
  have hdescent : baseEnd_2465561 < baseStart_2465561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465589 : List Nat := [1, 3, 3, 1, 5, 1, 1, 3, 5]
def baseStart_2465589 : Nat := 118140960795 + 2465589 * 2 ^ 59
def prefixEnd_2465589 : Nat := 4983230072969 + 3 ^ 40 * 2465589 * 2
def baseEnd_2465589 : Nat := 140670250382051011710941

theorem tailTrace_2465589 : CollatzResearch.WordTrace tailWord_2465589 prefixEnd_2465589 140670250382051011710941 := by
  unfold tailWord_2465589
  simp only [CollatzResearch.WordTrace]
  refine ⟨89927418664599616921695821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59951612443066411281130547 89927418664599616921695821)
  ·
    refine ⟨33722781999224856345635933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89927418664599616921695821 33722781999224856345635933)
    ·
      refine ⟨12646043249709321129613475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33722781999224856345635933 12646043249709321129613475)
      ·
        refine ⟨18969064874563981694420213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12646043249709321129613475 18969064874563981694420213)
        ·
          refine ⟨1778349831990373283851895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18969064874563981694420213 1778349831990373283851895)
          ·
            refine ⟨2667524747985559925777843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778349831990373283851895 2667524747985559925777843)
            ·
              refine ⟨4001287121978339888666765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2667524747985559925777843 4001287121978339888666765)
              ·
                refine ⟨1500482670741877458250037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4001287121978339888666765 1500482670741877458250037)
                ·
                  refine ⟨140670250382051011710941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1500482670741877458250037 140670250382051011710941)
                  ·
                    rfl

theorem cell23_2465589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_2465589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465589 prefixEnd_2465589 := by exact prefixLift 2465589
  have htrace : WordTrace (prefixWord ++ tailWord_2465589) baseStart_2465589 baseEnd_2465589 := by
    simpa [prefixWord, tailWord_2465589, baseEnd_2465589] using wordTrace_append hprefix tailTrace_2465589
  have hstable : (prefixWord ++ tailWord_2465589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465589).length < 2 ^ (prefixWord ++ tailWord_2465589).sum := by decide
  have hdescent : baseEnd_2465589 < baseStart_2465589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465606 : List Nat := [6, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_2465606 : Nat := 118140960795 + 2465606 * 2 ^ 59
def prefixEnd_2465606 : Nat := 4983230072969 + 3 ^ 40 * 2465606 * 2
def baseEnd_2465606 : Nat := 140671220289953948765099

theorem tailTrace_2465606 : CollatzResearch.WordTrace tailWord_2465606 prefixEnd_2465606 140671220289953948765099 := by
  unfold tailWord_2465606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2810251209548063400783271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59952025803692019216709781 2810251209548063400783271)
  ·
    refine ⟨4215376814322095101174907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2810251209548063400783271 4215376814322095101174907)
    ·
      refine ⟨6323065221483142651762361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4215376814322095101174907 6323065221483142651762361)
      ·
        refine ⟨4742298916112356988821771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6323065221483142651762361 4742298916112356988821771)
        ·
          refine ⟨7113448374168535483232657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4742298916112356988821771 7113448374168535483232657)
          ·
            refine ⟨5335086280626401612424493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7113448374168535483232657 5335086280626401612424493)
            ·
              refine ⟨2000657355234900604659185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5335086280626401612424493 2000657355234900604659185)
              ·
                refine ⟨1500493016426175453494389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2000657355234900604659185 1500493016426175453494389)
                ·
                  refine ⟨140671220289953948765099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1500493016426175453494389 140671220289953948765099)
                  ·
                    rfl

theorem cell23_2465606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_2465606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465606 prefixEnd_2465606 := by exact prefixLift 2465606
  have htrace : WordTrace (prefixWord ++ tailWord_2465606) baseStart_2465606 baseEnd_2465606 := by
    simpa [prefixWord, tailWord_2465606, baseEnd_2465606] using wordTrace_append hprefix tailTrace_2465606
  have hstable : (prefixWord ++ tailWord_2465606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465606).length < 2 ^ (prefixWord ++ tailWord_2465606).sum := by decide
  have hdescent : baseEnd_2465606 < baseStart_2465606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465662 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_2465662 : Nat := 118140960795 + 2465662 * 2 ^ 59
def prefixEnd_2465662 : Nat := 4983230072969 + 3 ^ 40 * 2465662 * 2
def baseEnd_2465662 : Nat := 140674415280693035531737

theorem tailTrace_2465662 : CollatzResearch.WordTrace tailWord_2465662 prefixEnd_2465662 140674415280693035531737 := by
  unfold tailWord_2465662
  simp only [CollatzResearch.WordTrace]
  refine ⟨11241260149166893798637905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59953387462223433592735493 11241260149166893798637905)
  ·
    refine ⟨8430945111875170348978429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11241260149166893798637905 8430945111875170348978429)
    ·
      refine ⟨3161604416953188880866911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8430945111875170348978429 3161604416953188880866911)
      ·
        refine ⟨4742406625429783321300367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3161604416953188880866911 4742406625429783321300367)
        ·
          refine ⟨7113609938144674981950551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4742406625429783321300367 7113609938144674981950551)
          ·
            refine ⟨10670414907217012472925827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7113609938144674981950551 10670414907217012472925827)
            ·
              refine ⟨16005622360825518709388741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10670414907217012472925827 16005622360825518709388741)
              ·
                refine ⟨3001054192654784758010389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16005622360825518709388741 3001054192654784758010389)
                ·
                  refine ⟨140674415280693035531737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3001054192654784758010389 140674415280693035531737)
                  ·
                    rfl

theorem cell23_2465662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_2465662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465662 prefixEnd_2465662 := by exact prefixLift 2465662
  have htrace : WordTrace (prefixWord ++ tailWord_2465662) baseStart_2465662 baseEnd_2465662 := by
    simpa [prefixWord, tailWord_2465662, baseEnd_2465662] using wordTrace_append hprefix tailTrace_2465662
  have hstable : (prefixWord ++ tailWord_2465662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465662).length < 2 ^ (prefixWord ++ tailWord_2465662).sum := by decide
  have hdescent : baseEnd_2465662 < baseStart_2465662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465745 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 1, 3, 3]
def baseStart_2465745 : Nat := 118140960795 + 2465745 * 2 ^ 59
def prefixEnd_2465745 : Nat := 4983230072969 + 3 ^ 40 * 2465745 * 2
def baseEnd_2465745 : Nat := 1266112356420560495047751

theorem tailTrace_2465745 : CollatzResearch.WordTrace tailWord_2465745 prefixEnd_2465745 1266112356420560495047751 := by
  unfold tailWord_2465745
  simp only [CollatzResearch.WordTrace]
  refine ⟨89933108452034455564374689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59955405634689637042916459 89933108452034455564374689)
  ·
    refine ⟨67449831339025841673281017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89933108452034455564374689 67449831339025841673281017)
    ·
      refine ⟨50587373504269381254960763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67449831339025841673281017 50587373504269381254960763)
      ·
        refine ⟨75881060256404071882441145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50587373504269381254960763 75881060256404071882441145)
        ·
          refine ⟨56910795192303053911830859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75881060256404071882441145 56910795192303053911830859)
          ·
            refine ⟨85366192788454580867746289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56910795192303053911830859 85366192788454580867746289)
            ·
              refine ⟨64024644591340935650809717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85366192788454580867746289 64024644591340935650809717)
              ·
                refine ⟨6002310430438212717263411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64024644591340935650809717 6002310430438212717263411)
                ·
                  refine ⟨9003465645657319075895117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6002310430438212717263411 9003465645657319075895117)
                  ·
                    refine ⟨3376299617121494653460669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9003465645657319075895117 3376299617121494653460669)
                    ·
                      refine ⟨1266112356420560495047751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3376299617121494653460669 1266112356420560495047751)
                      ·
                        rfl

theorem cell23_2465745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_2465745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465745 prefixEnd_2465745 := by exact prefixLift 2465745
  have htrace : WordTrace (prefixWord ++ tailWord_2465745) baseStart_2465745 baseEnd_2465745 := by
    simpa [prefixWord, tailWord_2465745, baseEnd_2465745] using wordTrace_append hprefix tailTrace_2465745
  have hstable : (prefixWord ++ tailWord_2465745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465745).length < 2 ^ (prefixWord ++ tailWord_2465745).sum := by decide
  have hdescent : baseEnd_2465745 < baseStart_2465745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465749 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_2465749 : Nat := 118140960795 + 2465749 * 2 ^ 59
def prefixEnd_2465749 : Nat := 4983230072969 + 3 ^ 40 * 2465749 * 2
def baseEnd_2465749 : Nat := 1266114410343178479397733

theorem tailTrace_2465749 : CollatzResearch.WordTrace tailWord_2465749 prefixEnd_2465749 1266114410343178479397733 := by
  unfold tailWord_2465749
  simp only [CollatzResearch.WordTrace]
  refine ⟨89933254344019964247520301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59955502896013309498346867 89933254344019964247520301)
  ·
    refine ⟨33724970379007486592820113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89933254344019964247520301 33724970379007486592820113)
    ·
      refine ⟨25293727784255614944615085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33724970379007486592820113 25293727784255614944615085)
      ·
        refine ⟨9485147919095855604230657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25293727784255614944615085 9485147919095855604230657)
        ·
          refine ⟨7113860939321891703172993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9485147919095855604230657 7113860939321891703172993)
          ·
            refine ⟨5335395704491418777379745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7113860939321891703172993 5335395704491418777379745)
            ·
              refine ⟨4001546778368564083034809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5335395704491418777379745 4001546778368564083034809)
              ·
                refine ⟨3001160083776423062276107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4001546778368564083034809 3001160083776423062276107)
                ·
                  refine ⟨4501740125664634593414161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3001160083776423062276107 4501740125664634593414161)
                  ·
                    refine ⟨3376305094248475945060621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4501740125664634593414161 3376305094248475945060621)
                    ·
                      refine ⟨1266114410343178479397733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3376305094248475945060621 1266114410343178479397733)
                      ·
                        rfl

theorem cell23_2465749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_2465749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465749 prefixEnd_2465749 := by exact prefixLift 2465749
  have htrace : WordTrace (prefixWord ++ tailWord_2465749) baseStart_2465749 baseEnd_2465749 := by
    simpa [prefixWord, tailWord_2465749, baseEnd_2465749] using wordTrace_append hprefix tailTrace_2465749
  have hstable : (prefixWord ++ tailWord_2465749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465749).length < 2 ^ (prefixWord ++ tailWord_2465749).sum := by decide
  have hdescent : baseEnd_2465749 < baseStart_2465749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465763 : List Nat := [1, 1, 1, 6, 1, 4, 1, 3, 1, 2, 2]
def baseStart_2465763 : Nat := 118140960795 + 2465763 * 2 ^ 59
def prefixEnd_2465763 : Nat := 4983230072969 + 3 ^ 40 * 2465763 * 2
def baseEnd_2465763 : Nat := 1266121599072341424622669

theorem tailTrace_2465763 : CollatzResearch.WordTrace tailWord_2465763 prefixEnd_2465763 1266121599072341424622669 := by
  unfold tailWord_2465763
  simp only [CollatzResearch.WordTrace]
  refine ⟨89933764965969244638529943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59955843310646163092353295 89933764965969244638529943)
  ·
    refine ⟨134900647448953866957794915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89933764965969244638529943 134900647448953866957794915)
    ·
      refine ⟨202350971173430800436692373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134900647448953866957794915 202350971173430800436692373)
      ·
        refine ⟨9485201773754568770469955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 202350971173430800436692373 9485201773754568770469955)
        ·
          refine ⟨14227802660631853155704933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9485201773754568770469955 14227802660631853155704933)
          ·
            refine ⟨2667712998868472466694675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14227802660631853155704933 2667712998868472466694675)
            ·
              refine ⟨4001569498302708700042013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2667712998868472466694675 4001569498302708700042013)
              ·
                refine ⟨1500588561863515762515755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4001569498302708700042013 1500588561863515762515755)
                ·
                  refine ⟨2250882842795273643773633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500588561863515762515755 2250882842795273643773633)
                  ·
                    refine ⟨1688162132096455232830225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2250882842795273643773633 1688162132096455232830225)
                    ·
                      refine ⟨1266121599072341424622669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688162132096455232830225 1266121599072341424622669)
                      ·
                        rfl

theorem cell23_2465763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_2465763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465763 prefixEnd_2465763 := by exact prefixLift 2465763
  have htrace : WordTrace (prefixWord ++ tailWord_2465763) baseStart_2465763 baseEnd_2465763 := by
    simpa [prefixWord, tailWord_2465763, baseEnd_2465763] using wordTrace_append hprefix tailTrace_2465763
  have hstable : (prefixWord ++ tailWord_2465763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465763).length < 2 ^ (prefixWord ++ tailWord_2465763).sum := by decide
  have hdescent : baseEnd_2465763 < baseStart_2465763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465852 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_2465852 : Nat := 118140960795 + 2465852 * 2 ^ 59
def prefixEnd_2465852 : Nat := 4983230072969 + 3 ^ 40 * 2465852 * 2
def baseEnd_2465852 : Nat := 1266167298850591576409759

theorem tailTrace_2465852 : CollatzResearch.WordTrace tailWord_2465852 prefixEnd_2465852 1266167298850591576409759 := by
  unfold tailWord_2465852
  simp only [CollatzResearch.WordTrace]
  refine ⟨44968505531323406419259905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59958007375097875225679873 44968505531323406419259905)
  ·
    refine ⟨33726379148492554814444929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44968505531323406419259905 33726379148492554814444929)
    ·
      refine ⟨25294784361369416110833697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33726379148492554814444929 25294784361369416110833697)
      ·
        refine ⟨18971088271027062083125273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25294784361369416110833697 18971088271027062083125273)
        ·
          refine ⟨14228316203270296562343955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18971088271027062083125273 14228316203270296562343955)
          ·
            refine ⟨21342474304905444843515933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14228316203270296562343955 21342474304905444843515933)
            ·
              refine ⟨8003427864339541816318475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21342474304905444843515933 8003427864339541816318475)
              ·
                refine ⟨12005141796509312724477713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8003427864339541816318475 12005141796509312724477713)
                ·
                  refine ⟨9003856347381984543358285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12005141796509312724477713 9003856347381984543358285)
                  ·
                    refine ⟨3376446130268244203759357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9003856347381984543358285 3376446130268244203759357)
                    ·
                      refine ⟨1266167298850591576409759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3376446130268244203759357 1266167298850591576409759)
                      ·
                        rfl

theorem cell23_2465852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_2465852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465852 prefixEnd_2465852 := by exact prefixLift 2465852
  have htrace : WordTrace (prefixWord ++ tailWord_2465852) baseStart_2465852 baseEnd_2465852 := by
    simpa [prefixWord, tailWord_2465852, baseEnd_2465852] using wordTrace_append hprefix tailTrace_2465852
  have hstable : (prefixWord ++ tailWord_2465852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465852).length < 2 ^ (prefixWord ++ tailWord_2465852).sum := by decide
  have hdescent : baseEnd_2465852 < baseStart_2465852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465855 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 4, 5]
def baseStart_2465855 : Nat := 118140960795 + 2465855 * 2 ^ 59
def prefixEnd_2465855 : Nat := 4983230072969 + 3 ^ 40 * 2465855 * 2
def baseEnd_2465855 : Nat := 422056279764185021557415

theorem tailTrace_2465855 : CollatzResearch.WordTrace tailWord_2465855 prefixEnd_2465855 422056279764185021557415 := by
  unfold tailWord_2465855
  simp only [CollatzResearch.WordTrace]
  refine ⟨89937120481635944350879019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59958080321090629567252679 89937120481635944350879019)
  ·
    refine ⟨134905680722453916526318529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89937120481635944350879019 134905680722453916526318529)
    ·
      refine ⟨101179260541840437394738897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134905680722453916526318529 101179260541840437394738897)
      ·
        refine ⟨75884445406380328046054173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101179260541840437394738897 75884445406380328046054173)
        ·
          refine ⟨28456667027392623017270315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75884445406380328046054173 28456667027392623017270315)
          ·
            refine ⟨42685000541088934525905473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28456667027392623017270315 42685000541088934525905473)
            ·
              refine ⟨32013750405816700894429105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42685000541088934525905473 32013750405816700894429105)
              ·
                refine ⟨24010312804362525670821829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32013750405816700894429105 24010312804362525670821829)
                ·
                  refine ⟨4501933650817973563279093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24010312804362525670821829 4501933650817973563279093)
                  ·
                    refine ⟨422056279764185021557415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4501933650817973563279093 422056279764185021557415)
                    ·
                      rfl

theorem cell23_2465855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_2465855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465855 prefixEnd_2465855 := by exact prefixLift 2465855
  have htrace : WordTrace (prefixWord ++ tailWord_2465855) baseStart_2465855 baseEnd_2465855 := by
    simpa [prefixWord, tailWord_2465855, baseEnd_2465855] using wordTrace_append hprefix tailTrace_2465855
  have hstable : (prefixWord ++ tailWord_2465855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465855).length < 2 ^ (prefixWord ++ tailWord_2465855).sum := by decide
  have hdescent : baseEnd_2465855 < baseStart_2465855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465892 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_2465892 : Nat := 118140960795 + 2465892 * 2 ^ 59
def prefixEnd_2465892 : Nat := 4983230072969 + 3 ^ 40 * 2465892 * 2
def baseEnd_2465892 : Nat := 1266187838076771419909575

theorem tailTrace_2465892 : CollatzResearch.WordTrace tailWord_2465892 prefixEnd_2465892 1266187838076771419909575 := by
  unfold tailWord_2465892
  simp only [CollatzResearch.WordTrace]
  refine ⟨44969234991250949834987965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59958979988334599779983953 44969234991250949834987965)
  ·
    refine ⟨16863463121719106188120487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44969234991250949834987965 16863463121719106188120487)
    ·
      refine ⟨25295194682578659282180731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16863463121719106188120487 25295194682578659282180731)
      ·
        refine ⟨37942792023867988923271097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25295194682578659282180731 37942792023867988923271097)
        ·
          refine ⟨28457094017900991692453323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37942792023867988923271097 28457094017900991692453323)
          ·
            refine ⟨42685641026851487538679985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28457094017900991692453323 42685641026851487538679985)
            ·
              refine ⟨32014230770138615654009989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42685641026851487538679985 32014230770138615654009989)
              ·
                refine ⟨6002668269400990435126873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32014230770138615654009989 6002668269400990435126873)
                ·
                  refine ⟨4502001202050742826345155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6002668269400990435126873 4502001202050742826345155)
                  ·
                    refine ⟨6753001803076114239517733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4502001202050742826345155 6753001803076114239517733)
                    ·
                      refine ⟨1266187838076771419909575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6753001803076114239517733 1266187838076771419909575)
                      ·
                        rfl

theorem cell23_2465892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_2465892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465892 prefixEnd_2465892 := by exact prefixLift 2465892
  have htrace : WordTrace (prefixWord ++ tailWord_2465892) baseStart_2465892 baseEnd_2465892 := by
    simpa [prefixWord, tailWord_2465892, baseEnd_2465892] using wordTrace_append hprefix tailTrace_2465892
  have hstable : (prefixWord ++ tailWord_2465892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465892).length < 2 ^ (prefixWord ++ tailWord_2465892).sum := by decide
  have hdescent : baseEnd_2465892 < baseStart_2465892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465905 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_2465905 : Nat := 118140960795 + 2465905 * 2 ^ 59
def prefixEnd_2465905 : Nat := 4983230072969 + 3 ^ 40 * 2465905 * 2
def baseEnd_2465905 : Nat := 1266194513325279869047015

theorem tailTrace_2465905 : CollatzResearch.WordTrace tailWord_2465905 prefixEnd_2465905 1266194513325279869047015 := by
  unfold tailWord_2465905
  simp only [CollatzResearch.WordTrace]
  refine ⟨89938944131454802890199169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59959296087636535260132779 89938944131454802890199169)
  ·
    refine ⟨67454208098591102167649377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89938944131454802890199169 67454208098591102167649377)
    ·
      refine ⟨50590656073943326625737033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67454208098591102167649377 50590656073943326625737033)
      ·
        refine ⟨37942992055457494969302775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50590656073943326625737033 37942992055457494969302775)
        ·
          refine ⟨56914488083186242453954163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37942992055457494969302775 56914488083186242453954163)
          ·
            refine ⟨85371732124779363680931245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56914488083186242453954163 85371732124779363680931245)
            ·
              refine ⟨32014399546792261380349217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85371732124779363680931245 32014399546792261380349217)
              ·
                refine ⟨24010799660094196035261913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32014399546792261380349217 24010799660094196035261913)
                ·
                  refine ⟨18008099745070647026446435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24010799660094196035261913 18008099745070647026446435)
                  ·
                    refine ⟨27012149617605970539669653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18008099745070647026446435 27012149617605970539669653)
                    ·
                      refine ⟨1266194513325279869047015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27012149617605970539669653 1266194513325279869047015)
                      ·
                        rfl

theorem cell23_2465905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_2465905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465905 prefixEnd_2465905 := by exact prefixLift 2465905
  have htrace : WordTrace (prefixWord ++ tailWord_2465905) baseStart_2465905 baseEnd_2465905 := by
    simpa [prefixWord, tailWord_2465905, baseEnd_2465905] using wordTrace_append hprefix tailTrace_2465905
  have hstable : (prefixWord ++ tailWord_2465905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465905).length < 2 ^ (prefixWord ++ tailWord_2465905).sum := by decide
  have hdescent : baseEnd_2465905 < baseStart_2465905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465946 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2465946 : Nat := 118140960795 + 2465946 * 2 ^ 59
def prefixEnd_2465946 : Nat := 4983230072969 + 3 ^ 40 * 2465946 * 2
def baseEnd_2465946 : Nat := 1266215566032114208634327

theorem tailTrace_2465946 : CollatzResearch.WordTrace tailWord_2465946 prefixEnd_2465946 1266215566032114208634327 := by
  unfold tailWord_2465946
  simp only [CollatzResearch.WordTrace]
  refine ⟨22485109881076566723110423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59960293016204177928294461 22485109881076566723110423)
  ·
    refine ⟨33727664821614850084665635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22485109881076566723110423 33727664821614850084665635)
    ·
      refine ⟨50591497232422275126998453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33727664821614850084665635 50591497232422275126998453)
      ·
        refine ⟨4742952865539588293156105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50591497232422275126998453 4742952865539588293156105)
        ·
          refine ⟨3557214649154691219867079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4742952865539588293156105 3557214649154691219867079)
          ·
            refine ⟨5335821973732036829800619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3557214649154691219867079 5335821973732036829800619)
            ·
              refine ⟨8003732960598055244700929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5335821973732036829800619 8003732960598055244700929)
              ·
                refine ⟨6002799720448541433525697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8003732960598055244700929 6002799720448541433525697)
                ·
                  refine ⟨4502099790336406075144273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6002799720448541433525697 4502099790336406075144273)
                  ·
                    refine ⟨3376574842752304556358205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4502099790336406075144273 3376574842752304556358205)
                    ·
                      refine ⟨1266215566032114208634327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3376574842752304556358205 1266215566032114208634327)
                      ·
                        rfl

theorem cell23_2465946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2465946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465946 prefixEnd_2465946 := by exact prefixLift 2465946
  have htrace : WordTrace (prefixWord ++ tailWord_2465946) baseStart_2465946 baseEnd_2465946 := by
    simpa [prefixWord, tailWord_2465946, baseEnd_2465946] using wordTrace_append hprefix tailTrace_2465946
  have hstable : (prefixWord ++ tailWord_2465946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465946).length < 2 ^ (prefixWord ++ tailWord_2465946).sum := by decide
  have hdescent : baseEnd_2465946 < baseStart_2465946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465953 : List Nat := [1, 2, 3, 3, 1, 3, 3, 2, 1, 4]
def baseStart_2465953 : Nat := 118140960795 + 2465953 * 2 ^ 59
def prefixEnd_2465953 : Nat := 4983230072969 + 3 ^ 40 * 2465953 * 2
def baseEnd_2465953 : Nat := 422073053465565227082265

theorem tailTrace_2465953 : CollatzResearch.WordTrace tailWord_2465953 prefixEnd_2465953 422073053465565227082265 := by
  unfold tailWord_2465953
  simp only [CollatzResearch.WordTrace]
  refine ⟨89940694835280907087946513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59960463223520604725297675 89940694835280907087946513)
  ·
    refine ⟨67455521126460680315959885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89940694835280907087946513 67455521126460680315959885)
    ·
      refine ⟨25295820422422755118484957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67455521126460680315959885 25295820422422755118484957)
      ·
        refine ⟨9485932658408533169431859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25295820422422755118484957 9485932658408533169431859)
        ·
          refine ⟨14228898987612799754147789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9485932658408533169431859 14228898987612799754147789)
          ·
            refine ⟨5335837120354799907805421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14228898987612799754147789 5335837120354799907805421)
            ·
              refine ⟨2000938920133049965427033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5335837120354799907805421 2000938920133049965427033)
              ·
                refine ⟨1500704190099787474070275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2000938920133049965427033 1500704190099787474070275)
                ·
                  refine ⟨2251056285149681211105413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500704190099787474070275 2251056285149681211105413)
                  ·
                    refine ⟨422073053465565227082265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2251056285149681211105413 422073053465565227082265)
                    ·
                      rfl

theorem cell23_2465953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_2465953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465953 prefixEnd_2465953 := by exact prefixLift 2465953
  have htrace : WordTrace (prefixWord ++ tailWord_2465953) baseStart_2465953 baseEnd_2465953 := by
    simpa [prefixWord, tailWord_2465953, baseEnd_2465953] using wordTrace_append hprefix tailTrace_2465953
  have hstable : (prefixWord ++ tailWord_2465953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465953).length < 2 ^ (prefixWord ++ tailWord_2465953).sum := by decide
  have hdescent : baseEnd_2465953 < baseStart_2465953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465955 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 7]
def baseStart_2465955 : Nat := 118140960795 + 2465955 * 2 ^ 59
def prefixEnd_2465955 : Nat := 4983230072969 + 3 ^ 40 * 2465955 * 2
def baseEnd_2465955 : Nat := 1266220187358004673421785

theorem tailTrace_2465955 : CollatzResearch.WordTrace tailWord_2465955 prefixEnd_2465955 1266220187358004673421785 := by
  unfold tailWord_2465955
  simp only [CollatzResearch.WordTrace]
  refine ⟨89940767781273661429519319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59960511854182440953012879 89940767781273661429519319)
  ·
    refine ⟨134911151671910492144278979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89940767781273661429519319 134911151671910492144278979)
    ·
      refine ⟨202366727507865738216418469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134911151671910492144278979 202366727507865738216418469)
      ·
        refine ⟨37943761407724825915578463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202366727507865738216418469 37943761407724825915578463)
        ·
          refine ⟨56915642111587238873367695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37943761407724825915578463 56915642111587238873367695)
          ·
            refine ⟨85373463167380858310051543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56915642111587238873367695 85373463167380858310051543)
            ·
              refine ⟨128060194751071287465077315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85373463167380858310051543 128060194751071287465077315)
              ·
                refine ⟨192090292126606931197615973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128060194751071287465077315 192090292126606931197615973)
                ·
                  refine ⟨36016929773738799599552995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192090292126606931197615973 36016929773738799599552995)
                  ·
                    refine ⟨54025394660608199399329493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36016929773738799599552995 54025394660608199399329493)
                    ·
                      refine ⟨1266220187358004673421785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54025394660608199399329493 1266220187358004673421785)
                      ·
                        rfl

theorem cell23_2465955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_2465955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2465955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2465955 prefixEnd_2465955 := by exact prefixLift 2465955
  have htrace : WordTrace (prefixWord ++ tailWord_2465955) baseStart_2465955 baseEnd_2465955 := by
    simpa [prefixWord, tailWord_2465955, baseEnd_2465955] using wordTrace_append hprefix tailTrace_2465955
  have hstable : (prefixWord ++ tailWord_2465955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465955).length < 2 ^ (prefixWord ++ tailWord_2465955).sum := by decide
  have hdescent : baseEnd_2465955 < baseStart_2465955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466009 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 2, 4]
def baseStart_2466009 : Nat := 118140960795 + 2466009 * 2 ^ 59
def prefixEnd_2466009 : Nat := 4983230072969 + 3 ^ 40 * 2466009 * 2
def baseEnd_2466009 : Nat := 422082638437782487382179

theorem tailTrace_2466009 : CollatzResearch.WordTrace tailWord_2466009 prefixEnd_2466009 422082638437782487382179 := by
  unfold tailWord_2466009
  simp only [CollatzResearch.WordTrace]
  refine ⟨89942737323078028651985081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59961824882052019101323387 89942737323078028651985081)
  ·
    refine ⟨67457052992308521488988811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89942737323078028651985081 67457052992308521488988811)
    ·
      refine ⟨101185579488462782233483217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67457052992308521488988811 101185579488462782233483217)
      ·
        refine ⟨75889184616347086675112413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101185579488462782233483217 75889184616347086675112413)
        ·
          refine ⟨28458444231130157503167155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75889184616347086675112413 28458444231130157503167155)
          ·
            refine ⟨42687666346695236254750733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28458444231130157503167155 42687666346695236254750733)
            ·
              refine ⟨16007874880010713595531525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42687666346695236254750733 16007874880010713595531525)
              ·
                refine ⟨3001476540002008799162161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16007874880010713595531525 3001476540002008799162161)
                ·
                  refine ⟨2251107405001506599371621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3001476540002008799162161 2251107405001506599371621)
                  ·
                    refine ⟨422082638437782487382179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2251107405001506599371621 422082638437782487382179)
                    ·
                      rfl

theorem cell23_2466009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 4].length) (baseStart_2466009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466009 prefixEnd_2466009 := by exact prefixLift 2466009
  have htrace : WordTrace (prefixWord ++ tailWord_2466009) baseStart_2466009 baseEnd_2466009 := by
    simpa [prefixWord, tailWord_2466009, baseEnd_2466009] using wordTrace_append hprefix tailTrace_2466009
  have hstable : (prefixWord ++ tailWord_2466009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466009).length < 2 ^ (prefixWord ++ tailWord_2466009).sum := by decide
  have hdescent : baseEnd_2466009 < baseStart_2466009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466016 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2]
def baseStart_2466016 : Nat := 118140960795 + 2466016 * 2 ^ 59
def prefixEnd_2466016 : Nat := 4983230072969 + 3 ^ 40 * 2466016 * 2
def baseEnd_2466016 : Nat := 1266251509677928934759005

theorem tailTrace_2466016 : CollatzResearch.WordTrace tailWord_2466016 prefixEnd_2466016 1266251509677928934759005 := by
  unfold tailWord_2466016
  simp only [CollatzResearch.WordTrace]
  refine ⟨44971496317026334423744951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59961995089368445898326601 44971496317026334423744951)
  ·
    refine ⟨67457244475539501635617427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44971496317026334423744951 67457244475539501635617427)
    ·
      refine ⟨101185866713309252453426141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67457244475539501635617427 101185866713309252453426141)
      ·
        refine ⟨37944700017490969670034803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101185866713309252453426141 37944700017490969670034803)
        ·
          refine ⟨56917050026236454505052205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37944700017490969670034803 56917050026236454505052205)
          ·
            refine ⟨21343893759838670439394577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56917050026236454505052205 21343893759838670439394577)
            ·
              refine ⟨16007920319879002829545933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21343893759838670439394577 16007920319879002829545933)
              ·
                refine ⟨6002970119954626061079725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16007920319879002829545933 6002970119954626061079725)
                ·
                  refine ⟨2251113794982984772904897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6002970119954626061079725 2251113794982984772904897)
                  ·
                    refine ⟨1688335346237238579678673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2251113794982984772904897 1688335346237238579678673)
                    ·
                      refine ⟨1266251509677928934759005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688335346237238579678673 1266251509677928934759005)
                      ·
                        rfl

theorem cell23_2466016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_2466016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466016 prefixEnd_2466016 := by exact prefixLift 2466016
  have htrace : WordTrace (prefixWord ++ tailWord_2466016) baseStart_2466016 baseEnd_2466016 := by
    simpa [prefixWord, tailWord_2466016, baseEnd_2466016] using wordTrace_append hprefix tailTrace_2466016
  have hstable : (prefixWord ++ tailWord_2466016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466016).length < 2 ^ (prefixWord ++ tailWord_2466016).sum := by decide
  have hdescent : baseEnd_2466016 < baseStart_2466016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466049 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_2466049 : Nat := 118140960795 + 2466049 * 2 ^ 59
def prefixEnd_2466049 : Nat := 4983230072969 + 3 ^ 40 * 2466049 * 2
def baseEnd_2466049 : Nat := 1266268454539527305646353

theorem tailTrace_2466049 : CollatzResearch.WordTrace tailWord_2466049 prefixEnd_2466049 1266268454539527305646353 := by
  unfold tailWord_2466049
  simp only [CollatzResearch.WordTrace]
  refine ⟨89944196242933115483441201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59962797495288743655627467 89944196242933115483441201)
  ·
    refine ⟨67458147182199836612580901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89944196242933115483441201 67458147182199836612580901)
    ·
      refine ⟨12648402596662469364858919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67458147182199836612580901 12648402596662469364858919)
      ·
        refine ⟨18972603894993704047288379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12648402596662469364858919 18972603894993704047288379)
        ·
          refine ⟨28458905842490556070932569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18972603894993704047288379 28458905842490556070932569)
          ·
            refine ⟨21344179381867917053199427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28458905842490556070932569 21344179381867917053199427)
            ·
              refine ⟨32016269072801875579799141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21344179381867917053199427 32016269072801875579799141)
              ·
                refine ⟨6003050451150351671212339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32016269072801875579799141 6003050451150351671212339)
                ·
                  refine ⟨9004575676725527506818509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6003050451150351671212339 9004575676725527506818509)
                  ·
                    refine ⟨3376715878772072815056941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9004575676725527506818509 3376715878772072815056941)
                    ·
                      refine ⟨1266268454539527305646353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3376715878772072815056941 1266268454539527305646353)
                      ·
                        rfl

theorem cell23_2466049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_2466049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466049 prefixEnd_2466049 := by exact prefixLift 2466049
  have htrace : WordTrace (prefixWord ++ tailWord_2466049) baseStart_2466049 baseEnd_2466049 := by
    simpa [prefixWord, tailWord_2466049, baseEnd_2466049] using wordTrace_append hprefix tailTrace_2466049
  have hstable : (prefixWord ++ tailWord_2466049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466049).length < 2 ^ (prefixWord ++ tailWord_2466049).sum := by decide
  have hdescent : baseEnd_2466049 < baseStart_2466049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466050 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_2466050 : Nat := 118140960795 + 2466050 * 2 ^ 59
def prefixEnd_2466050 : Nat := 4983230072969 + 3 ^ 40 * 2466050 * 2
def baseEnd_2466050 : Nat := 1266268968020181801733849

theorem tailTrace_2466050 : CollatzResearch.WordTrace tailWord_2466050 prefixEnd_2466050 1266268968020181801733849 := by
  unfold tailWord_2466050
  simp only [CollatzResearch.WordTrace]
  refine ⟨22486058178982373163556901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59962821810619661769485069 22486058178982373163556901)
  ·
    refine ⟨4216135908559194968166919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22486058178982373163556901 4216135908559194968166919)
    ·
      refine ⟨6324203862838792452250379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4216135908559194968166919 6324203862838792452250379)
      ·
        refine ⟨9486305794258188678375569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6324203862838792452250379 9486305794258188678375569)
        ·
          refine ⟨7114729345693641508781677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9486305794258188678375569 7114729345693641508781677)
          ·
            refine ⟨2668023504635115565793129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7114729345693641508781677 2668023504635115565793129)
            ·
              refine ⟨2001017628476336674344847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2668023504635115565793129 2001017628476336674344847)
              ·
                refine ⟨3001526442714505011517271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2001017628476336674344847 3001526442714505011517271)
                ·
                  refine ⟨4502289664071757517275907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3001526442714505011517271 4502289664071757517275907)
                  ·
                    refine ⟨6753434496107636275913861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4502289664071757517275907 6753434496107636275913861)
                    ·
                      refine ⟨1266268968020181801733849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6753434496107636275913861 1266268968020181801733849)
                      ·
                        rfl

theorem cell23_2466050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_2466050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466050 prefixEnd_2466050 := by exact prefixLift 2466050
  have htrace : WordTrace (prefixWord ++ tailWord_2466050) baseStart_2466050 baseEnd_2466050 := by
    simpa [prefixWord, tailWord_2466050, baseEnd_2466050] using wordTrace_append hprefix tailTrace_2466050
  have hstable : (prefixWord ++ tailWord_2466050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466050).length < 2 ^ (prefixWord ++ tailWord_2466050).sum := by decide
  have hdescent : baseEnd_2466050 < baseStart_2466050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466083 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 2, 1, 3]
def baseStart_2466083 : Nat := 118140960795 + 2466083 * 2 ^ 59
def prefixEnd_2466083 : Nat := 4983230072969 + 3 ^ 40 * 2466083 * 2
def baseEnd_2466083 : Nat := 1266285912881780172621197

theorem tailTrace_2466083 : CollatzResearch.WordTrace tailWord_2466083 prefixEnd_2466083 1266285912881780172621197 := by
  unfold tailWord_2466083
  simp only [CollatzResearch.WordTrace]
  refine ⟨89945436324809939290178903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59963624216539959526785935 89945436324809939290178903)
  ·
    refine ⟨134918154487214908935268355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89945436324809939290178903 134918154487214908935268355)
    ·
      refine ⟨202377231730822363402902533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134918154487214908935268355 202377231730822363402902533)
      ·
        refine ⟨37945730949529193138044225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202377231730822363402902533 37945730949529193138044225)
        ·
          refine ⟨28459298212146894853533169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37945730949529193138044225 28459298212146894853533169)
          ·
            refine ⟨21344473659110171140149877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28459298212146894853533169 21344473659110171140149877)
            ·
              refine ⟨2001044405541578544389051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21344473659110171140149877 2001044405541578544389051)
              ·
                refine ⟨3001566608312367816583577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2001044405541578544389051 3001566608312367816583577)
                ·
                  refine ⟨2251174956234275862437683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3001566608312367816583577 2251174956234275862437683)
                  ·
                    refine ⟨3376762434351413793656525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2251174956234275862437683 3376762434351413793656525)
                    ·
                      refine ⟨1266285912881780172621197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3376762434351413793656525 1266285912881780172621197)
                      ·
                        rfl

theorem cell23_2466083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_2466083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466083 prefixEnd_2466083 := by exact prefixLift 2466083
  have htrace : WordTrace (prefixWord ++ tailWord_2466083) baseStart_2466083 baseEnd_2466083 := by
    simpa [prefixWord, tailWord_2466083, baseEnd_2466083] using wordTrace_append hprefix tailTrace_2466083
  have hstable : (prefixWord ++ tailWord_2466083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466083).length < 2 ^ (prefixWord ++ tailWord_2466083).sum := by decide
  have hdescent : baseEnd_2466083 < baseStart_2466083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466087 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2466087 : Nat := 118140960795 + 2466087 * 2 ^ 59
def prefixEnd_2466087 : Nat := 4983230072969 + 3 ^ 40 * 2466087 * 2
def baseEnd_2466087 : Nat := 1266287966804398156971179

theorem tailTrace_2466087 : CollatzResearch.WordTrace tailWord_2466087 prefixEnd_2466087 1266287966804398156971179 := by
  unfold tailWord_2466087
  simp only [CollatzResearch.WordTrace]
  refine ⟨89945582216795447973324515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59963721477863631982216343 89945582216795447973324515)
  ·
    refine ⟨134918373325193171959986773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89945582216795447973324515 134918373325193171959986773)
    ·
      refine ⟨1581074687404607483906095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 134918373325193171959986773 1581074687404607483906095)
      ·
        refine ⟨2371612031106911225859143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1581074687404607483906095 2371612031106911225859143)
        ·
          refine ⟨3557418046660366838788715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2371612031106911225859143 3557418046660366838788715)
          ·
            refine ⟨5336127069990550258183073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3557418046660366838788715 5336127069990550258183073)
            ·
              refine ⟨4002095302492912693637305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5336127069990550258183073 4002095302492912693637305)
              ·
                refine ⟨3001571476869684520227979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4002095302492912693637305 3001571476869684520227979)
                ·
                  refine ⟨4502357215304526780341969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3001571476869684520227979 4502357215304526780341969)
                  ·
                    refine ⟨3376767911478395085256477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4502357215304526780341969 3376767911478395085256477)
                    ·
                      refine ⟨1266287966804398156971179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3376767911478395085256477 1266287966804398156971179)
                      ·
                        rfl

theorem cell23_2466087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2466087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466087 prefixEnd_2466087 := by exact prefixLift 2466087
  have htrace : WordTrace (prefixWord ++ tailWord_2466087) baseStart_2466087 baseEnd_2466087 := by
    simpa [prefixWord, tailWord_2466087, baseEnd_2466087] using wordTrace_append hprefix tailTrace_2466087
  have hstable : (prefixWord ++ tailWord_2466087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466087).length < 2 ^ (prefixWord ++ tailWord_2466087).sum := by decide
  have hdescent : baseEnd_2466087 < baseStart_2466087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466129 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 7]
def baseStart_2466129 : Nat := 118140960795 + 2466129 * 2 ^ 59
def prefixEnd_2466129 : Nat := 4983230072969 + 3 ^ 40 * 2466129 * 2
def baseEnd_2466129 : Nat := 140701059221320776960665

theorem tailTrace_2466129 : CollatzResearch.WordTrace tailWord_2466129 prefixEnd_2466129 140701059221320776960665 := by
  unfold tailWord_2466129
  simp only [CollatzResearch.WordTrace]
  refine ⟨89947114082643289146353441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59964742721762192764235627 89947114082643289146353441)
  ·
    refine ⟨67460335561982466859765081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89947114082643289146353441 67460335561982466859765081)
    ·
      refine ⟨50595251671486850144823811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67460335561982466859765081 50595251671486850144823811)
      ·
        refine ⟨75892877507230275217235717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50595251671486850144823811 75892877507230275217235717)
        ·
          refine ⟨14229914532605676603231697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75892877507230275217235717 14229914532605676603231697)
          ·
            refine ⟨10672435899454257452423773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14229914532605676603231697 10672435899454257452423773)
            ·
              refine ⟨4002163462295346544658915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10672435899454257452423773 4002163462295346544658915)
              ·
                refine ⟨6003245193443019816988373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002163462295346544658915 6003245193443019816988373)
                ·
                  refine ⟨140701059221320776960665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6003245193443019816988373 140701059221320776960665)
                  ·
                    rfl

theorem cell23_2466129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 7].length) (baseStart_2466129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466129 prefixEnd_2466129 := by exact prefixLift 2466129
  have htrace : WordTrace (prefixWord ++ tailWord_2466129) baseStart_2466129 baseEnd_2466129 := by
    simpa [prefixWord, tailWord_2466129, baseEnd_2466129] using wordTrace_append hprefix tailTrace_2466129
  have hstable : (prefixWord ++ tailWord_2466129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466129).length < 2 ^ (prefixWord ++ tailWord_2466129).sum := by decide
  have hdescent : baseEnd_2466129 < baseStart_2466129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466236 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 8]
def baseStart_2466236 : Nat := 118140960795 + 2466236 * 2 ^ 59
def prefixEnd_2466236 : Nat := 4983230072969 + 3 ^ 40 * 2466236 * 2
def baseEnd_2466236 : Nat := 140707163935768674889777

theorem tailTrace_2466236 : CollatzResearch.WordTrace tailWord_2466236 prefixEnd_2466236 140707163935768674889777 := by
  unfold tailWord_2466236
  simp only [CollatzResearch.WordTrace]
  refine ⟨44975508346627823210249281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59967344462170430946999041 44975508346627823210249281)
  ·
    refine ⟨33731631259970867407686961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44975508346627823210249281 33731631259970867407686961)
    ·
      refine ⟨25298723444978150555765221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33731631259970867407686961 25298723444978150555765221)
      ·
        refine ⟨4743510645933403229205979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25298723444978150555765221 4743510645933403229205979)
        ·
          refine ⟨7115265968900104843808969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4743510645933403229205979 7115265968900104843808969)
          ·
            refine ⟨5336449476675078632856727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7115265968900104843808969 5336449476675078632856727)
            ·
              refine ⟨8004674215012617949285091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5336449476675078632856727 8004674215012617949285091)
              ·
                refine ⟨12007011322518926923927637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8004674215012617949285091 12007011322518926923927637)
                ·
                  refine ⟨140707163935768674889777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12007011322518926923927637 140707163935768674889777)
                  ·
                    rfl

theorem cell23_2466236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_2466236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466236 prefixEnd_2466236 := by exact prefixLift 2466236
  have htrace : WordTrace (prefixWord ++ tailWord_2466236) baseStart_2466236 baseEnd_2466236 := by
    simpa [prefixWord, tailWord_2466236, baseEnd_2466236] using wordTrace_append hprefix tailTrace_2466236
  have hstable : (prefixWord ++ tailWord_2466236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466236).length < 2 ^ (prefixWord ++ tailWord_2466236).sum := by decide
  have hdescent : baseEnd_2466236 < baseStart_2466236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466249 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 5, 5]
def baseStart_2466249 : Nat := 118140960795 + 2466249 * 2 ^ 59
def prefixEnd_2466249 : Nat := 4983230072969 + 3 ^ 40 * 2466249 * 2
def baseEnd_2466249 : Nat := 422123716890142174381811

theorem tailTrace_2466249 : CollatzResearch.WordTrace tailWord_2466249 prefixEnd_2466249 422123716890142174381811 := by
  unfold tailWord_2466249
  simp only [CollatzResearch.WordTrace]
  refine ⟨89951490842208549640721801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59967660561472366427147867 89951490842208549640721801)
  ·
    refine ⟨67463618131656412230541351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89951490842208549640721801 67463618131656412230541351)
    ·
      refine ⟨101195427197484618345812027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67463618131656412230541351 101195427197484618345812027)
      ·
        refine ⟨151793140796226927518718041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101195427197484618345812027 151793140796226927518718041)
        ·
          refine ⟨113844855597170195639038531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151793140796226927518718041 113844855597170195639038531)
          ·
            refine ⟨170767283395755293458557797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113844855597170195639038531 170767283395755293458557797)
            ·
              refine ⟨32018865636704117523479587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170767283395755293458557797 32018865636704117523479587)
              ·
                refine ⟨48028298455056176285219381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32018865636704117523479587 48028298455056176285219381)
                ·
                  refine ⟨4502652980161516526739317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48028298455056176285219381 4502652980161516526739317)
                  ·
                    refine ⟨422123716890142174381811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4502652980161516526739317 422123716890142174381811)
                    ·
                      rfl

theorem cell23_2466249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_2466249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466249 prefixEnd_2466249 := by exact prefixLift 2466249
  have htrace : WordTrace (prefixWord ++ tailWord_2466249) baseStart_2466249 baseEnd_2466249 := by
    simpa [prefixWord, tailWord_2466249, baseEnd_2466249] using wordTrace_append hprefix tailTrace_2466249
  have hstable : (prefixWord ++ tailWord_2466249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466249).length < 2 ^ (prefixWord ++ tailWord_2466249).sum := by decide
  have hdescent : baseEnd_2466249 < baseStart_2466249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466273 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 2, 3, 2]
def baseStart_2466273 : Nat := 118140960795 + 2466273 * 2 ^ 59
def prefixEnd_2466273 : Nat := 4983230072969 + 3 ^ 40 * 2466273 * 2
def baseEnd_2466273 : Nat := 1266383474206134429245323

theorem tailTrace_2466273 : CollatzResearch.WordTrace tailWord_2466273 prefixEnd_2466273 1266383474206134429245323 := by
  unfold tailWord_2466273
  simp only [CollatzResearch.WordTrace]
  refine ⟨89952366194121601739595473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59968244129414401159730315 89952366194121601739595473)
  ·
    refine ⟨67464274645591201304696605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89952366194121601739595473 67464274645591201304696605)
    ·
      refine ⟨25299102992096700489261227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67464274645591201304696605 25299102992096700489261227)
      ·
        refine ⟨37948654488145050733891841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25299102992096700489261227 37948654488145050733891841)
        ·
          refine ⟨28461490866108788050418881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37948654488145050733891841 28461490866108788050418881)
          ·
            refine ⟨21346118149581591037814161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28461490866108788050418881 21346118149581591037814161)
            ·
              refine ⟨16009588612186193278360621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21346118149581591037814161 16009588612186193278360621)
              ·
                refine ⟨6003595729569822479385233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16009588612186193278360621 6003595729569822479385233)
                ·
                  refine ⟨4502696797177366859538925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6003595729569822479385233 4502696797177366859538925)
                  ·
                    refine ⟨1688511298941512572327097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4502696797177366859538925 1688511298941512572327097)
                    ·
                      refine ⟨1266383474206134429245323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688511298941512572327097 1266383474206134429245323)
                      ·
                        rfl

theorem cell23_2466273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_2466273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466273 prefixEnd_2466273 := by exact prefixLift 2466273
  have htrace : WordTrace (prefixWord ++ tailWord_2466273) baseStart_2466273 baseEnd_2466273 := by
    simpa [prefixWord, tailWord_2466273, baseEnd_2466273] using wordTrace_append hprefix tailTrace_2466273
  have hstable : (prefixWord ++ tailWord_2466273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466273).length < 2 ^ (prefixWord ++ tailWord_2466273).sum := by decide
  have hdescent : baseEnd_2466273 < baseStart_2466273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466296 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 4, 4]
def baseStart_2466296 : Nat := 118140960795 + 2466296 * 2 ^ 59
def prefixEnd_2466296 : Nat := 4983230072969 + 3 ^ 40 * 2466296 * 2
def baseEnd_2466296 : Nat := 422131761420395946419239

theorem tailTrace_2466296 : CollatzResearch.WordTrace tailWord_2466296 prefixEnd_2466296 422131761420395946419239 := by
  unfold tailWord_2466296
  simp only [CollatzResearch.WordTrace]
  refine ⟨44976602536519138333841371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59968803382025517778455161 44976602536519138333841371)
  ·
    refine ⟨67464903804778707500762057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44976602536519138333841371 67464903804778707500762057)
    ·
      refine ⟨50598677853584030625571543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67464903804778707500762057 50598677853584030625571543)
      ·
        refine ⟨75898016780376045938357315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50598677853584030625571543 75898016780376045938357315)
        ·
          refine ⟨113847025170564068907535973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75898016780376045938357315 113847025170564068907535973)
          ·
            refine ⟨21346317219480762920162995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113847025170564068907535973 21346317219480762920162995)
            ·
              refine ⟨32019475829221144380244493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21346317219480762920162995 32019475829221144380244493)
              ·
                refine ⟨12007303435957929142591685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32019475829221144380244493 12007303435957929142591685)
                ·
                  refine ⟨2251369394242111714235941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12007303435957929142591685 2251369394242111714235941)
                  ·
                    refine ⟨422131761420395946419239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2251369394242111714235941 422131761420395946419239)
                    ·
                      rfl

theorem cell23_2466296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_2466296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466296 prefixEnd_2466296 := by exact prefixLift 2466296
  have htrace : WordTrace (prefixWord ++ tailWord_2466296) baseStart_2466296 baseEnd_2466296 := by
    simpa [prefixWord, tailWord_2466296, baseEnd_2466296] using wordTrace_append hprefix tailTrace_2466296
  have hstable : (prefixWord ++ tailWord_2466296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466296).length < 2 ^ (prefixWord ++ tailWord_2466296).sum := by decide
  have hdescent : baseEnd_2466296 < baseStart_2466296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466299 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 4]
def baseStart_2466299 : Nat := 118140960795 + 2466299 * 2 ^ 59
def prefixEnd_2466299 : Nat := 4983230072969 + 3 ^ 40 * 2466299 * 2
def baseEnd_2466299 : Nat := 1266396824703151327520203

theorem tailTrace_2466299 : CollatzResearch.WordTrace tailWord_2466299 prefixEnd_2466299 1266396824703151327520203 := by
  unfold tailWord_2466299
  simp only [CollatzResearch.WordTrace]
  refine ⟨89953314492027408180041951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59968876328018272120027967 89953314492027408180041951)
  ·
    refine ⟨134929971738041112270062927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89953314492027408180041951 134929971738041112270062927)
    ·
      refine ⟨202394957607061668405094391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134929971738041112270062927 202394957607061668405094391)
      ·
        refine ⟨303592436410592502607641587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202394957607061668405094391 303592436410592502607641587)
        ·
          refine ⟨455388654615888753911462381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303592436410592502607641587 455388654615888753911462381)
          ·
            refine ⟨170770745480958282716798393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455388654615888753911462381 170770745480958282716798393)
            ·
              refine ⟨128078059110718712037598795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170770745480958282716798393 128078059110718712037598795)
              ·
                refine ⟨192117088666078068056398193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128078059110718712037598795 192117088666078068056398193)
                ·
                  refine ⟨144087816499558551042298645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192117088666078068056398193 144087816499558551042298645)
                  ·
                    refine ⟨6754116398416807080107749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 144087816499558551042298645 6754116398416807080107749)
                    ·
                      refine ⟨1266396824703151327520203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6754116398416807080107749 1266396824703151327520203)
                      ·
                        rfl

theorem cell23_2466299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 4].length) (baseStart_2466299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466299 prefixEnd_2466299 := by exact prefixLift 2466299
  have htrace : WordTrace (prefixWord ++ tailWord_2466299) baseStart_2466299 baseEnd_2466299 := by
    simpa [prefixWord, tailWord_2466299, baseEnd_2466299] using wordTrace_append hprefix tailTrace_2466299
  have hstable : (prefixWord ++ tailWord_2466299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466299).length < 2 ^ (prefixWord ++ tailWord_2466299).sum := by decide
  have hdescent : baseEnd_2466299 < baseStart_2466299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466309 : List Nat := [1, 3, 1, 1, 2, 2, 3, 10]
def baseStart_2466309 : Nat := 118140960795 + 2466309 * 2 ^ 59
def prefixEnd_2466309 : Nat := 4983230072969 + 3 ^ 40 * 2466309 * 2
def baseEnd_2466309 : Nat := 46903776278136899570191

theorem tailTrace_2466309 : CollatzResearch.WordTrace tailWord_2466309 prefixEnd_2466309 46903776278136899570191 := by
  unfold tailWord_2466309
  simp only [CollatzResearch.WordTrace]
  refine ⟨89953679221991179887905981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59969119481327453258603987 89953679221991179887905981)
  ·
    refine ⟨33732629708246692457964743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89953679221991179887905981 33732629708246692457964743)
    ·
      refine ⟨50598944562370038686947115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33732629708246692457964743 50598944562370038686947115)
      ·
        refine ⟨75898416843555058030420673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50598944562370038686947115 75898416843555058030420673)
        ·
          refine ⟨56923812632666293522815505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75898416843555058030420673 56923812632666293522815505)
          ·
            refine ⟨42692859474499720142111629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56923812632666293522815505 42692859474499720142111629)
            ·
              refine ⟨16009822302937395053291861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42692859474499720142111629 16009822302937395053291861)
              ·
                refine ⟨46903776278136899570191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16009822302937395053291861 46903776278136899570191)
                ·
                  rfl

theorem cell23_2466309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 10].length) (baseStart_2466309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466309 prefixEnd_2466309 := by exact prefixLift 2466309
  have htrace : WordTrace (prefixWord ++ tailWord_2466309) baseStart_2466309 baseEnd_2466309 := by
    simpa [prefixWord, tailWord_2466309, baseEnd_2466309] using wordTrace_append hprefix tailTrace_2466309
  have hstable : (prefixWord ++ tailWord_2466309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466309).length < 2 ^ (prefixWord ++ tailWord_2466309).sum := by decide
  have hdescent : baseEnd_2466309 < baseStart_2466309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466316 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_2466316 : Nat := 118140960795 + 2466316 * 2 ^ 59
def prefixEnd_2466316 : Nat := 4983230072969 + 3 ^ 40 * 2466316 * 2
def baseEnd_2466316 : Nat := 1266405553874277761007625

theorem tailTrace_2466316 : CollatzResearch.WordTrace tailWord_2466316 prefixEnd_2466316 1266405553874277761007625 := by
  unfold tailWord_2466316
  simp only [CollatzResearch.WordTrace]
  refine ⟨44976967266482910041705401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59969289688643880055607201 44976967266482910041705401)
  ·
    refine ⟨33732725449862182531279051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44976967266482910041705401 33732725449862182531279051)
    ·
      refine ⟨50599088174793273796918577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33732725449862182531279051 50599088174793273796918577)
      ·
        refine ⟨37949316131094955347688933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50599088174793273796918577 37949316131094955347688933)
        ·
          refine ⟨7115496774580304127691675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37949316131094955347688933 7115496774580304127691675)
          ·
            refine ⟨10673245161870456191537513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7115496774580304127691675 10673245161870456191537513)
            ·
              refine ⟨8004933871402842143653135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10673245161870456191537513 8004933871402842143653135)
              ·
                refine ⟨12007400807104263215479703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8004933871402842143653135 12007400807104263215479703)
                ·
                  refine ⟨18011101210656394823219555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12007400807104263215479703 18011101210656394823219555)
                  ·
                    refine ⟨27016651815984592234829333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18011101210656394823219555 27016651815984592234829333)
                    ·
                      refine ⟨1266405553874277761007625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27016651815984592234829333 1266405553874277761007625)
                      ·
                        rfl

theorem cell23_2466316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_2466316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466316 prefixEnd_2466316 := by exact prefixLift 2466316
  have htrace : WordTrace (prefixWord ++ tailWord_2466316) baseStart_2466316 baseEnd_2466316 := by
    simpa [prefixWord, tailWord_2466316, baseEnd_2466316] using wordTrace_append hprefix tailTrace_2466316
  have hstable : (prefixWord ++ tailWord_2466316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466316).length < 2 ^ (prefixWord ++ tailWord_2466316).sum := by decide
  have hdescent : baseEnd_2466316 < baseStart_2466316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466317 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2466317 : Nat := 118140960795 + 2466317 * 2 ^ 59
def prefixEnd_2466317 : Nat := 4983230072969 + 3 ^ 40 * 2466317 * 2
def baseEnd_2466317 : Nat := 422135355784977419031707

theorem tailTrace_2466317 : CollatzResearch.WordTrace tailWord_2466317 prefixEnd_2466317 422135355784977419031707 := by
  unfold tailWord_2466317
  simp only [CollatzResearch.WordTrace]
  refine ⟨89953971005962197254197205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59969314003974798169464803 89953971005962197254197205)
  ·
    refine ⟨2108296195452238998145247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 89953971005962197254197205 2108296195452238998145247)
    ·
      refine ⟨3162444293178358497217871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2108296195452238998145247 3162444293178358497217871)
      ·
        refine ⟨4743666439767537745826807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3162444293178358497217871 4743666439767537745826807)
        ·
          refine ⟨7115499659651306618740211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4743666439767537745826807 7115499659651306618740211)
          ·
            refine ⟨10673249489476959928110317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7115499659651306618740211 10673249489476959928110317)
            ·
              refine ⟨4002468558553859973041369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10673249489476959928110317 4002468558553859973041369)
              ·
                refine ⟨3001851418915394979781027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4002468558553859973041369 3001851418915394979781027)
                ·
                  refine ⟨4502777128373092469671541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3001851418915394979781027 4502777128373092469671541)
                  ·
                    refine ⟨422135355784977419031707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4502777128373092469671541 422135355784977419031707)
                    ·
                      rfl

theorem cell23_2466317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2466317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466317 prefixEnd_2466317 := by exact prefixLift 2466317
  have htrace : WordTrace (prefixWord ++ tailWord_2466317) baseStart_2466317 baseEnd_2466317 := by
    simpa [prefixWord, tailWord_2466317, baseEnd_2466317] using wordTrace_append hprefix tailTrace_2466317
  have hstable : (prefixWord ++ tailWord_2466317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466317).length < 2 ^ (prefixWord ++ tailWord_2466317).sum := by decide
  have hdescent : baseEnd_2466317 < baseStart_2466317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466329 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_2466329 : Nat := 118140960795 + 2466329 * 2 ^ 59
def prefixEnd_2466329 : Nat := 4983230072969 + 3 ^ 40 * 2466329 * 2
def baseEnd_2466329 : Nat := 1266412229122786210145065

theorem tailTrace_2466329 : CollatzResearch.WordTrace tailWord_2466329 prefixEnd_2466329 1266412229122786210145065 := by
  unfold tailWord_2466329
  simp only [CollatzResearch.WordTrace]
  refine ⟨89954408681918723303634041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59969605787945815535756027 89954408681918723303634041)
  ·
    refine ⟨67465806511439042477725531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89954408681918723303634041 67465806511439042477725531)
    ·
      refine ⟨101198709767158563716588297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67465806511439042477725531 101198709767158563716588297)
      ·
        refine ⟨75899032325368922787441223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101198709767158563716588297 75899032325368922787441223)
        ·
          refine ⟨113848548488053384181161835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75899032325368922787441223 113848548488053384181161835)
          ·
            refine ⟨170772822732080076271742753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113848548488053384181161835 170772822732080076271742753)
            ·
              refine ⟨128079617049060057203807065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170772822732080076271742753 128079617049060057203807065)
              ·
                refine ⟨96059712786795042902855299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128079617049060057203807065 96059712786795042902855299)
                ·
                  refine ⟨144089569180192564354282949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96059712786795042902855299 144089569180192564354282949)
                  ·
                    refine ⟨27016794221286105816428053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144089569180192564354282949 27016794221286105816428053)
                    ·
                      refine ⟨1266412229122786210145065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27016794221286105816428053 1266412229122786210145065)
                      ·
                        rfl

theorem cell23_2466329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_2466329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466329 prefixEnd_2466329 := by exact prefixLift 2466329
  have htrace : WordTrace (prefixWord ++ tailWord_2466329) baseStart_2466329 baseEnd_2466329 := by
    simpa [prefixWord, tailWord_2466329, baseEnd_2466329] using wordTrace_append hprefix tailTrace_2466329
  have hstable : (prefixWord ++ tailWord_2466329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466329).length < 2 ^ (prefixWord ++ tailWord_2466329).sum := by decide
  have hdescent : baseEnd_2466329 < baseStart_2466329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466333 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2466333 : Nat := 118140960795 + 2466333 * 2 ^ 59
def prefixEnd_2466333 : Nat := 4983230072969 + 3 ^ 40 * 2466333 * 2
def baseEnd_2466333 : Nat := 1266414283045404194495047

theorem tailTrace_2466333 : CollatzResearch.WordTrace tailWord_2466333 prefixEnd_2466333 1266414283045404194495047 := by
  unfold tailWord_2466333
  simp only [CollatzResearch.WordTrace]
  refine ⟨89954554573904231986779653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59969703049269487991186435 89954554573904231986779653)
  ·
    refine ⟨16866478982607043497521185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89954554573904231986779653 16866478982607043497521185)
    ·
      refine ⟨12649859236955282623140889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16866478982607043497521185 12649859236955282623140889)
      ·
        refine ⟨9487394427716461967355667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12649859236955282623140889 9487394427716461967355667)
        ·
          refine ⟨14231091641574692951033501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9487394427716461967355667 14231091641574692951033501)
          ·
            refine ⟨5336659365590509856637563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14231091641574692951033501 5336659365590509856637563)
            ·
              refine ⟨8004989048385764784956345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5336659365590509856637563 8004989048385764784956345)
              ·
                refine ⟨6003741786289323588717259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8004989048385764784956345 6003741786289323588717259)
                ·
                  refine ⟨9005612679433985383075889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6003741786289323588717259 9005612679433985383075889)
                  ·
                    refine ⟨6754209509575489037306917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9005612679433985383075889 6754209509575489037306917)
                    ·
                      refine ⟨1266414283045404194495047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6754209509575489037306917 1266414283045404194495047)
                      ·
                        rfl

theorem cell23_2466333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2466333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466333 prefixEnd_2466333 := by exact prefixLift 2466333
  have htrace : WordTrace (prefixWord ++ tailWord_2466333) baseStart_2466333 baseEnd_2466333 := by
    simpa [prefixWord, tailWord_2466333, baseEnd_2466333] using wordTrace_append hprefix tailTrace_2466333
  have hstable : (prefixWord ++ tailWord_2466333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466333).length < 2 ^ (prefixWord ++ tailWord_2466333).sum := by decide
  have hdescent : baseEnd_2466333 < baseStart_2466333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466337 : List Nat := [1, 2, 3, 2, 2, 1, 2, 5, 1, 2, 2]
def baseStart_2466337 : Nat := 118140960795 + 2466337 * 2 ^ 59
def prefixEnd_2466337 : Nat := 4983230072969 + 3 ^ 40 * 2466337 * 2
def baseEnd_2466337 : Nat := 1266416336968022178845029

theorem tailTrace_2466337 : CollatzResearch.WordTrace tailWord_2466337 prefixEnd_2466337 1266416336968022178845029 := by
  unfold tailWord_2466337
  simp only [CollatzResearch.WordTrace]
  refine ⟨89954700465889740669925265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59969800310593160446616843 89954700465889740669925265)
  ·
    refine ⟨67466025349417305502443949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89954700465889740669925265 67466025349417305502443949)
    ·
      refine ⟨25299759506031489563416481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67466025349417305502443949 25299759506031489563416481)
      ·
        refine ⟨18974819629523617172562361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25299759506031489563416481 18974819629523617172562361)
        ·
          refine ⟨14231114722142712879421771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18974819629523617172562361 14231114722142712879421771)
          ·
            refine ⟨21346672083214069319132657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14231114722142712879421771 21346672083214069319132657)
            ·
              refine ⟨16010004062410551989349493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21346672083214069319132657 16010004062410551989349493)
              ·
                refine ⟨1500937880850989249001515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16010004062410551989349493 1500937880850989249001515)
                ·
                  refine ⟨2251406821276483873502273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500937880850989249001515 2251406821276483873502273)
                  ·
                    refine ⟨1688555115957362905126705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2251406821276483873502273 1688555115957362905126705)
                    ·
                      refine ⟨1266416336968022178845029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688555115957362905126705 1266416336968022178845029)
                      ·
                        rfl

theorem cell23_2466337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_2466337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466337 prefixEnd_2466337 := by exact prefixLift 2466337
  have htrace : WordTrace (prefixWord ++ tailWord_2466337) baseStart_2466337 baseEnd_2466337 := by
    simpa [prefixWord, tailWord_2466337, baseEnd_2466337] using wordTrace_append hprefix tailTrace_2466337
  have hstable : (prefixWord ++ tailWord_2466337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466337).length < 2 ^ (prefixWord ++ tailWord_2466337).sum := by decide
  have hdescent : baseEnd_2466337 < baseStart_2466337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466343 : List Nat := [1, 1, 7, 2, 1, 11]
def baseStart_2466343 : Nat := 118140960795 + 2466343 * 2 ^ 59
def prefixEnd_2466343 : Nat := 4983230072969 + 3 ^ 40 * 2466343 * 2
def baseEnd_2466343 : Nat := 5211602542600613808107

theorem tailTrace_2466343 : CollatzResearch.WordTrace tailWord_2466343 prefixEnd_2466343 5211602542600613808107 := by
  unfold tailWord_2466343
  simp only [CollatzResearch.WordTrace]
  refine ⟨89954919303868003694643683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59969946202578669129762455 89954919303868003694643683)
  ·
    refine ⟨134932378955802005541965525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89954919303868003694643683 134932378955802005541965525)
    ·
      refine ⟨3162477631776609504889817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 134932378955802005541965525 3162477631776609504889817)
      ·
        refine ⟨2371858223832457128667363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3162477631776609504889817 2371858223832457128667363)
        ·
          refine ⟨3557787335748685693001045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2371858223832457128667363 3557787335748685693001045)
          ·
            refine ⟨5211602542600613808107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3557787335748685693001045 5211602542600613808107)
            ·
              rfl

theorem cell23_2466343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 11].length) (baseStart_2466343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466343 prefixEnd_2466343 := by exact prefixLift 2466343
  have htrace : WordTrace (prefixWord ++ tailWord_2466343) baseStart_2466343 baseEnd_2466343 := by
    simpa [prefixWord, tailWord_2466343, baseEnd_2466343] using wordTrace_append hprefix tailTrace_2466343
  have hstable : (prefixWord ++ tailWord_2466343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466343).length < 2 ^ (prefixWord ++ tailWord_2466343).sum := by decide
  have hdescent : baseEnd_2466343 < baseStart_2466343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466353 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 4, 1, 3]
def baseStart_2466353 : Nat := 118140960795 + 2466353 * 2 ^ 59
def prefixEnd_2466353 : Nat := 4983230072969 + 3 ^ 40 * 2466353 * 2
def baseEnd_2466353 : Nat := 1266424552658494116244955

theorem tailTrace_2466353 : CollatzResearch.WordTrace tailWord_2466353 prefixEnd_2466353 1266424552658494116244955 := by
  unfold tailWord_2466353
  simp only [CollatzResearch.WordTrace]
  refine ⟨89955284033831775402507713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59970189355887850268338475 89955284033831775402507713)
  ·
    refine ⟨67466463025373831551880785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89955284033831775402507713 67466463025373831551880785)
    ·
      refine ⟨50599847269030373663910589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67466463025373831551880785 50599847269030373663910589)
      ·
        refine ⟨18974942725886390123966471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50599847269030373663910589 18974942725886390123966471)
        ·
          refine ⟨28462414088829585185949707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18974942725886390123966471 28462414088829585185949707)
          ·
            refine ⟨42693621133244377778924561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28462414088829585185949707 42693621133244377778924561)
            ·
              refine ⟨32020215849933283334193421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42693621133244377778924561 32020215849933283334193421)
              ·
                refine ⟨12007580943724981250322533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32020215849933283334193421 12007580943724981250322533)
                ·
                  refine ⟨2251421426948433984435475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12007580943724981250322533 2251421426948433984435475)
                  ·
                    refine ⟨3377132140422650976653213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2251421426948433984435475 3377132140422650976653213)
                    ·
                      refine ⟨1266424552658494116244955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3377132140422650976653213 1266424552658494116244955)
                      ·
                        rfl

theorem cell23_2466353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_2466353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466353 prefixEnd_2466353 := by exact prefixLift 2466353
  have htrace : WordTrace (prefixWord ++ tailWord_2466353) baseStart_2466353 baseEnd_2466353 := by
    simpa [prefixWord, tailWord_2466353, baseEnd_2466353] using wordTrace_append hprefix tailTrace_2466353
  have hstable : (prefixWord ++ tailWord_2466353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466353).length < 2 ^ (prefixWord ++ tailWord_2466353).sum := by decide
  have hdescent : baseEnd_2466353 < baseStart_2466353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466354 : List Nat := [3, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2]
def baseStart_2466354 : Nat := 118140960795 + 2466354 * 2 ^ 59
def prefixEnd_2466354 : Nat := 4983230072969 + 3 ^ 40 * 2466354 * 2
def baseEnd_2466354 : Nat := 1266425066139148612332451

theorem tailTrace_2466354 : CollatzResearch.WordTrace tailWord_2466354 prefixEnd_2466354 1266425066139148612332451 := by
  unfold tailWord_2466354
  simp only [CollatzResearch.WordTrace]
  refine ⟨22488830126707038143323529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59970213671218768382196077 22488830126707038143323529)
  ·
    refine ⟨16866622595030278607492647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22488830126707038143323529 16866622595030278607492647)
    ·
      refine ⟨25299933892545417911238971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16866622595030278607492647 25299933892545417911238971)
      ·
        refine ⟨37949900838818126866858457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25299933892545417911238971 37949900838818126866858457)
        ·
          refine ⟨28462425629113595150143843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37949900838818126866858457 28462425629113595150143843)
          ·
            refine ⟨42693638443670392725215765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28462425629113595150143843 42693638443670392725215765)
            ·
              refine ⟨2001264302047049658994489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42693638443670392725215765 2001264302047049658994489)
              ·
                refine ⟨1500948226535287244245867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001264302047049658994489 1500948226535287244245867)
                ·
                  refine ⟨2251422339802930866368801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500948226535287244245867 2251422339802930866368801)
                  ·
                    refine ⟨1688566754852198149776601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2251422339802930866368801 1688566754852198149776601)
                    ·
                      refine ⟨1266425066139148612332451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688566754852198149776601 1266425066139148612332451)
                      ·
                        rfl

theorem cell23_2466354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_2466354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466354 prefixEnd_2466354 := by exact prefixLift 2466354
  have htrace : WordTrace (prefixWord ++ tailWord_2466354) baseStart_2466354 baseEnd_2466354 := by
    simpa [prefixWord, tailWord_2466354, baseEnd_2466354] using wordTrace_append hprefix tailTrace_2466354
  have hstable : (prefixWord ++ tailWord_2466354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466354).length < 2 ^ (prefixWord ++ tailWord_2466354).sum := by decide
  have hdescent : baseEnd_2466354 < baseStart_2466354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466380 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 1, 3, 2]
def baseStart_2466380 : Nat := 118140960795 + 2466380 * 2 ^ 59
def prefixEnd_2466380 : Nat := 4983230072969 + 3 ^ 40 * 2466380 * 2
def baseEnd_2466380 : Nat := 1266438416636165510607331

theorem tailTrace_2466380 : CollatzResearch.WordTrace tailWord_2466380 prefixEnd_2466380 1266438416636165510607331 := by
  unfold tailWord_2466380
  simp only [CollatzResearch.WordTrace]
  refine ⟨44978134402366979506870297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59970845869822639342493729 44978134402366979506870297)
  ·
    refine ⟨33733600801775234630152723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44978134402366979506870297 33733600801775234630152723)
    ·
      refine ⟨50600401202662851945229085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33733600801775234630152723 50600401202662851945229085)
      ·
        refine ⟨18975150450998569479460907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50600401202662851945229085 18975150450998569479460907)
        ·
          refine ⟨28462725676497854219191361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18975150450998569479460907 28462725676497854219191361)
          ·
            refine ⟨21347044257373390664393521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28462725676497854219191361 21347044257373390664393521)
            ·
              refine ⟨16010283193030042998295141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21347044257373390664393521 16010283193030042998295141)
              ·
                refine ⟨3001928098693133062180339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16010283193030042998295141 3001928098693133062180339)
                ·
                  refine ⟨4502892148039699593270509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3001928098693133062180339 4502892148039699593270509)
                  ·
                    refine ⟨1688584555514887347476441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4502892148039699593270509 1688584555514887347476441)
                    ·
                      refine ⟨1266438416636165510607331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688584555514887347476441 1266438416636165510607331)
                      ·
                        rfl

theorem cell23_2466380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_2466380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466380 prefixEnd_2466380 := by exact prefixLift 2466380
  have htrace : WordTrace (prefixWord ++ tailWord_2466380) baseStart_2466380 baseEnd_2466380 := by
    simpa [prefixWord, tailWord_2466380, baseEnd_2466380] using wordTrace_append hprefix tailTrace_2466380
  have hstable : (prefixWord ++ tailWord_2466380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466380).length < 2 ^ (prefixWord ++ tailWord_2466380).sum := by decide
  have hdescent : baseEnd_2466380 < baseStart_2466380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466386 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_2466386 : Nat := 118140960795 + 2466386 * 2 ^ 59
def prefixEnd_2466386 : Nat := 4983230072969 + 3 ^ 40 * 2466386 * 2
def baseEnd_2466386 : Nat := 422147165840030829044101

theorem tailTrace_2466386 : CollatzResearch.WordTrace tailWord_2466386 prefixEnd_2466386 422147165840030829044101 := by
  unfold tailWord_2466386
  simp only [CollatzResearch.WordTrace]
  refine ⟨22489121910678055509614753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59970991761808148025639341 22489121910678055509614753)
  ·
    refine ⟨16866841433008541632211065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22489121910678055509614753 16866841433008541632211065)
    ·
      refine ⟨12650131074756406224158299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16866841433008541632211065 12650131074756406224158299)
      ·
        refine ⟨18975196612134609336237449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12650131074756406224158299 18975196612134609336237449)
        ·
          refine ⟨14231397459100957002178087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18975196612134609336237449 14231397459100957002178087)
          ·
            refine ⟨21347096188651435503267131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14231397459100957002178087 21347096188651435503267131)
            ·
              refine ⟨32020644282977153254900697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21347096188651435503267131 32020644282977153254900697)
              ·
                refine ⟨24015483212232864941175523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32020644282977153254900697 24015483212232864941175523)
                ·
                  refine ⟨36023224818349297411763285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24015483212232864941175523 36023224818349297411763285)
                  ·
                    refine ⟨422147165840030829044101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36023224818349297411763285 422147165840030829044101)
                    ·
                      rfl

theorem cell23_2466386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_2466386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466386 prefixEnd_2466386 := by exact prefixLift 2466386
  have htrace : WordTrace (prefixWord ++ tailWord_2466386) baseStart_2466386 baseEnd_2466386 := by
    simpa [prefixWord, tailWord_2466386, baseEnd_2466386] using wordTrace_append hprefix tailTrace_2466386
  have hstable : (prefixWord ++ tailWord_2466386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466386).length < 2 ^ (prefixWord ++ tailWord_2466386).sum := by decide
  have hdescent : baseEnd_2466386 < baseStart_2466386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466398 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_2466398 : Nat := 118140960795 + 2466398 * 2 ^ 59
def prefixEnd_2466398 : Nat := 4983230072969 + 3 ^ 40 * 2466398 * 2
def baseEnd_2466398 : Nat := 422149219762648813394083

theorem tailTrace_2466398 : CollatzResearch.WordTrace tailWord_2466398 prefixEnd_2466398 422149219762648813394083 := by
  unfold tailWord_2466398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244615664833593510986981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59971283545779165391930565 11244615664833593510986981)
  ·
    refine ⟨2108365437156298783310059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11244615664833593510986981 2108365437156298783310059)
    ·
      refine ⟨3162548155734448174965089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2108365437156298783310059 3162548155734448174965089)
      ·
        refine ⟨2371911116800836131223817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3162548155734448174965089 2371911116800836131223817)
        ·
          refine ⟨1778933337600627098417863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2371911116800836131223817 1778933337600627098417863)
          ·
            refine ⟨2668400006400940647626795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778933337600627098417863 2668400006400940647626795)
            ·
              refine ⟨4002600009601410971440193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668400006400940647626795 4002600009601410971440193)
              ·
                refine ⟨3001950007201058228580145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4002600009601410971440193 3001950007201058228580145)
                ·
                  refine ⟨2251462505400793671435109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3001950007201058228580145 2251462505400793671435109)
                  ·
                    refine ⟨422149219762648813394083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2251462505400793671435109 422149219762648813394083)
                    ·
                      rfl

theorem cell23_2466398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_2466398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466398 prefixEnd_2466398 := by exact prefixLift 2466398
  have htrace : WordTrace (prefixWord ++ tailWord_2466398) baseStart_2466398 baseEnd_2466398 := by
    simpa [prefixWord, tailWord_2466398, baseEnd_2466398] using wordTrace_append hprefix tailTrace_2466398
  have hstable : (prefixWord ++ tailWord_2466398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466398).length < 2 ^ (prefixWord ++ tailWord_2466398).sum := by decide
  have hdescent : baseEnd_2466398 < baseStart_2466398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466453 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 3, 7, 2]
def baseStart_2466453 : Nat := 118140960795 + 2466453 * 2 ^ 59
def prefixEnd_2466453 : Nat := 4983230072969 + 3 ^ 40 * 2466453 * 2
def baseEnd_2466453 : Nat := 1266475900723943724994495

theorem tailTrace_2466453 : CollatzResearch.WordTrace tailWord_2466453 prefixEnd_2466453 1266475900723943724994495 := by
  unfold tailWord_2466453
  simp only [CollatzResearch.WordTrace]
  refine ⟨89958931333469492481148013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59972620888979661654098675 89958931333469492481148013)
  ·
    refine ⟨33734599250051059680430505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89958931333469492481148013 33734599250051059680430505)
    ·
      refine ⟨25300949437538294760322879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33734599250051059680430505 25300949437538294760322879)
      ·
        refine ⟨37951424156307442140484319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25300949437538294760322879 37951424156307442140484319)
        ·
          refine ⟨56927136234461163210726479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37951424156307442140484319 56927136234461163210726479)
          ·
            refine ⟨85390704351691744816089719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56927136234461163210726479 85390704351691744816089719)
            ·
              refine ⟨128086056527537617224134579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85390704351691744816089719 128086056527537617224134579)
              ·
                refine ⟨192129084791306425836201869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128086056527537617224134579 192129084791306425836201869)
                ·
                  refine ⟨72048406796739909688575701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192129084791306425836201869 72048406796739909688575701)
                  ·
                    refine ⟨1688634534298591633325993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 72048406796739909688575701 1688634534298591633325993)
                    ·
                      refine ⟨1266475900723943724994495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688634534298591633325993 1266475900723943724994495)
                      ·
                        rfl

theorem cell23_2466453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_2466453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466453 prefixEnd_2466453 := by exact prefixLift 2466453
  have htrace : WordTrace (prefixWord ++ tailWord_2466453) baseStart_2466453 baseEnd_2466453 := by
    simpa [prefixWord, tailWord_2466453, baseEnd_2466453] using wordTrace_append hprefix tailTrace_2466453
  have hstable : (prefixWord ++ tailWord_2466453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466453).length < 2 ^ (prefixWord ++ tailWord_2466453).sum := by decide
  have hdescent : baseEnd_2466453 < baseStart_2466453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466478 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_2466478 : Nat := 118140960795 + 2466478 * 2 ^ 59
def prefixEnd_2466478 : Nat := 4983230072969 + 3 ^ 40 * 2466478 * 2
def baseEnd_2466478 : Nat := 1266488737740306127181881

theorem tailTrace_2466478 : CollatzResearch.WordTrace tailWord_2466478 prefixEnd_2466478 1266488737740306127181881 := by
  unfold tailWord_2466478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244980394797365218851011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59973228772252614500538725 11244980394797365218851011)
  ·
    refine ⟨16867470592196047828276517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11244980394797365218851011 16867470592196047828276517)
    ·
      refine ⟨3162650736036758967801847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16867470592196047828276517 3162650736036758967801847)
      ·
        refine ⟨4743976104055138451702771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3162650736036758967801847 4743976104055138451702771)
        ·
          refine ⟨7115964156082707677554157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4743976104055138451702771 7115964156082707677554157)
          ·
            refine ⟨2668486558531015379082809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7115964156082707677554157 2668486558531015379082809)
            ·
              refine ⟨2001364918898261534312107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2668486558531015379082809 2001364918898261534312107)
              ·
                refine ⟨3002047378347392301468161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2001364918898261534312107 3002047378347392301468161)
                ·
                  refine ⟨2251535533760544226101121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3002047378347392301468161 2251535533760544226101121)
                  ·
                    refine ⟨1688651650320408169575841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2251535533760544226101121 1688651650320408169575841)
                    ·
                      refine ⟨1266488737740306127181881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688651650320408169575841 1266488737740306127181881)
                      ·
                        rfl

theorem cell23_2466478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_2466478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466478 prefixEnd_2466478 := by exact prefixLift 2466478
  have htrace : WordTrace (prefixWord ++ tailWord_2466478) baseStart_2466478 baseEnd_2466478 := by
    simpa [prefixWord, tailWord_2466478, baseEnd_2466478] using wordTrace_append hprefix tailTrace_2466478
  have hstable : (prefixWord ++ tailWord_2466478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466478).length < 2 ^ (prefixWord ++ tailWord_2466478).sum := by decide
  have hdescent : baseEnd_2466478 < baseStart_2466478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466500 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2466500 : Nat := 118140960795 + 2466500 * 2 ^ 59
def prefixEnd_2466500 : Nat := 4983230072969 + 3 ^ 40 * 2466500 * 2
def baseEnd_2466500 : Nat := 1266500034314705041106779

theorem tailTrace_2466500 : CollatzResearch.WordTrace tailWord_2466500 prefixEnd_2466500 1266500034314705041106779 := by
  unfold tailWord_2466500
  simp only [CollatzResearch.WordTrace]
  refine ⟨44980322782149609754054477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59973763709532813005405969 44980322782149609754054477)
  ·
    refine ⟨16867621043306103657770429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44980322782149609754054477 16867621043306103657770429)
    ·
      refine ⟨6325357891239788871663911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16867621043306103657770429 6325357891239788871663911)
      ·
        refine ⟨9488036836859683307495867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6325357891239788871663911 9488036836859683307495867)
        ·
          refine ⟨14232055255289524961243801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9488036836859683307495867 14232055255289524961243801)
          ·
            refine ⟨10674041441467143720932851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14232055255289524961243801 10674041441467143720932851)
            ·
              refine ⟨16011062162200715581399277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10674041441467143720932851 16011062162200715581399277)
              ·
                refine ⟨6004148310825268343024729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16011062162200715581399277 6004148310825268343024729)
                ·
                  refine ⟨4503111233118951257268547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6004148310825268343024729 4503111233118951257268547)
                  ·
                    refine ⟨6754666849678426885902821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4503111233118951257268547 6754666849678426885902821)
                    ·
                      refine ⟨1266500034314705041106779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6754666849678426885902821 1266500034314705041106779)
                      ·
                        rfl

theorem cell23_2466500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2466500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466500 prefixEnd_2466500 := by exact prefixLift 2466500
  have htrace : WordTrace (prefixWord ++ tailWord_2466500) baseStart_2466500 baseEnd_2466500 := by
    simpa [prefixWord, tailWord_2466500, baseEnd_2466500] using wordTrace_append hprefix tailTrace_2466500
  have hstable : (prefixWord ++ tailWord_2466500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466500).length < 2 ^ (prefixWord ++ tailWord_2466500).sum := by decide
  have hdescent : baseEnd_2466500 < baseStart_2466500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466520 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 2, 2, 3]
def baseStart_2466520 : Nat := 118140960795 + 2466520 * 2 ^ 59
def prefixEnd_2466520 : Nat := 4983230072969 + 3 ^ 40 * 2466520 * 2
def baseEnd_2466520 : Nat := 1266510303927794962856687

theorem tailTrace_2466520 : CollatzResearch.WordTrace tailWord_2466520 prefixEnd_2466520 1266510303927794962856687 := by
  unfold tailWord_2466520
  simp only [CollatzResearch.WordTrace]
  refine ⟨44980687512113381461918507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59974250016151175282558009 44980687512113381461918507)
  ·
    refine ⟨67471031268170072192877761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44980687512113381461918507 67471031268170072192877761)
    ·
      refine ⟨50603273451127554144658321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67471031268170072192877761 50603273451127554144658321)
      ·
        refine ⟨37952455088345665608493741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50603273451127554144658321 37952455088345665608493741)
        ·
          refine ⟨14232170658129624603185153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37952455088345665608493741 14232170658129624603185153)
          ·
            refine ⟨10674127993597218452388865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14232170658129624603185153 10674127993597218452388865)
            ·
              refine ⟨8005595995197913839291649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10674127993597218452388865 8005595995197913839291649)
              ·
                refine ⟨6004196996398435379468737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8005595995197913839291649 6004196996398435379468737)
                ·
                  refine ⟨4503147747298826534601553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6004196996398435379468737 4503147747298826534601553)
                  ·
                    refine ⟨3377360810474119900951165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4503147747298826534601553 3377360810474119900951165)
                    ·
                      refine ⟨1266510303927794962856687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3377360810474119900951165 1266510303927794962856687)
                      ·
                        rfl

theorem cell23_2466520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_2466520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466520 prefixEnd_2466520 := by exact prefixLift 2466520
  have htrace : WordTrace (prefixWord ++ tailWord_2466520) baseStart_2466520 baseEnd_2466520 := by
    simpa [prefixWord, tailWord_2466520, baseEnd_2466520] using wordTrace_append hprefix tailTrace_2466520
  have hstable : (prefixWord ++ tailWord_2466520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466520).length < 2 ^ (prefixWord ++ tailWord_2466520).sum := by decide
  have hdescent : baseEnd_2466520 < baseStart_2466520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466527 : List Nat := [1, 1, 2, 3, 2, 4, 1, 4, 1, 4]
def baseStart_2466527 : Nat := 118140960795 + 2466527 * 2 ^ 59
def prefixEnd_2466527 : Nat := 4983230072969 + 3 ^ 40 * 2466527 * 2
def baseEnd_2466527 : Nat := 422171299430792145156385

theorem tailTrace_2466527 : CollatzResearch.WordTrace tailWord_2466527 prefixEnd_2466527 422171299430792145156385 := by
  unfold tailWord_2466527
  simp only [CollatzResearch.WordTrace]
  refine ⟨89961630335201403119341835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59974420223467602079561223 89961630335201403119341835)
  ·
    refine ⟨134942445502802104679012753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89961630335201403119341835 134942445502802104679012753)
    ·
      refine ⟨101206834127101578509259565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134942445502802104679012753 101206834127101578509259565)
      ·
        refine ⟨37952562797663091940972337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101206834127101578509259565 37952562797663091940972337)
        ·
          refine ⟨28464422098247318955729253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37952562797663091940972337 28464422098247318955729253)
          ·
            refine ⟨5337079143421372304199235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28464422098247318955729253 5337079143421372304199235)
            ·
              refine ⟨8005618715132058456298853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5337079143421372304199235 8005618715132058456298853)
              ·
                refine ⟨1501053509087260960556035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8005618715132058456298853 1501053509087260960556035)
                ·
                  refine ⟨2251580263630891440834053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501053509087260960556035 2251580263630891440834053)
                  ·
                    refine ⟨422171299430792145156385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2251580263630891440834053 422171299430792145156385)
                    ·
                      rfl

theorem cell23_2466527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 1, 4].length) (baseStart_2466527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466527 prefixEnd_2466527 := by exact prefixLift 2466527
  have htrace : WordTrace (prefixWord ++ tailWord_2466527) baseStart_2466527 baseEnd_2466527 := by
    simpa [prefixWord, tailWord_2466527, baseEnd_2466527] using wordTrace_append hprefix tailTrace_2466527
  have hstable : (prefixWord ++ tailWord_2466527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466527).length < 2 ^ (prefixWord ++ tailWord_2466527).sum := by decide
  have hdescent : baseEnd_2466527 < baseStart_2466527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466570 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 1, 5]
def baseStart_2466570 : Nat := 118140960795 + 2466570 * 2 ^ 59
def prefixEnd_2466570 : Nat := 4983230072969 + 3 ^ 40 * 2466570 * 2
def baseEnd_2466570 : Nat := 422178659320173255743819

theorem tailTrace_2466570 : CollatzResearch.WordTrace tailWord_2466570 prefixEnd_2466570 422178659320173255743819 := by
  unfold tailWord_2466570
  simp only [CollatzResearch.WordTrace]
  refine ⟨22490799668511405365789291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59975465782697080975438109 22490799668511405365789291)
  ·
    refine ⟨33736199502767108048683937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22490799668511405365789291 33736199502767108048683937)
    ·
      refine ⟨25302149627075331036512953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33736199502767108048683937 25302149627075331036512953)
      ·
        refine ⟨18976612220306498277384715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25302149627075331036512953 18976612220306498277384715)
        ·
          refine ⟨28464918330459747416077073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18976612220306498277384715 28464918330459747416077073)
          ·
            refine ⟨21348688747844810562057805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28464918330459747416077073 21348688747844810562057805)
            ·
              refine ⟨8005758280441803960771677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21348688747844810562057805 8005758280441803960771677)
              ·
                refine ⟨3002159355165676485289379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8005758280441803960771677 3002159355165676485289379)
                ·
                  refine ⟨4503239032748514727934069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3002159355165676485289379 4503239032748514727934069)
                  ·
                    refine ⟨422178659320173255743819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4503239032748514727934069 422178659320173255743819)
                    ·
                      rfl

theorem cell23_2466570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_2466570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466570 prefixEnd_2466570 := by exact prefixLift 2466570
  have htrace : WordTrace (prefixWord ++ tailWord_2466570) baseStart_2466570 baseEnd_2466570 := by
    simpa [prefixWord, tailWord_2466570, baseEnd_2466570] using wordTrace_append hprefix tailTrace_2466570
  have hstable : (prefixWord ++ tailWord_2466570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466570).length < 2 ^ (prefixWord ++ tailWord_2466570).sum := by decide
  have hdescent : baseEnd_2466570 < baseStart_2466570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466618 : List Nat := [3, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3]
def baseStart_2466618 : Nat := 118140960795 + 2466618 * 2 ^ 59
def prefixEnd_2466618 : Nat := 4983230072969 + 3 ^ 40 * 2466618 * 2
def baseEnd_2466618 : Nat := 1266560625031935579431237

theorem tailTrace_2466618 : CollatzResearch.WordTrace tailWord_2466618 prefixEnd_2466618 1266560625031935579431237 := by
  unfold tailWord_2466618
  simp only [CollatzResearch.WordTrace]
  refine ⟨22491237344467931415226127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59976632918581150440603005 22491237344467931415226127)
  ·
    refine ⟨33736856016701897122839191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22491237344467931415226127 33736856016701897122839191)
    ·
      refine ⟨50605284025052845684258787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33736856016701897122839191 50605284025052845684258787)
      ·
        refine ⟨75907926037579268526388181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50605284025052845684258787 75907926037579268526388181)
        ·
          refine ⟨1779092016505764106087223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 75907926037579268526388181 1779092016505764106087223)
          ·
            refine ⟨2668638024758646159130835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779092016505764106087223 2668638024758646159130835)
            ·
              refine ⟨4002957037137969238696253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668638024758646159130835 4002957037137969238696253)
              ·
                refine ⟨1501108888926738464511095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4002957037137969238696253 1501108888926738464511095)
                ·
                  refine ⟨2251663333390107696766643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501108888926738464511095 2251663333390107696766643)
                  ·
                    refine ⟨3377495000085161545149965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2251663333390107696766643 3377495000085161545149965)
                    ·
                      refine ⟨1266560625031935579431237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3377495000085161545149965 1266560625031935579431237)
                      ·
                        rfl

theorem cell23_2466618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3].length) (baseStart_2466618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466618 prefixEnd_2466618 := by exact prefixLift 2466618
  have htrace : WordTrace (prefixWord ++ tailWord_2466618) baseStart_2466618 baseEnd_2466618 := by
    simpa [prefixWord, tailWord_2466618, baseEnd_2466618] using wordTrace_append hprefix tailTrace_2466618
  have hstable : (prefixWord ++ tailWord_2466618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466618).length < 2 ^ (prefixWord ++ tailWord_2466618).sum := by decide
  have hdescent : baseEnd_2466618 < baseStart_2466618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466641 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 3, 2, 2]
def baseStart_2466641 : Nat := 118140960795 + 2466641 * 2 ^ 59
def prefixEnd_2466641 : Nat := 4983230072969 + 3 ^ 40 * 2466641 * 2
def baseEnd_2466641 : Nat := 1266572435086988989443631

theorem tailTrace_2466641 : CollatzResearch.WordTrace tailWord_2466641 prefixEnd_2466641 1266572435086988989443631 := by
  unfold tailWord_2466641
  simp only [CollatzResearch.WordTrace]
  refine ⟨89965788256788400588991777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59977192171192267059327851 89965788256788400588991777)
  ·
    refine ⟨67474341192591300441743833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89965788256788400588991777 67474341192591300441743833)
    ·
      refine ⟨50605755894443475331307875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67474341192591300441743833 50605755894443475331307875)
      ·
        refine ⟨75908633841665212996961813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50605755894443475331307875 75908633841665212996961813)
        ·
          refine ⟨3558217211328056859232585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75908633841665212996961813 3558217211328056859232585)
          ·
            refine ⟨2668662908496042644424439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3558217211328056859232585 2668662908496042644424439)
            ·
              refine ⟨4002994362744063966636659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668662908496042644424439 4002994362744063966636659)
              ·
                refine ⟨6004491544116095949954989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002994362744063966636659 6004491544116095949954989)
                ·
                  refine ⟨2251684329043535981233121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6004491544116095949954989 2251684329043535981233121)
                  ·
                    refine ⟨1688763246782651985924841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2251684329043535981233121 1688763246782651985924841)
                    ·
                      refine ⟨1266572435086988989443631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688763246782651985924841 1266572435086988989443631)
                      ·
                        rfl

theorem cell23_2466641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 2, 2].length) (baseStart_2466641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466641 prefixEnd_2466641 := by exact prefixLift 2466641
  have htrace : WordTrace (prefixWord ++ tailWord_2466641) baseStart_2466641 baseEnd_2466641 := by
    simpa [prefixWord, tailWord_2466641, baseEnd_2466641] using wordTrace_append hprefix tailTrace_2466641
  have hstable : (prefixWord ++ tailWord_2466641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466641).length < 2 ^ (prefixWord ++ tailWord_2466641).sum := by decide
  have hdescent : baseEnd_2466641 < baseStart_2466641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466700 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 2, 4, 3]
def baseStart_2466700 : Nat := 118140960795 + 2466700 * 2 ^ 59
def prefixEnd_2466700 : Nat := 4983230072969 + 3 ^ 40 * 2466700 * 2
def baseEnd_2466700 : Nat := 1266602730445604258605859

theorem tailTrace_2466700 : CollatzResearch.WordTrace tailWord_2466700 prefixEnd_2466700 1266602730445604258605859 := by
  unfold tailWord_2466700
  simp only [CollatzResearch.WordTrace]
  refine ⟨44983970081787326832694777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59978626775716435776926369 44983970081787326832694777)
  ·
    refine ⟨33737977561340495124521083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44983970081787326832694777 33737977561340495124521083)
    ·
      refine ⟨50606966342010742686781625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33737977561340495124521083 50606966342010742686781625)
      ·
        refine ⟨37955224756508057015086219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50606966342010742686781625 37955224756508057015086219)
        ·
          refine ⟨56932837134762085522629329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37955224756508057015086219 56932837134762085522629329)
          ·
            refine ⟨42699627851071564141971997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56932837134762085522629329 42699627851071564141971997)
            ·
              refine ⟨16012360444151836553239499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42699627851071564141971997 16012360444151836553239499)
              ·
                refine ⟨24018540666227754829859249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16012360444151836553239499 24018540666227754829859249)
                ·
                  refine ⟨18013905499670816122394437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24018540666227754829859249 18013905499670816122394437)
                  ·
                    refine ⟨3377607281188278022948957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18013905499670816122394437 3377607281188278022948957)
                    ·
                      refine ⟨1266602730445604258605859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3377607281188278022948957 1266602730445604258605859)
                      ·
                        rfl

theorem cell23_2466700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_2466700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466700 prefixEnd_2466700 := by exact prefixLift 2466700
  have htrace : WordTrace (prefixWord ++ tailWord_2466700) baseStart_2466700 baseEnd_2466700 := by
    simpa [prefixWord, tailWord_2466700, baseEnd_2466700] using wordTrace_append hprefix tailTrace_2466700
  have hstable : (prefixWord ++ tailWord_2466700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466700).length < 2 ^ (prefixWord ++ tailWord_2466700).sum := by decide
  have hdescent : baseEnd_2466700 < baseStart_2466700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466742 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2466742 : Nat := 118140960795 + 2466742 * 2 ^ 59
def prefixEnd_2466742 : Nat := 4983230072969 + 3 ^ 40 * 2466742 * 2
def baseEnd_2466742 : Nat := 1266624296633093094280667

theorem tailTrace_2466742 : CollatzResearch.WordTrace tailWord_2466742 prefixEnd_2466742 1266624296633093094280667 := by
  unfold tailWord_2466742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5623092001838905927401155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59979648019614996558945653 5623092001838905927401155)
  ·
    refine ⟨8434638002758358891101733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5623092001838905927401155 8434638002758358891101733)
    ·
      refine ⟨1581494625517192292081575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8434638002758358891101733 1581494625517192292081575)
      ·
        refine ⟨2372241938275788438122363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1581494625517192292081575 2372241938275788438122363)
        ·
          refine ⟨3558362907413682657183545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372241938275788438122363 3558362907413682657183545)
          ·
            refine ⟨2668772180560261992887659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3558362907413682657183545 2668772180560261992887659)
            ·
              refine ⟨4003158270840392989331489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668772180560261992887659 4003158270840392989331489)
              ·
                refine ⟨3002368703130294741998617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003158270840392989331489 3002368703130294741998617)
                ·
                  refine ⟨2251776527347721056498963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3002368703130294741998617 2251776527347721056498963)
                  ·
                    refine ⟨3377664791021581584748445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2251776527347721056498963 3377664791021581584748445)
                    ·
                      refine ⟨1266624296633093094280667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3377664791021581584748445 1266624296633093094280667)
                      ·
                        rfl

theorem cell23_2466742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2466742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466742 prefixEnd_2466742 := by exact prefixLift 2466742
  have htrace : WordTrace (prefixWord ++ tailWord_2466742) baseStart_2466742 baseEnd_2466742 := by
    simpa [prefixWord, tailWord_2466742, baseEnd_2466742] using wordTrace_append hprefix tailTrace_2466742
  have hstable : (prefixWord ++ tailWord_2466742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466742).length < 2 ^ (prefixWord ++ tailWord_2466742).sum := by decide
  have hdescent : baseEnd_2466742 < baseStart_2466742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466787 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 4]
def baseStart_2466787 : Nat := 118140960795 + 2466787 * 2 ^ 59
def prefixEnd_2466787 : Nat := 4983230072969 + 3 ^ 40 * 2466787 * 2
def baseEnd_2466787 : Nat := 1266647403262545418217959

theorem tailTrace_2466787 : CollatzResearch.WordTrace tailWord_2466787 prefixEnd_2466787 1266647403262545418217959 := by
  unfold tailWord_2466787
  simp only [CollatzResearch.WordTrace]
  refine ⟨89971113314259467523806615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59980742209506311682537743 89971113314259467523806615)
  ·
    refine ⟨134956669971389201285709923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89971113314259467523806615 134956669971389201285709923)
    ·
      refine ⟨202435004957083801928564885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134956669971389201285709923 202435004957083801928564885)
      ·
        refine ⟨9489140857363303215401479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 202435004957083801928564885 9489140857363303215401479)
        ·
          refine ⟨14233711286044954823102219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9489140857363303215401479 14233711286044954823102219)
          ·
            refine ⟨21350566929067432234653329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14233711286044954823102219 21350566929067432234653329)
            ·
              refine ⟨16012925196800574175989997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21350566929067432234653329 16012925196800574175989997)
              ·
                refine ⟨6004846948800215315996249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16012925196800574175989997 6004846948800215315996249)
                ·
                  refine ⟨4503635211600161486997187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6004846948800215315996249 4503635211600161486997187)
                  ·
                    refine ⟨6755452817400242230495781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4503635211600161486997187 6755452817400242230495781)
                    ·
                      refine ⟨1266647403262545418217959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6755452817400242230495781 1266647403262545418217959)
                      ·
                        rfl

theorem cell23_2466787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_2466787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466787 prefixEnd_2466787 := by exact prefixLift 2466787
  have htrace : WordTrace (prefixWord ++ tailWord_2466787) baseStart_2466787 baseEnd_2466787 := by
    simpa [prefixWord, tailWord_2466787, baseEnd_2466787] using wordTrace_append hprefix tailTrace_2466787
  have hstable : (prefixWord ++ tailWord_2466787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466787).length < 2 ^ (prefixWord ++ tailWord_2466787).sum := by decide
  have hdescent : baseEnd_2466787 < baseStart_2466787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466827 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 6]
def baseStart_2466827 : Nat := 118140960795 + 2466827 * 2 ^ 59
def prefixEnd_2466827 : Nat := 4983230072969 + 3 ^ 40 * 2466827 * 2
def baseEnd_2466827 : Nat := 140740882498747251301975

theorem tailTrace_2466827 : CollatzResearch.WordTrace tailWord_2466827 prefixEnd_2466827 140740882498747251301975 := by
  unfold tailWord_2466827
  simp only [CollatzResearch.WordTrace]
  refine ⟨89972572234114554355262735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59981714822743036236841823 89972572234114554355262735)
  ·
    refine ⟨134958858351171831532894103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89972572234114554355262735 134958858351171831532894103)
    ·
      refine ⟨202438287526757747299341155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134958858351171831532894103 202438287526757747299341155)
      ·
        refine ⟨303657431290136620949011733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202438287526757747299341155 303657431290136620949011733)
        ·
          refine ⟨14233942091725154106984925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 303657431290136620949011733 14233942091725154106984925)
          ·
            refine ⟨5337728284396932790119347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14233942091725154106984925 5337728284396932790119347)
            ·
              refine ⟨8006592426595399185179021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5337728284396932790119347 8006592426595399185179021)
              ·
                refine ⟨3002472159973274694442133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8006592426595399185179021 3002472159973274694442133)
                ·
                  refine ⟨140740882498747251301975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3002472159973274694442133 140740882498747251301975)
                  ·
                    rfl

theorem cell23_2466827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 6].length) (baseStart_2466827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466827 prefixEnd_2466827 := by exact prefixLift 2466827
  have htrace : WordTrace (prefixWord ++ tailWord_2466827) baseStart_2466827 baseEnd_2466827 := by
    simpa [prefixWord, tailWord_2466827, baseEnd_2466827] using wordTrace_append hprefix tailTrace_2466827
  have hstable : (prefixWord ++ tailWord_2466827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466827).length < 2 ^ (prefixWord ++ tailWord_2466827).sum := by decide
  have hdescent : baseEnd_2466827 < baseStart_2466827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466864 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 2, 3, 2]
def baseStart_2466864 : Nat := 118140960795 + 2466864 * 2 ^ 59
def prefixEnd_2466864 : Nat := 4983230072969 + 3 ^ 40 * 2466864 * 2
def baseEnd_2466864 : Nat := 1266686941272941616955105

theorem tailTrace_2466864 : CollatzResearch.WordTrace tailWord_2466864 prefixEnd_2466864 1266686941272941616955105 := by
  unfold tailWord_2466864
  simp only [CollatzResearch.WordTrace]
  refine ⟨44986960867490254837179823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59982614489987006449573097 44986960867490254837179823)
  ·
    refine ⟨67480441301235382255769735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44986960867490254837179823 67480441301235382255769735)
    ·
      refine ⟨101220661951853073383654603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67480441301235382255769735 101220661951853073383654603)
      ·
        refine ⟨151830992927779610075481905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101220661951853073383654603 151830992927779610075481905)
        ·
          refine ⟨113873244695834707556611429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151830992927779610075481905 113873244695834707556611429)
          ·
            refine ⟨21351233380469007666864643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113873244695834707556611429 21351233380469007666864643)
            ·
              refine ⟨32026850070703511500296965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21351233380469007666864643 32026850070703511500296965)
              ·
                refine ⟨6005034388256908406305681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32026850070703511500296965 6005034388256908406305681)
                ·
                  refine ⟨4503775791192681304729261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6005034388256908406305681 4503775791192681304729261)
                  ·
                    refine ⟨1688915921697255489273473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4503775791192681304729261 1688915921697255489273473)
                    ·
                      refine ⟨1266686941272941616955105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688915921697255489273473 1266686941272941616955105)
                      ·
                        rfl

theorem cell23_2466864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 3, 2].length) (baseStart_2466864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466864 prefixEnd_2466864 := by exact prefixLift 2466864
  have htrace : WordTrace (prefixWord ++ tailWord_2466864) baseStart_2466864 baseEnd_2466864 := by
    simpa [prefixWord, tailWord_2466864, baseEnd_2466864] using wordTrace_append hprefix tailTrace_2466864
  have hstable : (prefixWord ++ tailWord_2466864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466864).length < 2 ^ (prefixWord ++ tailWord_2466864).sum := by decide
  have hdescent : baseEnd_2466864 < baseStart_2466864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466887 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 1, 6]
def baseStart_2466887 : Nat := 118140960795 + 2466887 * 2 ^ 59
def prefixEnd_2466887 : Nat := 4983230072969 + 3 ^ 40 * 2466887 * 2
def baseEnd_2466887 : Nat := 422232917109331675655833

theorem tailTrace_2466887 : CollatzResearch.WordTrace tailWord_2466887 prefixEnd_2466887 422232917109331675655833 := by
  unfold tailWord_2466887
  simp only [CollatzResearch.WordTrace]
  refine ⟨89974760613897184602446915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59983173742598123068297943 89974760613897184602446915)
  ·
    refine ⟨134962140920845776903670373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89974760613897184602446915 134962140920845776903670373)
    ·
      refine ⟨25305401422658583169438195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134962140920845776903670373 25305401422658583169438195)
      ·
        refine ⟨37958102133987874754157293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25305401422658583169438195 37958102133987874754157293)
        ·
          refine ⟨14234288300245453032808985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37958102133987874754157293 14234288300245453032808985)
          ·
            refine ⟨10675716225184089774606739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14234288300245453032808985 10675716225184089774606739)
            ·
              refine ⟨16013574337776134661910109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10675716225184089774606739 16013574337776134661910109)
              ·
                refine ⟨6005090376666050498216291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16013574337776134661910109 6005090376666050498216291)
                ·
                  refine ⟨9007635564999075747324437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6005090376666050498216291 9007635564999075747324437)
                  ·
                    refine ⟨422232917109331675655833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9007635564999075747324437 422232917109331675655833)
                    ·
                      rfl

theorem cell23_2466887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_2466887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466887 prefixEnd_2466887 := by exact prefixLift 2466887
  have htrace : WordTrace (prefixWord ++ tailWord_2466887) baseStart_2466887 baseEnd_2466887 := by
    simpa [prefixWord, tailWord_2466887, baseEnd_2466887] using wordTrace_append hprefix tailTrace_2466887
  have hstable : (prefixWord ++ tailWord_2466887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466887).length < 2 ^ (prefixWord ++ tailWord_2466887).sum := by decide
  have hdescent : baseEnd_2466887 < baseStart_2466887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466894 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_2466894 : Nat := 118140960795 + 2466894 * 2 ^ 59
def prefixEnd_2466894 : Nat := 4983230072969 + 3 ^ 40 * 2466894 * 2
def baseEnd_2466894 : Nat := 1266702345692576499579967

theorem tailTrace_2466894 : CollatzResearch.WordTrace tailWord_2466894 prefixEnd_2466894 1266702345692576499579967 := by
  unfold tailWord_2466894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11246876990608978099743967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59983343949914549865301157 11246876990608978099743967)
  ·
    refine ⟨16870315485913467149615951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11246876990608978099743967 16870315485913467149615951)
    ·
      refine ⟨25305473228870200724423927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16870315485913467149615951 25305473228870200724423927)
      ·
        refine ⟨37958209843305301086635891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25305473228870200724423927 37958209843305301086635891)
        ·
          refine ⟨56937314764957951629953837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37958209843305301086635891 56937314764957951629953837)
          ·
            refine ⟨21351493036859231861232689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56937314764957951629953837 21351493036859231861232689)
            ·
              refine ⟨16013619777644423895924517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21351493036859231861232689 16013619777644423895924517)
              ·
                refine ⟨3002553708308329480485847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16013619777644423895924517 3002553708308329480485847)
                ·
                  refine ⟨4503830562462494220728771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3002553708308329480485847 4503830562462494220728771)
                  ·
                    refine ⟨6755745843693741331093157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4503830562462494220728771 6755745843693741331093157)
                    ·
                      refine ⟨1266702345692576499579967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6755745843693741331093157 1266702345692576499579967)
                      ·
                        rfl

theorem cell23_2466894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_2466894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466894 prefixEnd_2466894 := by exact prefixLift 2466894
  have htrace : WordTrace (prefixWord ++ tailWord_2466894) baseStart_2466894 baseEnd_2466894 := by
    simpa [prefixWord, tailWord_2466894, baseEnd_2466894] using wordTrace_append hprefix tailTrace_2466894
  have hstable : (prefixWord ++ tailWord_2466894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466894).length < 2 ^ (prefixWord ++ tailWord_2466894).sum := by decide
  have hdescent : baseEnd_2466894 < baseStart_2466894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466898 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_2466898 : Nat := 118140960795 + 2466898 * 2 ^ 59
def prefixEnd_2466898 : Nat := 4983230072969 + 3 ^ 40 * 2466898 * 2
def baseEnd_2466898 : Nat := 1266704399615194483929949

theorem tailTrace_2466898 : CollatzResearch.WordTrace tailWord_2466898 prefixEnd_2466898 1266704399615194483929949 := by
  unfold tailWord_2466898
  simp only [CollatzResearch.WordTrace]
  refine ⟨22493790454214333370274337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59983441211238222320731565 22493790454214333370274337)
  ·
    refine ⟨16870342840660750027705753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22493790454214333370274337 16870342840660750027705753)
    ·
      refine ⟨12652757130495562520779315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16870342840660750027705753 12652757130495562520779315)
      ·
        refine ⟨18979135695743343781168973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12652757130495562520779315 18979135695743343781168973)
        ·
          refine ⟨7117175885903753917938365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18979135695743343781168973 7117175885903753917938365)
          ·
            refine ⟨2668940957213907719226887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7117175885903753917938365 2668940957213907719226887)
            ·
              refine ⟨4003411435820861578840331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668940957213907719226887 4003411435820861578840331)
              ·
                refine ⟨6005117153731292368260497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4003411435820861578840331 6005117153731292368260497)
                ·
                  refine ⟨4503837865298469276195373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6005117153731292368260497 4503837865298469276195373)
                  ·
                    refine ⟨1688939199486925978573265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4503837865298469276195373 1688939199486925978573265)
                    ·
                      refine ⟨1266704399615194483929949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688939199486925978573265 1266704399615194483929949)
                      ·
                        rfl

theorem cell23_2466898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_2466898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466898 prefixEnd_2466898 := by exact prefixLift 2466898
  have htrace : WordTrace (prefixWord ++ tailWord_2466898) baseStart_2466898 baseEnd_2466898 := by
    simpa [prefixWord, tailWord_2466898, baseEnd_2466898] using wordTrace_append hprefix tailTrace_2466898
  have hstable : (prefixWord ++ tailWord_2466898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466898).length < 2 ^ (prefixWord ++ tailWord_2466898).sum := by decide
  have hdescent : baseEnd_2466898 < baseStart_2466898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466921 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 2, 4]
def baseStart_2466921 : Nat := 118140960795 + 2466921 * 2 ^ 59
def prefixEnd_2466921 : Nat := 4983230072969 + 3 ^ 40 * 2466921 * 2
def baseEnd_2466921 : Nat := 422238736556749297980781

theorem tailTrace_2466921 : CollatzResearch.WordTrace tailWord_2466921 prefixEnd_2466921 422238736556749297980781 := by
  unfold tailWord_2466921
  simp only [CollatzResearch.WordTrace]
  refine ⟨89976000695774008409184617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59984000463849338939456411 89976000695774008409184617)
  ·
    refine ⟨67482000521830506306888463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89976000695774008409184617 67482000521830506306888463)
    ·
      refine ⟨101223000782745759460332695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67482000521830506306888463 101223000782745759460332695)
      ·
        refine ⟨151834501174118639190499043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101223000782745759460332695 151834501174118639190499043)
        ·
          refine ⟨227751751761177958785748565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151834501174118639190499043 227751751761177958785748565)
          ·
            refine ⟨2668965840951304204520491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 227751751761177958785748565 2668965840951304204520491)
            ·
              refine ⟨4003448761426956306780737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668965840951304204520491 4003448761426956306780737)
              ·
                refine ⟨3002586571070217230085553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003448761426956306780737 3002586571070217230085553)
                ·
                  refine ⟨2251939928302662922564165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3002586571070217230085553 2251939928302662922564165)
                  ·
                    refine ⟨422238736556749297980781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2251939928302662922564165 422238736556749297980781)
                    ·
                      rfl

theorem cell23_2466921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 4].length) (baseStart_2466921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466921 prefixEnd_2466921 := by exact prefixLift 2466921
  have htrace : WordTrace (prefixWord ++ tailWord_2466921) baseStart_2466921 baseEnd_2466921 := by
    simpa [prefixWord, tailWord_2466921, baseEnd_2466921] using wordTrace_append hprefix tailTrace_2466921
  have hstable : (prefixWord ++ tailWord_2466921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466921).length < 2 ^ (prefixWord ++ tailWord_2466921).sum := by decide
  have hdescent : baseEnd_2466921 < baseStart_2466921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466928 : List Nat := [2, 1, 1, 1, 5, 1, 1, 6, 1, 2, 2]
def baseStart_2466928 : Nat := 118140960795 + 2466928 * 2 ^ 59
def prefixEnd_2466928 : Nat := 4983230072969 + 3 ^ 40 * 2466928 * 2
def baseEnd_2466928 : Nat := 1266719804034829366554811

theorem tailTrace_2466928 : CollatzResearch.WordTrace tailWord_2466928 prefixEnd_2466928 1266719804034829366554811 := by
  unfold tailWord_2466928
  simp only [CollatzResearch.WordTrace]
  refine ⟨44988128003374324302344719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59984170671165765736459625 44988128003374324302344719)
  ·
    refine ⟨67482192005061486453517079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44988128003374324302344719 67482192005061486453517079)
    ·
      refine ⟨101223288007592229680275619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67482192005061486453517079 101223288007592229680275619)
      ·
        refine ⟨151834932011388344520413429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101223288007592229680275619 151834932011388344520413429)
        ·
          refine ⟨14234524876067657298788759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151834932011388344520413429 14234524876067657298788759)
          ·
            refine ⟨21351787314101485948183139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14234524876067657298788759 21351787314101485948183139)
            ·
              refine ⟨32027680971152228922274709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21351787314101485948183139 32027680971152228922274709)
              ·
                refine ⟨1501297545522760730731627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32027680971152228922274709 1501297545522760730731627)
                ·
                  refine ⟨2251946318284141096097441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501297545522760730731627 2251946318284141096097441)
                  ·
                    refine ⟨1688959738713105822073081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2251946318284141096097441 1688959738713105822073081)
                    ·
                      refine ⟨1266719804034829366554811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688959738713105822073081 1266719804034829366554811)
                      ·
                        rfl

theorem cell23_2466928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 1, 2, 2].length) (baseStart_2466928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466928 prefixEnd_2466928 := by exact prefixLift 2466928
  have htrace : WordTrace (prefixWord ++ tailWord_2466928) baseStart_2466928 baseEnd_2466928 := by
    simpa [prefixWord, tailWord_2466928, baseEnd_2466928] using wordTrace_append hprefix tailTrace_2466928
  have hstable : (prefixWord ++ tailWord_2466928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466928).length < 2 ^ (prefixWord ++ tailWord_2466928).sum := by decide
  have hdescent : baseEnd_2466928 < baseStart_2466928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466944 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 3]
def baseStart_2466944 : Nat := 118140960795 + 2466944 * 2 ^ 59
def prefixEnd_2466944 : Nat := 4983230072969 + 3 ^ 40 * 2466944 * 2
def baseEnd_2466944 : Nat := 1266728019725301303954737

theorem tailTrace_2466944 : CollatzResearch.WordTrace tailWord_2466944 prefixEnd_2466944 1266728019725301303954737 := by
  unfold tailWord_2466944
  simp only [CollatzResearch.WordTrace]
  refine ⟨44988419787345341668635943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59984559716460455558181257 44988419787345341668635943)
  ·
    refine ⟨67482629681018012502953915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44988419787345341668635943 67482629681018012502953915)
    ·
      refine ⟨101223944521527018754430873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67482629681018012502953915 101223944521527018754430873)
      ·
        refine ⟨75917958391145264065823155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101223944521527018754430873 75917958391145264065823155)
        ·
          refine ⟨113876937586717896098734733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75917958391145264065823155 113876937586717896098734733)
          ·
            refine ⟨42703851595019211037025525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113876937586717896098734733 42703851595019211037025525)
            ·
              refine ⟨4003486087033051034721143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42703851595019211037025525 4003486087033051034721143)
              ·
                refine ⟨6005229130549576552081715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4003486087033051034721143 6005229130549576552081715)
                ·
                  refine ⟨9007843695824364828122573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6005229130549576552081715 9007843695824364828122573)
                  ·
                    refine ⟨3377941385934136810545965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9007843695824364828122573 3377941385934136810545965)
                    ·
                      refine ⟨1266728019725301303954737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3377941385934136810545965 1266728019725301303954737)
                      ·
                        rfl

theorem cell23_2466944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_2466944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466944 prefixEnd_2466944 := by exact prefixLift 2466944
  have htrace : WordTrace (prefixWord ++ tailWord_2466944) baseStart_2466944 baseEnd_2466944 := by
    simpa [prefixWord, tailWord_2466944, baseEnd_2466944] using wordTrace_append hprefix tailTrace_2466944
  have hstable : (prefixWord ++ tailWord_2466944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466944).length < 2 ^ (prefixWord ++ tailWord_2466944).sum := by decide
  have hdescent : baseEnd_2466944 < baseStart_2466944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466962 : List Nat := [3, 2, 3, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_2466962 : Nat := 118140960795 + 2466962 * 2 ^ 59
def prefixEnd_2466962 : Nat := 4983230072969 + 3 ^ 40 * 2466962 * 2
def baseEnd_2466962 : Nat := 1266737262377082233529655

theorem tailTrace_2466962 : CollatzResearch.WordTrace tailWord_2466962 prefixEnd_2466962 1266737262377082233529655 := by
  unfold tailWord_2466962
  simp only [CollatzResearch.WordTrace]
  refine ⟨22494374022156368102856785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59984997392416981607618093 22494374022156368102856785)
  ·
    refine ⟨16870780516617276077142589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22494374022156368102856785 16870780516617276077142589)
    ·
      refine ⟨6326542693731478528928471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16870780516617276077142589 6326542693731478528928471)
      ·
        refine ⟨9489814040597217793392707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6326542693731478528928471 9489814040597217793392707)
        ·
          refine ⟨14234721060895826690089061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9489814040597217793392707 14234721060895826690089061)
          ·
            refine ⟨2669010198917967504391699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14234721060895826690089061 2669010198917967504391699)
            ·
              refine ⟨4003515298376951256587549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2669010198917967504391699 4003515298376951256587549)
              ·
                refine ⟨1501318236891356721220331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4003515298376951256587549 1501318236891356721220331)
                ·
                  refine ⟨2251977355337035081830497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501318236891356721220331 2251977355337035081830497)
                  ·
                    refine ⟨1688983016502776311372873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2251977355337035081830497 1688983016502776311372873)
                    ·
                      refine ⟨1266737262377082233529655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1688983016502776311372873 1266737262377082233529655)
                      ·
                        rfl

theorem cell23_2466962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_2466962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2466962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2466962 prefixEnd_2466962 := by exact prefixLift 2466962
  have htrace : WordTrace (prefixWord ++ tailWord_2466962) baseStart_2466962 baseEnd_2466962 := by
    simpa [prefixWord, tailWord_2466962, baseEnd_2466962] using wordTrace_append hprefix tailTrace_2466962
  have hstable : (prefixWord ++ tailWord_2466962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466962).length < 2 ^ (prefixWord ++ tailWord_2466962).sum := by decide
  have hdescent : baseEnd_2466962 < baseStart_2466962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467004 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2467004 : Nat := 118140960795 + 2467004 * 2 ^ 59
def prefixEnd_2467004 : Nat := 4983230072969 + 3 ^ 40 * 2467004 * 2
def baseEnd_2467004 : Nat := 1266758828564571069204461

theorem tailTrace_2467004 : CollatzResearch.WordTrace tailWord_2467004 prefixEnd_2467004 1266758828564571069204461 := by
  unfold tailWord_2467004
  simp only [CollatzResearch.WordTrace]
  refine ⟨44989513977236656792228033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59986018636315542389637377 44989513977236656792228033)
  ·
    refine ⟨33742135482927492594171025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44989513977236656792228033 33742135482927492594171025)
    ·
      refine ⟨25306601612195619445628269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33742135482927492594171025 25306601612195619445628269)
      ·
        refine ⟨9489975604573357292110601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25306601612195619445628269 9489975604573357292110601)
        ·
          refine ⟨7117481703430017969082951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9489975604573357292110601 7117481703430017969082951)
          ·
            refine ⟨10676222555145026953624427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7117481703430017969082951 10676222555145026953624427)
            ·
              refine ⟨16014333832717540430436641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10676222555145026953624427 16014333832717540430436641)
              ·
                refine ⟨12010750374538155322827481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16014333832717540430436641 12010750374538155322827481)
                ·
                  refine ⟨9008062780903616492120611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12010750374538155322827481 9008062780903616492120611)
                  ·
                    refine ⟨13512094171355424738180917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9008062780903616492120611 13512094171355424738180917)
                    ·
                      refine ⟨1266758828564571069204461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13512094171355424738180917 1266758828564571069204461)
                      ·
                        rfl

theorem cell23_2467004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2467004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467004 prefixEnd_2467004 := by exact prefixLift 2467004
  have htrace : WordTrace (prefixWord ++ tailWord_2467004) baseStart_2467004 baseEnd_2467004 := by
    simpa [prefixWord, tailWord_2467004, baseEnd_2467004] using wordTrace_append hprefix tailTrace_2467004
  have hstable : (prefixWord ++ tailWord_2467004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467004).length < 2 ^ (prefixWord ++ tailWord_2467004).sum := by decide
  have hdescent : baseEnd_2467004 < baseStart_2467004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467007 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 7]
def baseStart_2467007 : Nat := 118140960795 + 2467007 * 2 ^ 59
def prefixEnd_2467007 : Nat := 4983230072969 + 3 ^ 40 * 2467007 * 2
def baseEnd_2467007 : Nat := 140751152111837173051883

theorem tailTrace_2467007 : CollatzResearch.WordTrace tailWord_2467007 prefixEnd_2467007 140751152111837173051883 := by
  unfold tailWord_2467007
  simp only [CollatzResearch.WordTrace]
  refine ⟨89979137373462445096815275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59986091582308296731210183 89979137373462445096815275)
  ·
    refine ⟨134968706060193667645222913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89979137373462445096815275 134968706060193667645222913)
    ·
      refine ⟨101226529545145250733917185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134968706060193667645222913 101226529545145250733917185)
      ·
        refine ⟨75919897158858938050437889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101226529545145250733917185 75919897158858938050437889)
        ·
          refine ⟨56939922869144203537828417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75919897158858938050437889 56939922869144203537828417)
          ·
            refine ⟨42704942151858152653371313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56939922869144203537828417 42704942151858152653371313)
            ·
              refine ⟨32028706613893614490028485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42704942151858152653371313 32028706613893614490028485)
              ·
                refine ⟨6005382490105052716880341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32028706613893614490028485 6005382490105052716880341)
                ·
                  refine ⟨140751152111837173051883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6005382490105052716880341 140751152111837173051883)
                  ·
                    rfl

theorem cell23_2467007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 7].length) (baseStart_2467007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467007 prefixEnd_2467007 := by exact prefixLift 2467007
  have htrace : WordTrace (prefixWord ++ tailWord_2467007) baseStart_2467007 baseEnd_2467007 := by
    simpa [prefixWord, tailWord_2467007, baseEnd_2467007] using wordTrace_append hprefix tailTrace_2467007
  have hstable : (prefixWord ++ tailWord_2467007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467007).length < 2 ^ (prefixWord ++ tailWord_2467007).sum := by decide
  have hdescent : baseEnd_2467007 < baseStart_2467007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467034 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3]
def baseStart_2467034 : Nat := 118140960795 + 2467034 * 2 ^ 59
def prefixEnd_2467034 : Nat := 4983230072969 + 3 ^ 40 * 2467034 * 2
def baseEnd_2467034 : Nat := 1266774232984205951829323

theorem tailTrace_2467034 : CollatzResearch.WordTrace tailWord_2467034 prefixEnd_2467034 1266774232984205951829323 := by
  unfold tailWord_2467034
  simp only [CollatzResearch.WordTrace]
  refine ⟨22495030536091157177012039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59986748096243085805365437 22495030536091157177012039)
  ·
    refine ⟨33742545804136735765518059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22495030536091157177012039 33742545804136735765518059)
    ·
      refine ⟨50613818706205103648277089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33742545804136735765518059 50613818706205103648277089)
      ·
        refine ⟨37960364029653827736207817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50613818706205103648277089 37960364029653827736207817)
        ·
          refine ⟨28470273022240370802155863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37960364029653827736207817 28470273022240370802155863)
          ·
            refine ⟨42705409533360556203233795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28470273022240370802155863 42705409533360556203233795)
            ·
              refine ⟨64058114300040834304850693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42705409533360556203233795 64058114300040834304850693)
              ·
                refine ⟨12010896431257656432159505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64058114300040834304850693 12010896431257656432159505)
                ·
                  refine ⟨9008172323443242324119629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12010896431257656432159505 9008172323443242324119629)
                  ·
                    refine ⟨3378064621291215871544861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9008172323443242324119629 3378064621291215871544861)
                    ·
                      refine ⟨1266774232984205951829323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3378064621291215871544861 1266774232984205951829323)
                      ·
                        rfl

theorem cell23_2467034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_2467034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467034 prefixEnd_2467034 := by exact prefixLift 2467034
  have htrace : WordTrace (prefixWord ++ tailWord_2467034) baseStart_2467034 baseEnd_2467034 := by
    simpa [prefixWord, tailWord_2467034, baseEnd_2467034] using wordTrace_append hprefix tailTrace_2467034
  have hstable : (prefixWord ++ tailWord_2467034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467034).length < 2 ^ (prefixWord ++ tailWord_2467034).sum := by decide
  have hdescent : baseEnd_2467034 < baseStart_2467034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467041 : List Nat := [1, 2, 3, 1, 3, 3, 1, 4, 5]
def baseStart_2467041 : Nat := 118140960795 + 2467041 * 2 ^ 59
def prefixEnd_2467041 : Nat := 4983230072969 + 3 ^ 40 * 2467041 * 2
def baseEnd_2467041 : Nat := 140753091927643047160199

theorem tailTrace_2467041 : CollatzResearch.WordTrace tailWord_2467041 prefixEnd_2467041 140753091927643047160199 := by
  unfold tailWord_2467041
  simp only [CollatzResearch.WordTrace]
  refine ⟨89980377455339268903552977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59986918303559512602368651 89980377455339268903552977)
  ·
    refine ⟨67485283091504451677664733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89980377455339268903552977 67485283091504451677664733)
    ·
      refine ⟨25306981159314169379124275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67485283091504451677664733 25306981159314169379124275)
      ·
        refine ⟨37960471738971254068686413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25306981159314169379124275 37960471738971254068686413)
        ·
          refine ⟨14235176902114220275757405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37960471738971254068686413 14235176902114220275757405)
          ·
            refine ⟨5338191338292832603409027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14235176902114220275757405 5338191338292832603409027)
            ·
              refine ⟨8007287007439248905113541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5338191338292832603409027 8007287007439248905113541)
              ·
                refine ⟨1501366313894859169708789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8007287007439248905113541 1501366313894859169708789)
                ·
                  refine ⟨140753091927643047160199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1501366313894859169708789 140753091927643047160199)
                  ·
                    rfl

theorem cell23_2467041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 5].length) (baseStart_2467041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467041 prefixEnd_2467041 := by exact prefixLift 2467041
  have htrace : WordTrace (prefixWord ++ tailWord_2467041) baseStart_2467041 baseEnd_2467041 := by
    simpa [prefixWord, tailWord_2467041, baseEnd_2467041] using wordTrace_append hprefix tailTrace_2467041
  have hstable : (prefixWord ++ tailWord_2467041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467041).length < 2 ^ (prefixWord ++ tailWord_2467041).sum := by decide
  have hdescent : baseEnd_2467041 < baseStart_2467041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467054 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_2467054 : Nat := 118140960795 + 2467054 * 2 ^ 59
def prefixEnd_2467054 : Nat := 4983230072969 + 3 ^ 40 * 2467054 * 2
def baseEnd_2467054 : Nat := 422261500865765291193077

theorem tailTrace_2467054 : CollatzResearch.WordTrace tailWord_2467054 prefixEnd_2467054 422261500865765291193077 := by
  unfold tailWord_2467054
  simp only [CollatzResearch.WordTrace]
  refine ⟨11247606450536521515472027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59987234402861448082517477 11247606450536521515472027)
  ·
    refine ⟨16871409675804782273208041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11247606450536521515472027 16871409675804782273208041)
    ·
      refine ⟨12653557256853586704906031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16871409675804782273208041 12653557256853586704906031)
      ·
        refine ⟨18980335885280380057359047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12653557256853586704906031 18980335885280380057359047)
        ·
          refine ⟨28470503827920570086038571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18980335885280380057359047 28470503827920570086038571)
          ·
            refine ⟨42705755741880855129057857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28470503827920570086038571 42705755741880855129057857)
            ·
              refine ⟨32029316806410641346793393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42705755741880855129057857 32029316806410641346793393)
              ·
                refine ⟨24021987604807981010095045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32029316806410641346793393 24021987604807981010095045)
                ·
                  refine ⟨4504122675901496439392821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24021987604807981010095045 4504122675901496439392821)
                  ·
                    refine ⟨422261500865765291193077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4504122675901496439392821 422261500865765291193077)
                    ·
                      rfl

theorem cell23_2467054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_2467054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467054 prefixEnd_2467054 := by exact prefixLift 2467054
  have htrace : WordTrace (prefixWord ++ tailWord_2467054) baseStart_2467054 baseEnd_2467054 := by
    simpa [prefixWord, tailWord_2467054, baseEnd_2467054] using wordTrace_append hprefix tailTrace_2467054
  have hstable : (prefixWord ++ tailWord_2467054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467054).length < 2 ^ (prefixWord ++ tailWord_2467054).sum := by decide
  have hdescent : baseEnd_2467054 < baseStart_2467054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467071 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 2, 5]
def baseStart_2467071 : Nat := 118140960795 + 2467071 * 2 ^ 59
def prefixEnd_2467071 : Nat := 4983230072969 + 3 ^ 40 * 2467071 * 2
def baseEnd_2467071 : Nat := 422264410589474102355551

theorem tailTrace_2467071 : CollatzResearch.WordTrace tailWord_2467071 prefixEnd_2467071 422264410589474102355551 := by
  unfold tailWord_2467071
  simp only [CollatzResearch.WordTrace]
  refine ⟨89981471645230584027145067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59987647763487056018096711 89981471645230584027145067)
  ·
    refine ⟨134972207467845876040717601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89981471645230584027145067 134972207467845876040717601)
    ·
      refine ⟨101229155600884407030538201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134972207467845876040717601 101229155600884407030538201)
      ·
        refine ⟨75921866700663305272903651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101229155600884407030538201 75921866700663305272903651)
        ·
          refine ⟨113882800050994957909355477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75921866700663305272903651 113882800050994957909355477)
          ·
            refine ⟨2669128126195194326000519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 113882800050994957909355477 2669128126195194326000519)
            ·
              refine ⟨4003692189292791489000779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2669128126195194326000519 4003692189292791489000779)
              ·
                refine ⟨6005538283939187233501169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4003692189292791489000779 6005538283939187233501169)
                ·
                  refine ⟨4504153712954390425125877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6005538283939187233501169 4504153712954390425125877)
                  ·
                    refine ⟨422264410589474102355551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4504153712954390425125877 422264410589474102355551)
                    ·
                      rfl

theorem cell23_2467071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 5].length) (baseStart_2467071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467071 prefixEnd_2467071 := by exact prefixLift 2467071
  have htrace : WordTrace (prefixWord ++ tailWord_2467071) baseStart_2467071 baseEnd_2467071 := by
    simpa [prefixWord, tailWord_2467071, baseEnd_2467071] using wordTrace_append hprefix tailTrace_2467071
  have hstable : (prefixWord ++ tailWord_2467071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467071).length < 2 ^ (prefixWord ++ tailWord_2467071).sum := by decide
  have hdescent : baseEnd_2467071 < baseStart_2467071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467135 : List Nat := [1, 1, 2, 2, 4, 4, 1, 3, 1, 4]
def baseStart_2467135 : Nat := 118140960795 + 2467135 * 2 ^ 59
def prefixEnd_2467135 : Nat := 4983230072969 + 3 ^ 40 * 2467135 * 2
def baseEnd_2467135 : Nat := 422275364843436685555453

theorem tailTrace_2467135 : CollatzResearch.WordTrace tailWord_2467135 prefixEnd_2467135 422275364843436685555453 := by
  unfold tailWord_2467135
  simp only [CollatzResearch.WordTrace]
  refine ⟨89983805916998722957474859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59989203944665815304983239 89983805916998722957474859)
  ·
    refine ⟨134975708875498084436212289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89983805916998722957474859 134975708875498084436212289)
    ·
      refine ⟨101231781656623563327159217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134975708875498084436212289 101231781656623563327159217)
      ·
        refine ⟨75923836242467672495369413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101231781656623563327159217 75923836242467672495369413)
        ·
          refine ⟨14235719295462688592881765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75923836242467672495369413 14235719295462688592881765)
          ·
            refine ⟨2669197367899254111165331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14235719295462688592881765 2669197367899254111165331)
            ·
              refine ⟨4003796051848881166747997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2669197367899254111165331 4003796051848881166747997)
              ·
                refine ⟨1501423519443330437530499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4003796051848881166747997 1501423519443330437530499)
                ·
                  refine ⟨2252135279164995656295749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501423519443330437530499 2252135279164995656295749)
                  ·
                    refine ⟨422275364843436685555453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2252135279164995656295749 422275364843436685555453)
                    ·
                      rfl

theorem cell23_2467135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 1, 4].length) (baseStart_2467135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467135 prefixEnd_2467135 := by exact prefixLift 2467135
  have htrace : WordTrace (prefixWord ++ tailWord_2467135) baseStart_2467135 baseEnd_2467135 := by
    simpa [prefixWord, tailWord_2467135, baseEnd_2467135] using wordTrace_append hprefix tailTrace_2467135
  have hstable : (prefixWord ++ tailWord_2467135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467135).length < 2 ^ (prefixWord ++ tailWord_2467135).sum := by decide
  have hdescent : baseEnd_2467135 < baseStart_2467135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467141 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 5, 1, 3]
def baseStart_2467141 : Nat := 118140960795 + 2467141 * 2 ^ 59
def prefixEnd_2467141 : Nat := 4983230072969 + 3 ^ 40 * 2467141 * 2
def baseEnd_2467141 : Nat := 1266829175414237033191331

theorem tailTrace_2467141 : CollatzResearch.WordTrace tailWord_2467141 prefixEnd_2467141 1266829175414237033191331 := by
  unfold tailWord_2467141
  simp only [CollatzResearch.WordTrace]
  refine ⟨89984024754976985982193277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59989349836651323988128851 89984024754976985982193277)
  ·
    refine ⟨33744009283116369743322479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89984024754976985982193277 33744009283116369743322479)
    ·
      refine ⟨50616013924674554614983719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33744009283116369743322479 50616013924674554614983719)
      ·
        refine ⟨75924020887011831922475579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50616013924674554614983719 75924020887011831922475579)
        ·
          refine ⟨113886031330517747883713369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75924020887011831922475579 113886031330517747883713369)
          ·
            refine ⟨85414523497888310912785027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113886031330517747883713369 85414523497888310912785027)
            ·
              refine ⟨128121785246832466369177541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85414523497888310912785027 128121785246832466369177541)
              ·
                refine ⟨24022834733781087444220789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128121785246832466369177541 24022834733781087444220789)
                ·
                  refine ⟨2252140756291976947895699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24022834733781087444220789 2252140756291976947895699)
                  ·
                    refine ⟨3378211134437965421843549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2252140756291976947895699 3378211134437965421843549)
                    ·
                      refine ⟨1266829175414237033191331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3378211134437965421843549 1266829175414237033191331)
                      ·
                        rfl

theorem cell23_2467141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_2467141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467141 prefixEnd_2467141 := by exact prefixLift 2467141
  have htrace : WordTrace (prefixWord ++ tailWord_2467141) baseStart_2467141 baseEnd_2467141 := by
    simpa [prefixWord, tailWord_2467141, baseEnd_2467141] using wordTrace_append hprefix tailTrace_2467141
  have hstable : (prefixWord ++ tailWord_2467141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467141).length < 2 ^ (prefixWord ++ tailWord_2467141).sum := by decide
  have hdescent : baseEnd_2467141 < baseStart_2467141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467142 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2467142 : Nat := 118140960795 + 2467142 * 2 ^ 59
def prefixEnd_2467142 : Nat := 4983230072969 + 3 ^ 40 * 2467142 * 2
def baseEnd_2467142 : Nat := 1266829688894891529278827

theorem tailTrace_2467142 : CollatzResearch.WordTrace tailWord_2467142 prefixEnd_2467142 1266829688894891529278827 := by
  unfold tailWord_2467142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2812001913374167598530615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59989374151982242101986453 2812001913374167598530615)
  ·
    refine ⟨4218002870061251397795923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2812001913374167598530615 4218002870061251397795923)
    ·
      refine ⟨6327004305091877096693885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4218002870061251397795923 6327004305091877096693885)
      ·
        refine ⟨2372626614409453911260207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6327004305091877096693885 2372626614409453911260207)
        ·
          refine ⟨3558939921614180866890311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372626614409453911260207 3558939921614180866890311)
          ·
            refine ⟨5338409882421271300335467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3558939921614180866890311 5338409882421271300335467)
            ·
              refine ⟨8007614823631906950503201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5338409882421271300335467 8007614823631906950503201)
              ·
                refine ⟨6005711117723930212877401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8007614823631906950503201 6005711117723930212877401)
                ·
                  refine ⟨4504283338292947659658051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6005711117723930212877401 4504283338292947659658051)
                  ·
                    refine ⟨6756425007439421489487077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4504283338292947659658051 6756425007439421489487077)
                    ·
                      refine ⟨1266829688894891529278827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6756425007439421489487077 1266829688894891529278827)
                      ·
                        rfl

theorem cell23_2467142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2467142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467142 prefixEnd_2467142 := by exact prefixLift 2467142
  have htrace : WordTrace (prefixWord ++ tailWord_2467142) baseStart_2467142 baseEnd_2467142 := by
    simpa [prefixWord, tailWord_2467142, baseEnd_2467142] using wordTrace_append hprefix tailTrace_2467142
  have hstable : (prefixWord ++ tailWord_2467142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467142).length < 2 ^ (prefixWord ++ tailWord_2467142).sum := by decide
  have hdescent : baseEnd_2467142 < baseStart_2467142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467144 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 5, 5]
def baseStart_2467144 : Nat := 118140960795 + 2467144 * 2 ^ 59
def prefixEnd_2467144 : Nat := 4983230072969 + 3 ^ 40 * 2467144 * 2
def baseEnd_2467144 : Nat := 422276905285400173817939

theorem tailTrace_2467144 : CollatzResearch.WordTrace tailWord_2467144 prefixEnd_2467144 422276905285400173817939 := by
  unfold tailWord_2467144
  simp only [CollatzResearch.WordTrace]
  refine ⟨44992067086983058747276243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59989422782644078329701657 44992067086983058747276243)
  ·
    refine ⟨67488100630474588120914365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44992067086983058747276243 67488100630474588120914365)
    ·
      refine ⟨25308037736427970545342887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67488100630474588120914365 25308037736427970545342887)
      ·
        refine ⟨37962056604641955818014331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25308037736427970545342887 37962056604641955818014331)
        ·
          refine ⟨56943084906962933727021497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37962056604641955818014331 56943084906962933727021497)
          ·
            refine ⟨42707313680222200295266123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56943084906962933727021497 42707313680222200295266123)
            ·
              refine ⟨64060970520333300442899185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42707313680222200295266123 64060970520333300442899185)
              ·
                refine ⟨48045727890249975332174389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64060970520333300442899185 48045727890249975332174389)
                ·
                  refine ⟨4504286989710935187391349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48045727890249975332174389 4504286989710935187391349)
                  ·
                    refine ⟨422276905285400173817939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4504286989710935187391349 422276905285400173817939)
                    ·
                      rfl

theorem cell23_2467144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_2467144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467144 prefixEnd_2467144 := by exact prefixLift 2467144
  have htrace : WordTrace (prefixWord ++ tailWord_2467144) baseStart_2467144 baseEnd_2467144 := by
    simpa [prefixWord, tailWord_2467144, baseEnd_2467144] using wordTrace_append hprefix tailTrace_2467144
  have hstable : (prefixWord ++ tailWord_2467144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467144).length < 2 ^ (prefixWord ++ tailWord_2467144).sum := by decide
  have hdescent : baseEnd_2467144 < baseStart_2467144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467154 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2467154 : Nat := 118140960795 + 2467154 * 2 ^ 59
def prefixEnd_2467154 : Nat := 4983230072969 + 3 ^ 40 * 2467154 * 2
def baseEnd_2467154 : Nat := 1266835850662745482328771

theorem tailTrace_2467154 : CollatzResearch.WordTrace tailWord_2467154 prefixEnd_2467154 1266835850662745482328771 := by
  unfold tailWord_2467154
  simp only [CollatzResearch.WordTrace]
  refine ⟨22496124725982472300604129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59989665935953259468277677 22496124725982472300604129)
  ·
    refine ⟨16872093544486854225453097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22496124725982472300604129 16872093544486854225453097)
    ·
      refine ⟨12654070158365140669089823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16872093544486854225453097 12654070158365140669089823)
      ·
        refine ⟨18981105237547711003634735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12654070158365140669089823 18981105237547711003634735)
        ·
          refine ⟨28471657856321566505452103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18981105237547711003634735 28471657856321566505452103)
          ·
            refine ⟨42707486784482349758178155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28471657856321566505452103 42707486784482349758178155)
            ·
              refine ⟨64061230176723524637267233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42707486784482349758178155 64061230176723524637267233)
              ·
                refine ⟨48045922632542643477950425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64061230176723524637267233 48045922632542643477950425)
                ·
                  refine ⟨36034441974406982608462819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48045922632542643477950425 36034441974406982608462819)
                  ·
                    refine ⟨54051662961610473912694229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36034441974406982608462819 54051662961610473912694229)
                    ·
                      refine ⟨1266835850662745482328771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54051662961610473912694229 1266835850662745482328771)
                      ·
                        rfl

theorem cell23_2467154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2467154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467154 prefixEnd_2467154 := by exact prefixLift 2467154
  have htrace : WordTrace (prefixWord ++ tailWord_2467154) baseStart_2467154 baseEnd_2467154 := by
    simpa [prefixWord, tailWord_2467154, baseEnd_2467154] using wordTrace_append hprefix tailTrace_2467154
  have hstable : (prefixWord ++ tailWord_2467154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467154).length < 2 ^ (prefixWord ++ tailWord_2467154).sum := by decide
  have hdescent : baseEnd_2467154 < baseStart_2467154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467178 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 3, 5]
def baseStart_2467178 : Nat := 118140960795 + 2467178 * 2 ^ 59
def prefixEnd_2467178 : Nat := 4983230072969 + 3 ^ 40 * 2467178 * 2
def baseEnd_2467178 : Nat := 422282724732817796142887

theorem tailTrace_2467178 : CollatzResearch.WordTrace tailWord_2467178 prefixEnd_2467178 422282724732817796142887 := by
  unfold tailWord_2467178
  simp only [CollatzResearch.WordTrace]
  refine ⟨22496343563960735325322547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59990249503895294200860125 22496343563960735325322547)
  ·
    refine ⟨33744515345941102987983821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22496343563960735325322547 33744515345941102987983821)
    ·
      refine ⟨12654193254727913620493933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33744515345941102987983821 12654193254727913620493933)
      ·
        refine ⟨4745322470522967607685225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12654193254727913620493933 4745322470522967607685225)
        ·
          refine ⟨3558991852892225705763919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4745322470522967607685225 3558991852892225705763919)
          ·
            refine ⟨5338487779338338558645879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3558991852892225705763919 5338487779338338558645879)
            ·
              refine ⟨8007731669007507837968819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5338487779338338558645879 8007731669007507837968819)
              ·
                refine ⟨12011597503511261756953229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8007731669007507837968819 12011597503511261756953229)
                ·
                  refine ⟨4504349063816723158857461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12011597503511261756953229 4504349063816723158857461)
                  ·
                    refine ⟨422282724732817796142887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4504349063816723158857461 422282724732817796142887)
                    ·
                      rfl

theorem cell23_2467178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_2467178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467178 prefixEnd_2467178 := by exact prefixLift 2467178
  have htrace : WordTrace (prefixWord ++ tailWord_2467178) baseStart_2467178 baseEnd_2467178 := by
    simpa [prefixWord, tailWord_2467178, baseEnd_2467178] using wordTrace_append hprefix tailTrace_2467178
  have hstable : (prefixWord ++ tailWord_2467178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467178).length < 2 ^ (prefixWord ++ tailWord_2467178).sum := by decide
  have hdescent : baseEnd_2467178 < baseStart_2467178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467202 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_2467202 : Nat := 118140960795 + 2467202 * 2 ^ 59
def prefixEnd_2467202 : Nat := 4983230072969 + 3 ^ 40 * 2467202 * 2
def baseEnd_2467202 : Nat := 1266860497734161294528551

theorem tailTrace_2467202 : CollatzResearch.WordTrace tailWord_2467202 prefixEnd_2467202 1266860497734161294528551 := by
  unfold tailWord_2467202
  simp only [CollatzResearch.WordTrace]
  refine ⟨22496562401938998350040965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59990833071837328933442573 22496562401938998350040965)
  ·
    refine ⟨4218105450363562190632681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22496562401938998350040965 4218105450363562190632681)
    ·
      refine ⟨3163579087772671642974511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4218105450363562190632681 3163579087772671642974511)
      ·
        refine ⟨4745368631659007464461767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3163579087772671642974511 4745368631659007464461767)
        ·
          refine ⟨7118052947488511196692651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4745368631659007464461767 7118052947488511196692651)
          ·
            refine ⟨10677079421232766795038977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7118052947488511196692651 10677079421232766795038977)
            ·
              refine ⟨8007809565924575096279233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10677079421232766795038977 8007809565924575096279233)
              ·
                refine ⟨6005857174443431322209425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8007809565924575096279233 6005857174443431322209425)
                ·
                  refine ⟨4504392880832573491657069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6005857174443431322209425 4504392880832573491657069)
                  ·
                    refine ⟨1689147330312215059371401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4504392880832573491657069 1689147330312215059371401)
                    ·
                      refine ⟨1266860497734161294528551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1689147330312215059371401 1266860497734161294528551)
                      ·
                        rfl

theorem cell23_2467202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_2467202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467202 prefixEnd_2467202 := by exact prefixLift 2467202
  have htrace : WordTrace (prefixWord ++ tailWord_2467202) baseStart_2467202 baseEnd_2467202 := by
    simpa [prefixWord, tailWord_2467202, baseEnd_2467202] using wordTrace_append hprefix tailTrace_2467202
  have hstable : (prefixWord ++ tailWord_2467202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467202).length < 2 ^ (prefixWord ++ tailWord_2467202).sum := by decide
  have hdescent : baseEnd_2467202 < baseStart_2467202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467204 : List Nat := [2, 3, 2, 1, 1, 14]
def baseStart_2467204 : Nat := 118140960795 + 2467204 * 2 ^ 59
def prefixEnd_2467204 : Nat := 4983230072969 + 3 ^ 40 * 2467204 * 2
def baseEnd_2467204 : Nat := 5213421912327038216887

theorem tailTrace_2467204 : CollatzResearch.WordTrace tailWord_2467204 prefixEnd_2467204 5213421912327038216887 := by
  unfold tailWord_2467204
  simp only [CollatzResearch.WordTrace]
  refine ⟨44993161276874373870868333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59990881702499165161157777 44993161276874373870868333)
  ·
    refine ⟨16872435478827890201575625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44993161276874373870868333 16872435478827890201575625)
    ·
      refine ⟨12654326609120917651181719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16872435478827890201575625 12654326609120917651181719)
      ·
        refine ⟨18981489913681376476772579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12654326609120917651181719 18981489913681376476772579)
        ·
          refine ⟨28472234870522064715158869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18981489913681376476772579 28472234870522064715158869)
          ·
            refine ⟨5213421912327038216887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 28472234870522064715158869 5213421912327038216887)
            ·
              rfl

theorem cell23_2467204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 14].length) (baseStart_2467204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467204 prefixEnd_2467204 := by exact prefixLift 2467204
  have htrace : WordTrace (prefixWord ++ tailWord_2467204) baseStart_2467204 baseEnd_2467204 := by
    simpa [prefixWord, tailWord_2467204, baseEnd_2467204] using wordTrace_append hprefix tailTrace_2467204
  have hstable : (prefixWord ++ tailWord_2467204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467204).length < 2 ^ (prefixWord ++ tailWord_2467204).sum := by decide
  have hdescent : baseEnd_2467204 < baseStart_2467204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467208 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 2, 4]
def baseStart_2467208 : Nat := 118140960795 + 2467208 * 2 ^ 59
def prefixEnd_2467208 : Nat := 4983230072969 + 3 ^ 40 * 2467208 * 2
def baseEnd_2467208 : Nat := 422287859539362757017841

theorem tailTrace_2467208 : CollatzResearch.WordTrace tailWord_2467208 prefixEnd_2467208 422287859539362757017841 := by
  unfold tailWord_2467208
  simp only [CollatzResearch.WordTrace]
  refine ⟨44993234222867128212441139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59990978963822837616588185 44993234222867128212441139)
  ·
    refine ⟨67489851334300692318661709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44993234222867128212441139 67489851334300692318661709)
    ·
      refine ⟨25308694250362759619498141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67489851334300692318661709 25308694250362759619498141)
      ·
        refine ⟨9490760343886034857311803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25308694250362759619498141 9490760343886034857311803)
        ·
          refine ⟨14236140515829052285967705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9490760343886034857311803 14236140515829052285967705)
          ·
            refine ⟨10677105386871789214475779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14236140515829052285967705 10677105386871789214475779)
            ·
              refine ⟨16015658080307683821713669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10677105386871789214475779 16015658080307683821713669)
              ·
                refine ⟨3002935890057690716571313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16015658080307683821713669 3002935890057690716571313)
                ·
                  refine ⟨2252201917543268037428485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3002935890057690716571313 2252201917543268037428485)
                  ·
                    refine ⟨422287859539362757017841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2252201917543268037428485 422287859539362757017841)
                    ·
                      rfl

theorem cell23_2467208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_2467208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467208 prefixEnd_2467208 := by exact prefixLift 2467208
  have htrace : WordTrace (prefixWord ++ tailWord_2467208) baseStart_2467208 baseEnd_2467208 := by
    simpa [prefixWord, tailWord_2467208, baseEnd_2467208] using wordTrace_append hprefix tailTrace_2467208
  have hstable : (prefixWord ++ tailWord_2467208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467208).length < 2 ^ (prefixWord ++ tailWord_2467208).sum := by decide
  have hdescent : baseEnd_2467208 < baseStart_2467208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467209 : List Nat := [1, 2, 1, 1, 7, 2, 2, 2, 1, 1, 3]
def baseStart_2467209 : Nat := 118140960795 + 2467209 * 2 ^ 59
def prefixEnd_2467209 : Nat := 4983230072969 + 3 ^ 40 * 2467209 * 2
def baseEnd_2467209 : Nat := 1266864092098742767141019

theorem tailTrace_2467209 : CollatzResearch.WordTrace tailWord_2467209 prefixEnd_2467209 1266864092098742767141019 := by
  unfold tailWord_2467209
  simp only [CollatzResearch.WordTrace]
  refine ⟨89986504918730633595668681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59991003279153755730445787 89986504918730633595668681)
  ·
    refine ⟨67489878689047975196751511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89986504918730633595668681 67489878689047975196751511)
    ·
      refine ⟨101234818033571962795127267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67489878689047975196751511 101234818033571962795127267)
      ·
        refine ⟨151852227050357944192690901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101234818033571962795127267 151852227050357944192690901)
        ·
          refine ⟨3559036571492764317016193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 151852227050357944192690901 3559036571492764317016193)
          ·
            refine ⟨2669277428619573237762145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3559036571492764317016193 2669277428619573237762145)
            ·
              refine ⟨2001958071464679928321609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2669277428619573237762145 2001958071464679928321609)
              ·
                refine ⟨1501468553598509946241207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001958071464679928321609 1501468553598509946241207)
                ·
                  refine ⟨2252202830397764919361811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501468553598509946241207 2252202830397764919361811)
                  ·
                    refine ⟨3378304245596647379042717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2252202830397764919361811 3378304245596647379042717)
                    ·
                      refine ⟨1266864092098742767141019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3378304245596647379042717 1266864092098742767141019)
                      ·
                        rfl

theorem cell23_2467209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 1, 1, 3].length) (baseStart_2467209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467209 prefixEnd_2467209 := by exact prefixLift 2467209
  have htrace : WordTrace (prefixWord ++ tailWord_2467209) baseStart_2467209 baseEnd_2467209 := by
    simpa [prefixWord, tailWord_2467209, baseEnd_2467209] using wordTrace_append hprefix tailTrace_2467209
  have hstable : (prefixWord ++ tailWord_2467209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467209).length < 2 ^ (prefixWord ++ tailWord_2467209).sum := by decide
  have hdescent : baseEnd_2467209 < baseStart_2467209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467415 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 3]
def baseStart_2467415 : Nat := 118140960795 + 2467415 * 2 ^ 59
def prefixEnd_2467415 : Nat := 4983230072969 + 3 ^ 40 * 2467415 * 2
def baseEnd_2467415 : Nat := 1266969869113568961165071

theorem tailTrace_2467415 : CollatzResearch.WordTrace tailWord_2467415 prefixEnd_2467415 1266969869113568961165071 := by
  unfold tailWord_2467415
  simp only [CollatzResearch.WordTrace]
  refine ⟨89994018355984330777667699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59996012237322887185111799 89994018355984330777667699)
  ·
    refine ⟨134991027533976496166501549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89994018355984330777667699 134991027533976496166501549)
    ·
      refine ⟨50621635325241186062438081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134991027533976496166501549 50621635325241186062438081)
      ·
        refine ⟨37966226493930889546828561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50621635325241186062438081 37966226493930889546828561)
        ·
          refine ⟨28474669870448167160121421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37966226493930889546828561 28474669870448167160121421)
          ·
            refine ⟨10678001201418062685045533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28474669870448167160121421 10678001201418062685045533)
            ·
              refine ⟨4004250450531773506892075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10678001201418062685045533 4004250450531773506892075)
              ·
                refine ⟨6006375675797660260338113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4004250450531773506892075 6006375675797660260338113)
                ·
                  refine ⟨4504781756848245195253585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6006375675797660260338113 4504781756848245195253585)
                  ·
                    refine ⟨3378586317636183896440189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4504781756848245195253585 3378586317636183896440189)
                    ·
                      refine ⟨1266969869113568961165071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3378586317636183896440189 1266969869113568961165071)
                      ·
                        rfl

theorem cell23_2467415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_2467415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467415 prefixEnd_2467415 := by exact prefixLift 2467415
  have htrace : WordTrace (prefixWord ++ tailWord_2467415) baseStart_2467415 baseEnd_2467415 := by
    simpa [prefixWord, tailWord_2467415, baseEnd_2467415] using wordTrace_append hprefix tailTrace_2467415
  have hstable : (prefixWord ++ tailWord_2467415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467415).length < 2 ^ (prefixWord ++ tailWord_2467415).sum := by decide
  have hdescent : baseEnd_2467415 < baseStart_2467415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467479 : List Nat := [1, 1, 3, 3, 2, 2, 3, 3, 1, 1, 3]
def baseStart_2467479 : Nat := 118140960795 + 2467479 * 2 ^ 59
def prefixEnd_2467479 : Nat := 4983230072969 + 3 ^ 40 * 2467479 * 2
def baseEnd_2467479 : Nat := 1267002731875456710764777

theorem tailTrace_2467479 : CollatzResearch.WordTrace tailWord_2467479 prefixEnd_2467479 1267002731875456710764777 := by
  unfold tailWord_2467479
  simp only [CollatzResearch.WordTrace]
  refine ⟨89996352627752469707997491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59997568418501646471998327 89996352627752469707997491)
  ·
    refine ⟨134994528941628704561996237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89996352627752469707997491 134994528941628704561996237)
    ·
      refine ⟨50622948353110764210748589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134994528941628704561996237 50622948353110764210748589)
      ·
        refine ⟨18983605632416536579030721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50622948353110764210748589 18983605632416536579030721)
        ·
          refine ⟨14237704224312402434273041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18983605632416536579030721 14237704224312402434273041)
          ·
            refine ⟨10678278168234301825704781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14237704224312402434273041 10678278168234301825704781)
            ·
              refine ⟨4004354313087863184639293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10678278168234301825704781 4004354313087863184639293)
              ·
                refine ⟨1501632867407948694239735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4004354313087863184639293 1501632867407948694239735)
                ·
                  refine ⟨2252449301111923041359603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501632867407948694239735 2252449301111923041359603)
                  ·
                    refine ⟨3378673951667884562039405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2252449301111923041359603 3378673951667884562039405)
                    ·
                      refine ⟨1267002731875456710764777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3378673951667884562039405 1267002731875456710764777)
                      ·
                        rfl

theorem cell23_2467479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_2467479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467479 prefixEnd_2467479 := by exact prefixLift 2467479
  have htrace : WordTrace (prefixWord ++ tailWord_2467479) baseStart_2467479 baseEnd_2467479 := by
    simpa [prefixWord, tailWord_2467479, baseEnd_2467479] using wordTrace_append hprefix tailTrace_2467479
  have hstable : (prefixWord ++ tailWord_2467479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467479).length < 2 ^ (prefixWord ++ tailWord_2467479).sum := by decide
  have hdescent : baseEnd_2467479 < baseStart_2467479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467532 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2467532 : Nat := 118140960795 + 2467532 * 2 ^ 59
def prefixEnd_2467532 : Nat := 4983230072969 + 3 ^ 40 * 2467532 * 2
def baseEnd_2467532 : Nat := 1267029946350145003402033

theorem tailTrace_2467532 : CollatzResearch.WordTrace tailWord_2467532 prefixEnd_2467532 1267029946350145003402033 := by
  unfold tailWord_2467532
  simp only [CollatzResearch.WordTrace]
  refine ⟨44999142848280229879838425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59998857131040306506451233 44999142848280229879838425)
  ·
    refine ⟨33749357136210172409878819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44999142848280229879838425 33749357136210172409878819)
    ·
      refine ⟨50624035704315258614818229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33749357136210172409878819 50624035704315258614818229)
      ·
        refine ⟨4746003347279555495139209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50624035704315258614818229 4746003347279555495139209)
        ·
          refine ⟨3559502510459666621354407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4746003347279555495139209 3559502510459666621354407)
          ·
            refine ⟨5339253765689499932031611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3559502510459666621354407 5339253765689499932031611)
            ·
              refine ⟨8008880648534249898047417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5339253765689499932031611 8008880648534249898047417)
              ·
                refine ⟨6006660486400687423535563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8008880648534249898047417 6006660486400687423535563)
                ·
                  refine ⟨9009990729601031135303345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6006660486400687423535563 9009990729601031135303345)
                  ·
                    refine ⟨6757493047200773351477509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9009990729601031135303345 6757493047200773351477509)
                    ·
                      refine ⟨1267029946350145003402033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6757493047200773351477509 1267029946350145003402033)
                      ·
                        rfl

theorem cell23_2467532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2467532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467532 prefixEnd_2467532 := by exact prefixLift 2467532
  have htrace : WordTrace (prefixWord ++ tailWord_2467532) baseStart_2467532 baseEnd_2467532 := by
    simpa [prefixWord, tailWord_2467532, baseEnd_2467532] using wordTrace_append hprefix tailTrace_2467532
  have hstable : (prefixWord ++ tailWord_2467532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467532).length < 2 ^ (prefixWord ++ tailWord_2467532).sum := by decide
  have hdescent : baseEnd_2467532 < baseStart_2467532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467535 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 6, 1, 3]
def baseStart_2467535 : Nat := 118140960795 + 2467535 * 2 ^ 59
def prefixEnd_2467535 : Nat := 4983230072969 + 3 ^ 40 * 2467535 * 2
def baseEnd_2467535 : Nat := 1267031486792108491664519

theorem tailTrace_2467535 : CollatzResearch.WordTrace tailWord_2467535 prefixEnd_2467535 1267031486792108491664519 := by
  unfold tailWord_2467535
  simp only [CollatzResearch.WordTrace]
  refine ⟨89998395115549591272036059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59998930077033060848024039 89998395115549591272036059)
  ·
    refine ⟨134997592673324386908054089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89998395115549591272036059 134997592673324386908054089)
    ·
      refine ⟨101248194504993290181040567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134997592673324386908054089 101248194504993290181040567)
      ·
        refine ⟨151872291757489935271560851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101248194504993290181040567 151872291757489935271560851)
        ·
          refine ⟨227808437636234902907341277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151872291757489935271560851 227808437636234902907341277)
          ·
            refine ⟨85428164113588088590252979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227808437636234902907341277 85428164113588088590252979)
            ·
              refine ⟨128142246170382132885379469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85428164113588088590252979 128142246170382132885379469)
              ·
                refine ⟨48053342313893299832017301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128142246170382132885379469 48053342313893299832017301)
                ·
                  refine ⟨2252500420963748429625811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48053342313893299832017301 2252500420963748429625811)
                  ·
                    refine ⟨3378750631445622644438717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2252500420963748429625811 3378750631445622644438717)
                    ·
                      refine ⟨1267031486792108491664519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3378750631445622644438717 1267031486792108491664519)
                      ·
                        rfl

theorem cell23_2467535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 1, 3].length) (baseStart_2467535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467535 prefixEnd_2467535 := by exact prefixLift 2467535
  have htrace : WordTrace (prefixWord ++ tailWord_2467535) baseStart_2467535 baseEnd_2467535 := by
    simpa [prefixWord, tailWord_2467535, baseEnd_2467535] using wordTrace_append hprefix tailTrace_2467535
  have hstable : (prefixWord ++ tailWord_2467535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467535).length < 2 ^ (prefixWord ++ tailWord_2467535).sum := by decide
  have hdescent : baseEnd_2467535 < baseStart_2467535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467542 : List Nat := [5, 2, 1, 3, 1, 11]
def baseStart_2467542 : Nat := 118140960795 + 2467542 * 2 ^ 59
def prefixEnd_2467542 : Nat := 4983230072969 + 3 ^ 40 * 2467542 * 2
def baseEnd_2467542 : Nat := 5214136136447283803609

theorem tailTrace_2467542 : CollatzResearch.WordTrace tailWord_2467542 prefixEnd_2467542 5214136136447283803609 := by
  unfold tailWord_2467542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624915651657764466721305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59999100284349487645027253 5624915651657764466721305)
  ·
    refine ⟨4218686738743323350040979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5624915651657764466721305 4218686738743323350040979)
    ·
      refine ⟨6328030108114985025061469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4218686738743323350040979 6328030108114985025061469)
      ·
        refine ⟨2373011290543119384398051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6328030108114985025061469 2373011290543119384398051)
        ·
          refine ⟨3559516935814679076597077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373011290543119384398051 3559516935814679076597077)
          ·
            refine ⟨5214136136447283803609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3559516935814679076597077 5214136136447283803609)
            ·
              rfl

theorem cell23_2467542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 11].length) (baseStart_2467542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467542 prefixEnd_2467542 := by exact prefixLift 2467542
  have htrace : WordTrace (prefixWord ++ tailWord_2467542) baseStart_2467542 baseEnd_2467542 := by
    simpa [prefixWord, tailWord_2467542, baseEnd_2467542] using wordTrace_append hprefix tailTrace_2467542
  have hstable : (prefixWord ++ tailWord_2467542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467542).length < 2 ^ (prefixWord ++ tailWord_2467542).sum := by decide
  have hdescent : baseEnd_2467542 < baseStart_2467542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467552 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 2, 1, 3]
def baseStart_2467552 : Nat := 118140960795 + 2467552 * 2 ^ 59
def prefixEnd_2467552 : Nat := 4983230072969 + 3 ^ 40 * 2467552 * 2
def baseEnd_2467552 : Nat := 1267040215963234925151941

theorem tailTrace_2467552 : CollatzResearch.WordTrace tailWord_2467552 prefixEnd_2467552 1267040215963234925151941 := by
  unfold tailWord_2467552
  simp only [CollatzResearch.WordTrace]
  refine ⟨44999507578244001587702455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59999343437658668783603273 44999507578244001587702455)
  ·
    refine ⟨67499261367366002381553683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44999507578244001587702455 67499261367366002381553683)
    ·
      refine ⟨101248892051049003572330525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67499261367366002381553683 101248892051049003572330525)
      ·
        refine ⟨37968334519143376339623947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101248892051049003572330525 37968334519143376339623947)
        ·
          refine ⟨56952501778715064509435921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37968334519143376339623947 56952501778715064509435921)
          ·
            refine ⟨42714376334036298382076941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56952501778715064509435921 42714376334036298382076941)
            ·
              refine ⟨16017891125263611893278853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42714376334036298382076941 16017891125263611893278853)
              ·
                refine ⟨3003354585986927229989785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16017891125263611893278853 3003354585986927229989785)
                ·
                  refine ⟨2252515939490195422492339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3003354585986927229989785 2252515939490195422492339)
                  ·
                    refine ⟨3378773909235293133738509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2252515939490195422492339 3378773909235293133738509)
                    ·
                      refine ⟨1267040215963234925151941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3378773909235293133738509 1267040215963234925151941)
                      ·
                        rfl

theorem cell23_2467552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_2467552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467552 prefixEnd_2467552 := by exact prefixLift 2467552
  have htrace : WordTrace (prefixWord ++ tailWord_2467552) baseStart_2467552 baseEnd_2467552 := by
    simpa [prefixWord, tailWord_2467552, baseEnd_2467552] using wordTrace_append hprefix tailTrace_2467552
  have hstable : (prefixWord ++ tailWord_2467552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467552).length < 2 ^ (prefixWord ++ tailWord_2467552).sum := by decide
  have hdescent : baseEnd_2467552 < baseStart_2467552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467559 : List Nat := [1, 1, 5, 4, 2, 1, 1, 8]
def baseStart_2467559 : Nat := 118140960795 + 2467559 * 2 ^ 59
def prefixEnd_2467559 : Nat := 4983230072969 + 3 ^ 40 * 2467559 * 2
def baseEnd_2467559 : Nat := 46927548530659866583867

theorem tailTrace_2467559 : CollatzResearch.WordTrace tailWord_2467559 prefixEnd_2467559 46927548530659866583867 := by
  unfold tailWord_2467559
  simp only [CollatzResearch.WordTrace]
  refine ⟨89999270467462643370909731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59999513644975095580606487 89999270467462643370909731)
  ·
    refine ⟨134998905701193965056364597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89999270467462643370909731 134998905701193965056364597)
    ·
      refine ⟨12656147409486934224034181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134998905701193965056364597 12656147409486934224034181)
      ·
        refine ⟨2373027639278800167006409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12656147409486934224034181 2373027639278800167006409)
        ·
          refine ⟨1779770729459100125254807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2373027639278800167006409 1779770729459100125254807)
          ·
            refine ⟨2669656094188650187882211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779770729459100125254807 2669656094188650187882211)
            ·
              refine ⟨4004484141282975281823317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2669656094188650187882211 4004484141282975281823317)
              ·
                refine ⟨46927548530659866583867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4004484141282975281823317 46927548530659866583867)
                ·
                  rfl

theorem cell23_2467559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 8].length) (baseStart_2467559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467559 prefixEnd_2467559 := by exact prefixLift 2467559
  have htrace : WordTrace (prefixWord ++ tailWord_2467559) baseStart_2467559 baseEnd_2467559 := by
    simpa [prefixWord, tailWord_2467559, baseEnd_2467559] using wordTrace_append hprefix tailTrace_2467559
  have hstable : (prefixWord ++ tailWord_2467559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467559).length < 2 ^ (prefixWord ++ tailWord_2467559).sum := by decide
  have hdescent : baseEnd_2467559 < baseStart_2467559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467562 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_2467562 : Nat := 118140960795 + 2467562 * 2 ^ 59
def prefixEnd_2467562 : Nat := 4983230072969 + 3 ^ 40 * 2467562 * 2
def baseEnd_2467562 : Nat := 1267045350769779886026895

theorem tailTrace_2467562 : CollatzResearch.WordTrace tailWord_2467562 prefixEnd_2467562 1267045350769779886026895 := by
  unfold tailWord_2467562
  simp only [CollatzResearch.WordTrace]
  refine ⟨22499844971612943720817235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59999586590967849922179293 22499844971612943720817235)
  ·
    refine ⟨33749767457419415581225853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22499844971612943720817235 33749767457419415581225853)
    ·
      refine ⟨12656162796532280842959695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33749767457419415581225853 12656162796532280842959695)
      ·
        refine ⟨18984244194798421264439543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12656162796532280842959695 18984244194798421264439543)
        ·
          refine ⟨28476366292197631896659315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18984244194798421264439543 28476366292197631896659315)
          ·
            refine ⟨42714549438296447844988973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28476366292197631896659315 42714549438296447844988973)
            ·
              refine ⟨16017956039361167941870865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42714549438296447844988973 16017956039361167941870865)
              ·
                refine ⟨12013467029520875956403149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16017956039361167941870865 12013467029520875956403149)
                ·
                  refine ⟨4505050136070328483651181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12013467029520875956403149 4505050136070328483651181)
                  ·
                    refine ⟨1689393801026373181369193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4505050136070328483651181 1689393801026373181369193)
                    ·
                      refine ⟨1267045350769779886026895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1689393801026373181369193 1267045350769779886026895)
                      ·
                        rfl

theorem cell23_2467562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_2467562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467562 prefixEnd_2467562 := by exact prefixLift 2467562
  have htrace : WordTrace (prefixWord ++ tailWord_2467562) baseStart_2467562 baseEnd_2467562 := by
    simpa [prefixWord, tailWord_2467562, baseEnd_2467562] using wordTrace_append hprefix tailTrace_2467562
  have hstable : (prefixWord ++ tailWord_2467562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467562).length < 2 ^ (prefixWord ++ tailWord_2467562).sum := by decide
  have hdescent : baseEnd_2467562 < baseStart_2467562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467592 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 1, 4, 2]
def baseStart_2467592 : Nat := 118140960795 + 2467592 * 2 ^ 59
def prefixEnd_2467592 : Nat := 4983230072969 + 3 ^ 40 * 2467592 * 2
def baseEnd_2467592 : Nat := 1267060755189414768651757

theorem tailTrace_2467592 : CollatzResearch.WordTrace tailWord_2467592 prefixEnd_2467592 1267060755189414768651757 := by
  unfold tailWord_2467592
  simp only [CollatzResearch.WordTrace]
  refine ⟨45000237038171545003430515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60000316050895393337907353 45000237038171545003430515)
  ·
    refine ⟨67500355557257317505145773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45000237038171545003430515 67500355557257317505145773)
    ·
      refine ⟨25312633333971494064429665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67500355557257317505145773 25312633333971494064429665)
      ·
        refine ⟨18984475000478620548322249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25312633333971494064429665 18984475000478620548322249)
        ·
          refine ⟨14238356250358965411241687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18984475000478620548322249 14238356250358965411241687)
          ·
            refine ⟨21357534375538448116862531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14238356250358965411241687 21357534375538448116862531)
            ·
              refine ⟨32036301563307672175293797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21357534375538448116862531 32036301563307672175293797)
              ·
                refine ⟨6006806543120188532867587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32036301563307672175293797 6006806543120188532867587)
                ·
                  refine ⟨9010209814680282799301381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6006806543120188532867587 9010209814680282799301381)
                  ·
                    refine ⟨1689414340252553024869009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9010209814680282799301381 1689414340252553024869009)
                    ·
                      refine ⟨1267060755189414768651757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1689414340252553024869009 1267060755189414768651757)
                      ·
                        rfl

theorem cell23_2467592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_2467592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467592 prefixEnd_2467592 := by exact prefixLift 2467592
  have htrace : WordTrace (prefixWord ++ tailWord_2467592) baseStart_2467592 baseEnd_2467592 := by
    simpa [prefixWord, tailWord_2467592, baseEnd_2467592] using wordTrace_append hprefix tailTrace_2467592
  have hstable : (prefixWord ++ tailWord_2467592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467592).length < 2 ^ (prefixWord ++ tailWord_2467592).sum := by decide
  have hdescent : baseEnd_2467592 < baseStart_2467592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467597 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2467597 : Nat := 118140960795 + 2467597 * 2 ^ 59
def prefixEnd_2467597 : Nat := 4983230072969 + 3 ^ 40 * 2467597 * 2
def baseEnd_2467597 : Nat := 422354440864229083029745

theorem tailTrace_2467597 : CollatzResearch.WordTrace tailWord_2467597 prefixEnd_2467597 422354440864229083029745 := by
  unfold tailWord_2467597
  simp only [CollatzResearch.WordTrace]
  refine ⟨90000656441324975860793045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60000437627549983907195363 90000656441324975860793045)
  ·
    refine ⟨2109390385343554121737337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 90000656441324975860793045 2109390385343554121737337)
    ·
      refine ⟨1582042789007665591303003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2109390385343554121737337 1582042789007665591303003)
      ·
        refine ⟨2373064183511498386954505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582042789007665591303003 2373064183511498386954505)
        ·
          refine ⟨1779798137633623790215879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2373064183511498386954505 1779798137633623790215879)
          ·
            refine ⟨2669697206450435685323819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779798137633623790215879 2669697206450435685323819)
            ·
              refine ⟨4004545809675653527985729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2669697206450435685323819 4004545809675653527985729)
              ·
                refine ⟨3003409357256740145989297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4004545809675653527985729 3003409357256740145989297)
                ·
                  refine ⟨2252557017942555109491973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3003409357256740145989297 2252557017942555109491973)
                  ·
                    refine ⟨422354440864229083029745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2252557017942555109491973 422354440864229083029745)
                    ·
                      rfl

theorem cell23_2467597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2467597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467597 prefixEnd_2467597 := by exact prefixLift 2467597
  have htrace : WordTrace (prefixWord ++ tailWord_2467597) baseStart_2467597 baseEnd_2467597 := by
    simpa [prefixWord, tailWord_2467597, baseEnd_2467597] using wordTrace_append hprefix tailTrace_2467597
  have hstable : (prefixWord ++ tailWord_2467597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467597).length < 2 ^ (prefixWord ++ tailWord_2467597).sum := by decide
  have hdescent : baseEnd_2467597 < baseStart_2467597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467602 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2467602 : Nat := 118140960795 + 2467602 * 2 ^ 59
def prefixEnd_2467602 : Nat := 4983230072969 + 3 ^ 40 * 2467602 * 2
def baseEnd_2467602 : Nat := 422355296665319909842237

theorem tailTrace_2467602 : CollatzResearch.WordTrace tailWord_2467602 prefixEnd_2467602 422355296665319909842237 := by
  unfold tailWord_2467602
  simp only [CollatzResearch.WordTrace]
  refine ⟨22500209701576715428681265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60000559204204574476483373 22500209701576715428681265)
  ·
    refine ⟨16875157276182536571510949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22500209701576715428681265 16875157276182536571510949)
    ·
      refine ⟨3164091989284225607158303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16875157276182536571510949 3164091989284225607158303)
      ·
        refine ⟨4746137983926338410737455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3164091989284225607158303 4746137983926338410737455)
        ·
          refine ⟨7119206975889507616106183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4746137983926338410737455 7119206975889507616106183)
          ·
            refine ⟨10678810463834261424159275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7119206975889507616106183 10678810463834261424159275)
            ·
              refine ⟨16018215695751392136238913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10678810463834261424159275 16018215695751392136238913)
              ·
                refine ⟨12013661771813544102179185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16018215695751392136238913 12013661771813544102179185)
                ·
                  refine ⟨9010246328860158076634389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12013661771813544102179185 9010246328860158076634389)
                  ·
                    refine ⟨422355296665319909842237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9010246328860158076634389 422355296665319909842237)
                    ·
                      rfl

theorem cell23_2467602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2467602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467602 prefixEnd_2467602 := by exact prefixLift 2467602
  have htrace : WordTrace (prefixWord ++ tailWord_2467602) baseStart_2467602 baseEnd_2467602 := by
    simpa [prefixWord, tailWord_2467602, baseEnd_2467602] using wordTrace_append hprefix tailTrace_2467602
  have hstable : (prefixWord ++ tailWord_2467602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467602).length < 2 ^ (prefixWord ++ tailWord_2467602).sum := by decide
  have hdescent : baseEnd_2467602 < baseStart_2467602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467605 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_2467605 : Nat := 118140960795 + 2467605 * 2 ^ 59
def prefixEnd_2467605 : Nat := 4983230072969 + 3 ^ 40 * 2467605 * 2
def baseEnd_2467605 : Nat := 1267067430437923217789197

theorem tailTrace_2467605 : CollatzResearch.WordTrace tailWord_2467605 prefixEnd_2467605 1267067430437923217789197 := by
  unfold tailWord_2467605
  simp only [CollatzResearch.WordTrace]
  refine ⟨90000948225295993227084269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60000632150197328818056179 90000948225295993227084269)
  ·
    refine ⟨33750355584485997460156601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90000948225295993227084269 33750355584485997460156601)
    ·
      refine ⟨25312766688364498095117451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33750355584485997460156601 25312766688364498095117451)
      ·
        refine ⟨37969150032546747142676177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25312766688364498095117451 37969150032546747142676177)
        ·
          refine ⟨28476862524410060357007133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37969150032546747142676177 28476862524410060357007133)
          ·
            refine ⟨10678823446653772633877675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28476862524410060357007133 10678823446653772633877675)
            ·
              refine ⟨16018235169980658950816513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10678823446653772633877675 16018235169980658950816513)
              ·
                refine ⟨12013676377485494213112385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16018235169980658950816513 12013676377485494213112385)
                ·
                  refine ⟨9010257283114120659834289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12013676377485494213112385 9010257283114120659834289)
                  ·
                    refine ⟨6757692962335590494875717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9010257283114120659834289 6757692962335590494875717)
                    ·
                      refine ⟨1267067430437923217789197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6757692962335590494875717 1267067430437923217789197)
                      ·
                        rfl

theorem cell23_2467605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_2467605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467605 prefixEnd_2467605 := by exact prefixLift 2467605
  have htrace : WordTrace (prefixWord ++ tailWord_2467605) baseStart_2467605 baseEnd_2467605 := by
    simpa [prefixWord, tailWord_2467605, baseEnd_2467605] using wordTrace_append hprefix tailTrace_2467605
  have hstable : (prefixWord ++ tailWord_2467605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467605).length < 2 ^ (prefixWord ++ tailWord_2467605).sum := by decide
  have hdescent : baseEnd_2467605 < baseStart_2467605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467615 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 7]
def baseStart_2467615 : Nat := 118140960795 + 2467615 * 2 ^ 59
def prefixEnd_2467615 : Nat := 4983230072969 + 3 ^ 40 * 2467615 * 2
def baseEnd_2467615 : Nat := 140785840582718686518239

theorem tailTrace_2467615 : CollatzResearch.WordTrace tailWord_2467615 prefixEnd_2467615 140785840582718686518239 := by
  unfold tailWord_2467615
  simp only [CollatzResearch.WordTrace]
  refine ⟨90001312955259764934948299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60000875303506509956632199 90001312955259764934948299)
  ·
    refine ⟨135001969432889647402422449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90001312955259764934948299 135001969432889647402422449)
    ·
      refine ⟨101251477074667235551816837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135001969432889647402422449 101251477074667235551816837)
      ·
        refine ⟨18984651951500106665965657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101251477074667235551816837 18984651951500106665965657)
        ·
          refine ⟨14238488963625079999474243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18984651951500106665965657 14238488963625079999474243)
          ·
            refine ⟨21357733445437619999211365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14238488963625079999474243 21357733445437619999211365)
            ·
              refine ⟨4004575021019553749852131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21357733445437619999211365 4004575021019553749852131)
              ·
                refine ⟨6006862531529330624778197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4004575021019553749852131 6006862531529330624778197)
                ·
                  refine ⟨140785840582718686518239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6006862531529330624778197 140785840582718686518239)
                  ·
                    rfl

theorem cell23_2467615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 7].length) (baseStart_2467615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467615 prefixEnd_2467615 := by exact prefixLift 2467615
  have htrace : WordTrace (prefixWord ++ tailWord_2467615) baseStart_2467615 baseEnd_2467615 := by
    simpa [prefixWord, tailWord_2467615, baseEnd_2467615] using wordTrace_append hprefix tailTrace_2467615
  have hstable : (prefixWord ++ tailWord_2467615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467615).length < 2 ^ (prefixWord ++ tailWord_2467615).sum := by decide
  have hdescent : baseEnd_2467615 < baseStart_2467615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467709 : List Nat := [1, 4, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_2467709 : Nat := 118140960795 + 2467709 * 2 ^ 59
def prefixEnd_2467709 : Nat := 4983230072969 + 3 ^ 40 * 2467709 * 2
def baseEnd_2467709 : Nat := 422373610808663603629573

theorem tailTrace_2467709 : CollatzResearch.WordTrace tailWord_2467709 prefixEnd_2467709 422373610808663603629573 := by
  unfold tailWord_2467709
  simp only [CollatzResearch.WordTrace]
  refine ⟨90004741416919218988870181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60003160944612812659246787 90004741416919218988870181)
  ·
    refine ⟨16875889015672353560413159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90004741416919218988870181 16875889015672353560413159)
    ·
      refine ⟨25313833523508530340619739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16875889015672353560413159 25313833523508530340619739)
      ·
        refine ⟨37970750285262795510929609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25313833523508530340619739 37970750285262795510929609)
        ·
          refine ⟨28478062713947096633197207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37970750285262795510929609 28478062713947096633197207)
          ·
            refine ⟨42717094070920644949795811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28478062713947096633197207 42717094070920644949795811)
            ·
              refine ⟨64075641106380967424693717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42717094070920644949795811 64075641106380967424693717)
              ·
                refine ⟨1501772838430803924016259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 64075641106380967424693717 1501772838430803924016259)
                ·
                  refine ⟨2252659257646205886024389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501772838430803924016259 2252659257646205886024389)
                  ·
                    refine ⟨422373610808663603629573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2252659257646205886024389 422373610808663603629573)
                    ·
                      rfl

theorem cell23_2467709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_2467709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467709 prefixEnd_2467709 := by exact prefixLift 2467709
  have htrace : WordTrace (prefixWord ++ tailWord_2467709) baseStart_2467709 baseEnd_2467709 := by
    simpa [prefixWord, tailWord_2467709, baseEnd_2467709] using wordTrace_append hprefix tailTrace_2467709
  have hstable : (prefixWord ++ tailWord_2467709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467709).length < 2 ^ (prefixWord ++ tailWord_2467709).sum := by decide
  have hdescent : baseEnd_2467709 < baseStart_2467709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467785 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_2467785 : Nat := 118140960795 + 2467785 * 2 ^ 59
def prefixEnd_2467785 : Nat := 4983230072969 + 3 ^ 40 * 2467785 * 2
def baseEnd_2467785 : Nat := 1267159856955732513538369

theorem tailTrace_2467785 : CollatzResearch.WordTrace tailWord_2467785 prefixEnd_2467785 1267159856955732513538369 := by
  unfold tailWord_2467785
  simp only [CollatzResearch.WordTrace]
  refine ⟨90007513364643883968636809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60005008909762589312424539 90007513364643883968636809)
  ·
    refine ⟨67505635023482912976477607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90007513364643883968636809 67505635023482912976477607)
    ·
      refine ⟨101258452535224369464716411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67505635023482912976477607 101258452535224369464716411)
      ·
        refine ⟨151887678802836554197074617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101258452535224369464716411 151887678802836554197074617)
        ·
          refine ⟨113915759102127415647805963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151887678802836554197074617 113915759102127415647805963)
          ·
            refine ⟨170873638653191123471708945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113915759102127415647805963 170873638653191123471708945)
            ·
              refine ⟨128155228989893342603781709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170873638653191123471708945 128155228989893342603781709)
              ·
                refine ⟨48058210871210003476418141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128155228989893342603781709 48058210871210003476418141)
                ·
                  refine ⟨18021829076703751303656803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48058210871210003476418141 18021829076703751303656803)
                  ·
                    refine ⟨27032743615055626955485205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18021829076703751303656803 27032743615055626955485205)
                    ·
                      refine ⟨1267159856955732513538369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27032743615055626955485205 1267159856955732513538369)
                      ·
                        rfl

theorem cell23_2467785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_2467785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467785 prefixEnd_2467785 := by exact prefixLift 2467785
  have htrace : WordTrace (prefixWord ++ tailWord_2467785) baseStart_2467785 baseEnd_2467785 := by
    simpa [prefixWord, tailWord_2467785, baseEnd_2467785] using wordTrace_append hprefix tailTrace_2467785
  have hstable : (prefixWord ++ tailWord_2467785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467785).length < 2 ^ (prefixWord ++ tailWord_2467785).sum := by decide
  have hdescent : baseEnd_2467785 < baseStart_2467785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467792 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 3]
def baseStart_2467792 : Nat := 118140960795 + 2467792 * 2 ^ 59
def prefixEnd_2467792 : Nat := 4983230072969 + 3 ^ 40 * 2467792 * 2
def baseEnd_2467792 : Nat := 1267163451320313986150837

theorem tailTrace_2467792 : CollatzResearch.WordTrace tailWord_2467792 prefixEnd_2467792 1267163451320313986150837 := by
  unfold tailWord_2467792
  simp only [CollatzResearch.WordTrace]
  refine ⟨45003884337809262082070815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60005179117079016109427753 45003884337809262082070815)
  ·
    refine ⟨67505826506713893123106223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45003884337809262082070815 67505826506713893123106223)
    ·
      refine ⟨101258739760070839684659335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67505826506713893123106223 101258739760070839684659335)
      ·
        refine ⟨151888109640106259526989003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101258739760070839684659335 151888109640106259526989003)
        ·
          refine ⟨227832164460159389290483505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151888109640106259526989003 227832164460159389290483505)
          ·
            refine ⟨170874123345119541967862629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227832164460159389290483505 170874123345119541967862629)
            ·
              refine ⟨32038898127209914118974243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170874123345119541967862629 32038898127209914118974243)
              ·
                refine ⟨48058347190814871178461365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32038898127209914118974243 48058347190814871178461365)
                ·
                  refine ⟨4505470049138894172980753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48058347190814871178461365 4505470049138894172980753)
                  ·
                    refine ⟨3379102536854170629735565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4505470049138894172980753 3379102536854170629735565)
                    ·
                      refine ⟨1267163451320313986150837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3379102536854170629735565 1267163451320313986150837)
                      ·
                        rfl

theorem cell23_2467792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 3].length) (baseStart_2467792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467792 prefixEnd_2467792 := by exact prefixLift 2467792
  have htrace : WordTrace (prefixWord ++ tailWord_2467792) baseStart_2467792 baseEnd_2467792 := by
    simpa [prefixWord, tailWord_2467792, baseEnd_2467792] using wordTrace_append hprefix tailTrace_2467792
  have hstable : (prefixWord ++ tailWord_2467792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467792).length < 2 ^ (prefixWord ++ tailWord_2467792).sum := by decide
  have hdescent : baseEnd_2467792 < baseStart_2467792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467809 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_2467809 : Nat := 118140960795 + 2467809 * 2 ^ 59
def prefixEnd_2467809 : Nat := 4983230072969 + 3 ^ 40 * 2467809 * 2
def baseEnd_2467809 : Nat := 1267172180491440419638259

theorem tailTrace_2467809 : CollatzResearch.WordTrace tailWord_2467809 prefixEnd_2467809 1267172180491440419638259 := by
  unfold tailWord_2467809
  simp only [CollatzResearch.WordTrace]
  refine ⟨90008388716556936067510481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60005592477704624045006987 90008388716556936067510481)
  ·
    refine ⟨67506291537417702050632861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90008388716556936067510481 67506291537417702050632861)
    ·
      refine ⟨25314859326531638268987323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67506291537417702050632861 25314859326531638268987323)
      ·
        refine ⟨37972288989797457403480985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25314859326531638268987323 37972288989797457403480985)
        ·
          refine ⟨28479216742348093052610739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37972288989797457403480985 28479216742348093052610739)
          ·
            refine ⟨42718825113522139578916109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28479216742348093052610739 42718825113522139578916109)
            ·
              refine ⟨16019559417570802342093541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42718825113522139578916109 16019559417570802342093541)
              ·
                refine ⟨3003667390794525439142539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16019559417570802342093541 3003667390794525439142539)
                ·
                  refine ⟨4505501086191788158713809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3003667390794525439142539 4505501086191788158713809)
                  ·
                    refine ⟨3379125814643841119035357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4505501086191788158713809 3379125814643841119035357)
                    ·
                      refine ⟨1267172180491440419638259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3379125814643841119035357 1267172180491440419638259)
                      ·
                        rfl

theorem cell23_2467809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_2467809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467809 prefixEnd_2467809 := by exact prefixLift 2467809
  have htrace : WordTrace (prefixWord ++ tailWord_2467809) baseStart_2467809 baseEnd_2467809 := by
    simpa [prefixWord, tailWord_2467809, baseEnd_2467809] using wordTrace_append hprefix tailTrace_2467809
  have hstable : (prefixWord ++ tailWord_2467809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467809).length < 2 ^ (prefixWord ++ tailWord_2467809).sum := by decide
  have hdescent : baseEnd_2467809 < baseStart_2467809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467850 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 2, 4]
def baseStart_2467850 : Nat := 118140960795 + 2467850 * 2 ^ 59
def prefixEnd_2467850 : Nat := 4983230072969 + 3 ^ 40 * 2467850 * 2
def baseEnd_2467850 : Nat := 422397744399424919741857

theorem tailTrace_2467850 : CollatzResearch.WordTrace tailWord_2467850 prefixEnd_2467850 422397744399424919741857 := by
  unfold tailWord_2467850
  simp only [CollatzResearch.WordTrace]
  refine ⟨22502471027352100017438251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60006589406272266713168669 22502471027352100017438251)
  ·
    refine ⟨33753706541028150026157377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22502471027352100017438251 33753706541028150026157377)
    ·
      refine ⟨25315279905771112519618033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33753706541028150026157377 25315279905771112519618033)
      ·
        refine ⟨18986459929328334389713525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25315279905771112519618033 18986459929328334389713525)
        ·
          refine ⟨1779980618374531349035643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18986459929328334389713525 1779980618374531349035643)
          ·
            refine ⟨2669970927561797023553465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779980618374531349035643 2669970927561797023553465)
            ·
              refine ⟨2002478195671347767665099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2669970927561797023553465 2002478195671347767665099)
              ·
                refine ⟨3003717293507021651497649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002478195671347767665099 3003717293507021651497649)
                ·
                  refine ⟨2252787970130266238623237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3003717293507021651497649 2252787970130266238623237)
                  ·
                    refine ⟨422397744399424919741857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2252787970130266238623237 422397744399424919741857)
                    ·
                      rfl

theorem cell23_2467850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_2467850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467850 prefixEnd_2467850 := by exact prefixLift 2467850
  have htrace : WordTrace (prefixWord ++ tailWord_2467850) baseStart_2467850 baseEnd_2467850 := by
    simpa [prefixWord, tailWord_2467850, baseEnd_2467850] using wordTrace_append hprefix tailTrace_2467850
  have hstable : (prefixWord ++ tailWord_2467850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467850).length < 2 ^ (prefixWord ++ tailWord_2467850).sum := by decide
  have hdescent : baseEnd_2467850 < baseStart_2467850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467866 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2]
def baseStart_2467866 : Nat := 118140960795 + 2467866 * 2 ^ 59
def prefixEnd_2467866 : Nat := 4983230072969 + 3 ^ 40 * 2467866 * 2
def baseEnd_2467866 : Nat := 1267201448888746696625497

theorem tailTrace_2467866 : CollatzResearch.WordTrace tailWord_2467866 prefixEnd_2467866 1267201448888746696625497 := by
  unfold tailWord_2467866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22502616919337608700583863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60006978451566956534890301 22502616919337608700583863)
  ·
    refine ⟨33753925379006413050875795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22502616919337608700583863 33753925379006413050875795)
    ·
      refine ⟨50630888068509619576313693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33753925379006413050875795 50630888068509619576313693)
      ·
        refine ⟨18986583025691107341117635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50630888068509619576313693 18986583025691107341117635)
        ·
          refine ⟨28479874538536661011676453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18986583025691107341117635 28479874538536661011676453)
          ·
            refine ⟨5339976475975623939689335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28479874538536661011676453 5339976475975623939689335)
            ·
              refine ⟨8009964713963435909534003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5339976475975623939689335 8009964713963435909534003)
              ·
                refine ⟨12014947070945153864301005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8009964713963435909534003 12014947070945153864301005)
                ·
                  refine ⟨4505605151604432699112877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12014947070945153864301005 4505605151604432699112877)
                  ·
                    refine ⟨1689601931851662262167329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4505605151604432699112877 1689601931851662262167329)
                    ·
                      refine ⟨1267201448888746696625497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1689601931851662262167329 1267201448888746696625497)
                      ·
                        rfl

theorem cell23_2467866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_2467866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467866 prefixEnd_2467866 := by exact prefixLift 2467866
  have htrace : WordTrace (prefixWord ++ tailWord_2467866) baseStart_2467866 baseEnd_2467866 := by
    simpa [prefixWord, tailWord_2467866, baseEnd_2467866] using wordTrace_append hprefix tailTrace_2467866
  have hstable : (prefixWord ++ tailWord_2467866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467866).length < 2 ^ (prefixWord ++ tailWord_2467866).sum := by decide
  have hdescent : baseEnd_2467866 < baseStart_2467866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467936 : List Nat := [2, 1, 1, 3, 2, 4, 2, 3, 5]
def baseStart_2467936 : Nat := 118140960795 + 2467936 * 2 ^ 59
def prefixEnd_2467936 : Nat := 4983230072969 + 3 ^ 40 * 2467936 * 2
def baseEnd_2467936 : Nat := 140804154726062380305575

theorem tailTrace_2467936 : CollatzResearch.WordTrace tailWord_2467936 prefixEnd_2467936 140804154726062380305575 := by
  unfold tailWord_2467936
  simp only [CollatzResearch.WordTrace]
  refine ⟨45006510393548418378691831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60008680524731224504922441 45006510393548418378691831)
  ·
    refine ⟨67509765590322627568037747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45006510393548418378691831 67509765590322627568037747)
    ·
      refine ⟨101264648385483941352056621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67509765590322627568037747 101264648385483941352056621)
      ·
        refine ⟨37974243144556478007021233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101264648385483941352056621 37974243144556478007021233)
        ·
          refine ⟨28480682358417358505265925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37974243144556478007021233 28480682358417358505265925)
          ·
            refine ⟨5340127942203254719737361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28480682358417358505265925 5340127942203254719737361)
            ·
              refine ⟨4005095956652441039803021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5340127942203254719737361 4005095956652441039803021)
              ·
                refine ⟨1501910983744665389926133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4005095956652441039803021 1501910983744665389926133)
                ·
                  refine ⟨140804154726062380305575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1501910983744665389926133 140804154726062380305575)
                  ·
                    rfl

theorem cell23_2467936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 5].length) (baseStart_2467936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467936 prefixEnd_2467936 := by exact prefixLift 2467936
  have htrace : WordTrace (prefixWord ++ tailWord_2467936) baseStart_2467936 baseEnd_2467936 := by
    simpa [prefixWord, tailWord_2467936, baseEnd_2467936] using wordTrace_append hprefix tailTrace_2467936
  have hstable : (prefixWord ++ tailWord_2467936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467936).length < 2 ^ (prefixWord ++ tailWord_2467936).sum := by decide
  have hdescent : baseEnd_2467936 < baseStart_2467936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467949 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_2467949 : Nat := 118140960795 + 2467949 * 2 ^ 59
def prefixEnd_2467949 : Nat := 4983230072969 + 3 ^ 40 * 2467949 * 2
def baseEnd_2467949 : Nat := 422414689261023290629205

theorem tailTrace_2467949 : CollatzResearch.WordTrace tailWord_2467949 prefixEnd_2467949 422414689261023290629205 := by
  unfold tailWord_2467949
  simp only [CollatzResearch.WordTrace]
  refine ⟨90013494936049739977606901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60008996624033159985071267 90013494936049739977606901)
  ·
    refine ⟨8438765150254663122900647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90013494936049739977606901 8438765150254663122900647)
    ·
      refine ⟨12658147725381994684350971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8438765150254663122900647 12658147725381994684350971)
      ·
        refine ⟨18987221588072992026526457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12658147725381994684350971 18987221588072992026526457)
        ·
          refine ⟨14240416191054744019894843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18987221588072992026526457 14240416191054744019894843)
          ·
            refine ⟨21360624286582116029842265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14240416191054744019894843 21360624286582116029842265)
            ·
              refine ⟨16020468214936587022381699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21360624286582116029842265 16020468214936587022381699)
              ·
                refine ⟨24030702322404880533572549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16020468214936587022381699 24030702322404880533572549)
                ·
                  refine ⟨4505756685450915100044853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24030702322404880533572549 4505756685450915100044853)
                  ·
                    refine ⟨422414689261023290629205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4505756685450915100044853 422414689261023290629205)
                    ·
                      rfl

theorem cell23_2467949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_2467949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467949 prefixEnd_2467949 := by exact prefixLift 2467949
  have htrace : WordTrace (prefixWord ++ tailWord_2467949) baseStart_2467949 baseEnd_2467949 := by
    simpa [prefixWord, tailWord_2467949, baseEnd_2467949] using wordTrace_append hprefix tailTrace_2467949
  have hstable : (prefixWord ++ tailWord_2467949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467949).length < 2 ^ (prefixWord ++ tailWord_2467949).sum := by decide
  have hdescent : baseEnd_2467949 < baseStart_2467949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467986 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_2467986 : Nat := 118140960795 + 2467986 * 2 ^ 59
def prefixEnd_2467986 : Nat := 4983230072969 + 3 ^ 40 * 2467986 * 2
def baseEnd_2467986 : Nat := 1267263066567286227124945

theorem tailTrace_2467986 : CollatzResearch.WordTrace tailWord_2467986 prefixEnd_2467986 1267263066567286227124945 := by
  unfold tailWord_2467986
  simp only [CollatzResearch.WordTrace]
  refine ⟨22503711109228923824175953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60009896291277130197802541 22503711109228923824175953)
  ·
    refine ⟨16877783331921692868131965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22503711109228923824175953 16877783331921692868131965)
    ·
      refine ⟨6329168749470634825549487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16877783331921692868131965 6329168749470634825549487)
      ·
        refine ⟨9493753124205952238324231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6329168749470634825549487 9493753124205952238324231)
        ·
          refine ⟨14240629686308928357486347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9493753124205952238324231 14240629686308928357486347)
          ·
            refine ⟨21360944529463392536229521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14240629686308928357486347 21360944529463392536229521)
            ·
              refine ⟨16020708397097544402172141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21360944529463392536229521 16020708397097544402172141)
              ·
                refine ⟨6007765648911579150814553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16020708397097544402172141 6007765648911579150814553)
                ·
                  refine ⟨4505824236683684363110915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6007765648911579150814553 4505824236683684363110915)
                  ·
                    refine ⟨6758736355025526544666373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4505824236683684363110915 6758736355025526544666373)
                    ·
                      refine ⟨1267263066567286227124945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6758736355025526544666373 1267263066567286227124945)
                      ·
                        rfl

theorem cell23_2467986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_2467986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467986 prefixEnd_2467986 := by exact prefixLift 2467986
  have htrace : WordTrace (prefixWord ++ tailWord_2467986) baseStart_2467986 baseEnd_2467986 := by
    simpa [prefixWord, tailWord_2467986, baseEnd_2467986] using wordTrace_append hprefix tailTrace_2467986
  have hstable : (prefixWord ++ tailWord_2467986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467986).length < 2 ^ (prefixWord ++ tailWord_2467986).sum := by decide
  have hdescent : baseEnd_2467986 < baseStart_2467986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467989 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_2467989 : Nat := 118140960795 + 2467989 * 2 ^ 59
def prefixEnd_2467989 : Nat := 4983230072969 + 3 ^ 40 * 2467989 * 2
def baseEnd_2467989 : Nat := 1267264607009249715387431

theorem tailTrace_2467989 : CollatzResearch.WordTrace tailWord_2467989 prefixEnd_2467989 1267264607009249715387431 := by
  unfold tailWord_2467989
  simp only [CollatzResearch.WordTrace]
  refine ⟨90014953855904826809063021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60009969237269884539375347 90014953855904826809063021)
  ·
    refine ⟨33755607695964310053398633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90014953855904826809063021 33755607695964310053398633)
    ·
      refine ⟨25316705771973232540048975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33755607695964310053398633 25316705771973232540048975)
      ·
        refine ⟨37975058657959848810073463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25316705771973232540048975 37975058657959848810073463)
        ·
          refine ⟨56962587986939773215110195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37975058657959848810073463 56962587986939773215110195)
          ·
            refine ⟨85443881980409659822665293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56962587986939773215110195 85443881980409659822665293)
            ·
              refine ⟨32041455742653622433499485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85443881980409659822665293 32041455742653622433499485)
              ·
                refine ⟨12015545903495108412562307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32041455742653622433499485 12015545903495108412562307)
                ·
                  refine ⟨18023318855242662618843461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12015545903495108412562307 18023318855242662618843461)
                  ·
                    refine ⟨3379372285357999241033149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18023318855242662618843461 3379372285357999241033149)
                    ·
                      refine ⟨1267264607009249715387431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3379372285357999241033149 1267264607009249715387431)
                      ·
                        rfl

theorem cell23_2467989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_2467989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2467989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2467989 prefixEnd_2467989 := by exact prefixLift 2467989
  have htrace : WordTrace (prefixWord ++ tailWord_2467989) baseStart_2467989 baseEnd_2467989 := by
    simpa [prefixWord, tailWord_2467989, baseEnd_2467989] using wordTrace_append hprefix tailTrace_2467989
  have hstable : (prefixWord ++ tailWord_2467989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467989).length < 2 ^ (prefixWord ++ tailWord_2467989).sum := by decide
  have hdescent : baseEnd_2467989 < baseStart_2467989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468013 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2468013 : Nat := 118140960795 + 2468013 * 2 ^ 59
def prefixEnd_2468013 : Nat := 4983230072969 + 3 ^ 40 * 2468013 * 2
def baseEnd_2468013 : Nat := 422425643514985873829107

theorem tailTrace_2468013 : CollatzResearch.WordTrace tailWord_2468013 prefixEnd_2468013 422425643514985873829107 := by
  unfold tailWord_2468013
  simp only [CollatzResearch.WordTrace]
  refine ⟨90015829207817878907936693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60010552805211919271957795 90015829207817878907936693)
  ·
    refine ⟨8438983988232926147619065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90015829207817878907936693 8438983988232926147619065)
    ·
      refine ⟨6329237991174694610714299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8438983988232926147619065 6329237991174694610714299)
      ·
        refine ⟨9493856986762041916071449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6329237991174694610714299 9493856986762041916071449)
        ·
          refine ⟨7120392740071531437053587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9493856986762041916071449 7120392740071531437053587)
          ·
            refine ⟨10680589110107297155580381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7120392740071531437053587 10680589110107297155580381)
            ·
              refine ⟨4005220916290236433342643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10680589110107297155580381 4005220916290236433342643)
              ·
                refine ⟨6007831374435354650013965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4005220916290236433342643 6007831374435354650013965)
                ·
                  refine ⟨2252936765413257993755237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6007831374435354650013965 2252936765413257993755237)
                  ·
                    refine ⟨422425643514985873829107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2252936765413257993755237 422425643514985873829107)
                    ·
                      rfl

theorem cell23_2468013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2468013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468013 prefixEnd_2468013 := by exact prefixLift 2468013
  have htrace : WordTrace (prefixWord ++ tailWord_2468013) baseStart_2468013 baseEnd_2468013 := by
    simpa [prefixWord, tailWord_2468013, baseEnd_2468013] using wordTrace_append hprefix tailTrace_2468013
  have hstable : (prefixWord ++ tailWord_2468013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468013).length < 2 ^ (prefixWord ++ tailWord_2468013).sum := by decide
  have hdescent : baseEnd_2468013 < baseStart_2468013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468026 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 6]
def baseStart_2468026 : Nat := 118140960795 + 2468026 * 2 ^ 59
def prefixEnd_2468026 : Nat := 4983230072969 + 3 ^ 40 * 2468026 * 2
def baseEnd_2468026 : Nat := 140809289532607341180529

theorem tailTrace_2468026 : CollatzResearch.WordTrace tailWord_2468026 prefixEnd_2468026 140809289532607341180529 := by
  unfold tailWord_2468026
  simp only [CollatzResearch.WordTrace]
  refine ⟨22504075839192695532039983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60010868904513854752106621 22504075839192695532039983)
  ·
    refine ⟨33756113758789043298059975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22504075839192695532039983 33756113758789043298059975)
    ·
      refine ⟨50634170638183564947089963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33756113758789043298059975 50634170638183564947089963)
      ·
        refine ⟨75951255957275347420634945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50634170638183564947089963 75951255957275347420634945)
        ·
          refine ⟨56963441967956510565476209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75951255957275347420634945 56963441967956510565476209)
          ·
            refine ⟨42722581475967382924107157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56963441967956510565476209 42722581475967382924107157)
            ·
              refine ⟨2002621006685971074567523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42722581475967382924107157 2002621006685971074567523)
              ·
                refine ⟨3003931510028956611851285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002621006685971074567523 3003931510028956611851285)
                ·
                  refine ⟨140809289532607341180529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3003931510028956611851285 140809289532607341180529)
                  ·
                    rfl

theorem cell23_2468026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_2468026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468026 prefixEnd_2468026 := by exact prefixLift 2468026
  have htrace : WordTrace (prefixWord ++ tailWord_2468026) baseStart_2468026 baseEnd_2468026 := by
    simpa [prefixWord, tailWord_2468026, baseEnd_2468026] using wordTrace_append hprefix tailTrace_2468026
  have hstable : (prefixWord ++ tailWord_2468026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468026).length < 2 ^ (prefixWord ++ tailWord_2468026).sum := by decide
  have hdescent : baseEnd_2468026 < baseStart_2468026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468059 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 4]
def baseStart_2468059 : Nat := 118140960795 + 2468059 * 2 ^ 59
def prefixEnd_2468059 : Nat := 4983230072969 + 3 ^ 40 * 2468059 * 2
def baseEnd_2468059 : Nat := 1267300550655064441512109

theorem tailTrace_2468059 : CollatzResearch.WordTrace tailWord_2468059 prefixEnd_2468059 1267300550655064441512109 := by
  unfold tailWord_2468059
  simp only [CollatzResearch.WordTrace]
  refine ⟨90017506965651228764111231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60011671310434152509407487 90017506965651228764111231)
  ·
    refine ⟨135026260448476843146166847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90017506965651228764111231 135026260448476843146166847)
    ·
      refine ⟨202539390672715264719250271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135026260448476843146166847 202539390672715264719250271)
      ·
        refine ⟨303809086009072897078875407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202539390672715264719250271 303809086009072897078875407)
        ·
          refine ⟨455713629013609345618313111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303809086009072897078875407 455713629013609345618313111)
          ·
            refine ⟨683570443520414018427469667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455713629013609345618313111 683570443520414018427469667)
            ·
              refine ⟨1025355665280621027641204501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683570443520414018427469667 1025355665280621027641204501)
              ·
                refine ⟨48063546810029110670681461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1025355665280621027641204501 48063546810029110670681461)
                ·
                  refine ⟨4505957513440229125376387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48063546810029110670681461 4505957513440229125376387)
                  ·
                    refine ⟨6758936270160343688064581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4505957513440229125376387 6758936270160343688064581)
                    ·
                      refine ⟨1267300550655064441512109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6758936270160343688064581 1267300550655064441512109)
                      ·
                        rfl

theorem cell23_2468059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 4].length) (baseStart_2468059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468059 prefixEnd_2468059 := by exact prefixLift 2468059
  have htrace : WordTrace (prefixWord ++ tailWord_2468059) baseStart_2468059 baseEnd_2468059 := by
    simpa [prefixWord, tailWord_2468059, baseEnd_2468059] using wordTrace_append hprefix tailTrace_2468059
  have hstable : (prefixWord ++ tailWord_2468059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468059).length < 2 ^ (prefixWord ++ tailWord_2468059).sum := by decide
  have hdescent : baseEnd_2468059 < baseStart_2468059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468060 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 6]
def baseStart_2468060 : Nat := 118140960795 + 2468060 * 2 ^ 59
def prefixEnd_2468060 : Nat := 4983230072969 + 3 ^ 40 * 2468060 * 2
def baseEnd_2468060 : Nat := 140811229348413215288845

theorem tailTrace_2468060 : CollatzResearch.WordTrace tailWord_2468060 prefixEnd_2468060 140811229348413215288845 := by
  unfold tailWord_2468060
  simp only [CollatzResearch.WordTrace]
  refine ⟨45008771719323802967448817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60011695625765070623265089 45008771719323802967448817)
  ·
    refine ⟨33756578789492852225586613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45008771719323802967448817 33756578789492852225586613)
    ·
      refine ⟨3164679261514954896148745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33756578789492852225586613 3164679261514954896148745)
      ·
        refine ⟨2373509446136216172111559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3164679261514954896148745 2373509446136216172111559)
        ·
          refine ⟨3560264169204324258167339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373509446136216172111559 3560264169204324258167339)
          ·
            refine ⟨5340396253806486387251009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560264169204324258167339 5340396253806486387251009)
            ·
              refine ⟨4005297190354864790438257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5340396253806486387251009 4005297190354864790438257)
              ·
                refine ⟨3003972892766148592828693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4005297190354864790438257 3003972892766148592828693)
                ·
                  refine ⟨140811229348413215288845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3003972892766148592828693 140811229348413215288845)
                  ·
                    rfl

theorem cell23_2468060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_2468060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468060 prefixEnd_2468060 := by exact prefixLift 2468060
  have htrace : WordTrace (prefixWord ++ tailWord_2468060) baseStart_2468060 baseEnd_2468060 := by
    simpa [prefixWord, tailWord_2468060, baseEnd_2468060] using wordTrace_append hprefix tailTrace_2468060
  have hstable : (prefixWord ++ tailWord_2468060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468060).length < 2 ^ (prefixWord ++ tailWord_2468060).sum := by decide
  have hdescent : baseEnd_2468060 < baseStart_2468060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468086 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_2468086 : Nat := 118140960795 + 2468086 * 2 ^ 59
def prefixEnd_2468086 : Nat := 4983230072969 + 3 ^ 40 * 2468086 * 2
def baseEnd_2468086 : Nat := 422438138210911945291495

theorem tailTrace_2468086 : CollatzResearch.WordTrace tailWord_2468086 prefixEnd_2468086 422438138210911945291495 := by
  unfold tailWord_2468086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5626155733534588273459007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60012327824368941583562741 5626155733534588273459007)
  ·
    refine ⟨8439233600301882410188511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5626155733534588273459007 8439233600301882410188511)
    ·
      refine ⟨12658850400452823615282767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8439233600301882410188511 12658850400452823615282767)
      ·
        refine ⟨18988275600679235422924151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12658850400452823615282767 18988275600679235422924151)
        ·
          refine ⟨28482413401018853134386227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18988275600679235422924151 28482413401018853134386227)
          ·
            refine ⟨42723620101528279701579341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28482413401018853134386227 42723620101528279701579341)
            ·
              refine ⟨16021357538073104888092253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42723620101528279701579341 16021357538073104888092253)
              ·
                refine ⟨6008009076777414333034595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16021357538073104888092253 6008009076777414333034595)
                ·
                  refine ⟨9012013615166121499551893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6008009076777414333034595 9012013615166121499551893)
                  ·
                    refine ⟨422438138210911945291495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9012013615166121499551893 422438138210911945291495)
                    ·
                      rfl

theorem cell23_2468086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_2468086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468086 prefixEnd_2468086 := by exact prefixLift 2468086
  have htrace : WordTrace (prefixWord ++ tailWord_2468086) baseStart_2468086 baseEnd_2468086 := by
    simpa [prefixWord, tailWord_2468086, baseEnd_2468086] using wordTrace_append hprefix tailTrace_2468086
  have hstable : (prefixWord ++ tailWord_2468086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468086).length < 2 ^ (prefixWord ++ tailWord_2468086).sum := by decide
  have hdescent : baseEnd_2468086 < baseStart_2468086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468096 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 3]
def baseStart_2468096 : Nat := 118140960795 + 2468096 * 2 ^ 59
def prefixEnd_2468096 : Nat := 4983230072969 + 3 ^ 40 * 2468096 * 2
def baseEnd_2468096 : Nat := 1267319549439280796749439

theorem tailTrace_2468096 : CollatzResearch.WordTrace tailWord_2468096 prefixEnd_2468096 1267319549439280796749439 := by
  unfold tailWord_2468096
  simp only [CollatzResearch.WordTrace]
  refine ⟨45009428233258592041604071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60012570977678122722138761 45009428233258592041604071)
  ·
    refine ⟨67514142349887888062406107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45009428233258592041604071 67514142349887888062406107)
    ·
      refine ⟨101271213524831832093609161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67514142349887888062406107 101271213524831832093609161)
      ·
        refine ⟨75953410143623874070206871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101271213524831832093609161 75953410143623874070206871)
        ·
          refine ⟨113930115215435811105310307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75953410143623874070206871 113930115215435811105310307)
          ·
            refine ⟨170895172823153716657965461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113930115215435811105310307 170895172823153716657965461)
            ·
              refine ⟨8010711226085330468342131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 170895172823153716657965461 8010711226085330468342131)
              ·
                refine ⟨12016066839127995702513197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8010711226085330468342131 12016066839127995702513197)
                ·
                  refine ⟨4506025064672998388442449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12016066839127995702513197 4506025064672998388442449)
                  ·
                    refine ⟨3379518798504748791331837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4506025064672998388442449 3379518798504748791331837)
                    ·
                      refine ⟨1267319549439280796749439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3379518798504748791331837 1267319549439280796749439)
                      ·
                        rfl

theorem cell23_2468096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_2468096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468096 prefixEnd_2468096 := by exact prefixLift 2468096
  have htrace : WordTrace (prefixWord ++ tailWord_2468096) baseStart_2468096 baseEnd_2468096 := by
    simpa [prefixWord, tailWord_2468096, baseEnd_2468096] using wordTrace_append hprefix tailTrace_2468096
  have hstable : (prefixWord ++ tailWord_2468096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468096).length < 2 ^ (prefixWord ++ tailWord_2468096).sum := by decide
  have hdescent : baseEnd_2468096 < baseStart_2468096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468106 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_2468106 : Nat := 118140960795 + 2468106 * 2 ^ 59
def prefixEnd_2468106 : Nat := 4983230072969 + 3 ^ 40 * 2468106 * 2
def baseEnd_2468106 : Nat := 1267324684245825757624393

theorem tailTrace_2468106 : CollatzResearch.WordTrace tailWord_2468106 prefixEnd_2468106 1267324684245825757624393 := by
  unfold tailWord_2468106
  simp only [CollatzResearch.WordTrace]
  refine ⟨22504805299120238947768043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60012814130987303860714781 22504805299120238947768043)
  ·
    refine ⟨33757207948680358421652065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22504805299120238947768043 33757207948680358421652065)
    ·
      refine ⟨25317905961510268816239049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33757207948680358421652065 25317905961510268816239049)
      ·
        refine ⟨18988429471132701612179287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25317905961510268816239049 18988429471132701612179287)
        ·
          refine ⟨28482644206699052418268931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18988429471132701612179287 28482644206699052418268931)
          ·
            refine ⟨42723966310048578627403397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28482644206699052418268931 42723966310048578627403397)
            ·
              refine ⟨8010743683134108492638137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42723966310048578627403397 8010743683134108492638137)
              ·
                refine ⟨6008057762350581369478603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8010743683134108492638137 6008057762350581369478603)
                ·
                  refine ⟨9012086643525872054217905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6008057762350581369478603 9012086643525872054217905)
                  ·
                    refine ⟨6759064982644404040663429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9012086643525872054217905 6759064982644404040663429)
                    ·
                      refine ⟨1267324684245825757624393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6759064982644404040663429 1267324684245825757624393)
                      ·
                        rfl

theorem cell23_2468106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_2468106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468106 prefixEnd_2468106 := by exact prefixLift 2468106
  have htrace : WordTrace (prefixWord ++ tailWord_2468106) baseStart_2468106 baseEnd_2468106 := by
    simpa [prefixWord, tailWord_2468106, baseEnd_2468106] using wordTrace_append hprefix tailTrace_2468106
  have hstable : (prefixWord ++ tailWord_2468106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468106).length < 2 ^ (prefixWord ++ tailWord_2468106).sum := by decide
  have hdescent : baseEnd_2468106 < baseStart_2468106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468113 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 3]
def baseStart_2468113 : Nat := 118140960795 + 2468113 * 2 ^ 59
def prefixEnd_2468113 : Nat := 4983230072969 + 3 ^ 40 * 2468113 * 2
def baseEnd_2468113 : Nat := 1267328278610407230236861

theorem tailTrace_2468113 : CollatzResearch.WordTrace tailWord_2468113 prefixEnd_2468113 1267328278610407230236861 := by
  unfold tailWord_2468113
  simp only [CollatzResearch.WordTrace]
  refine ⟨90019476507455595986576993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60012984338303730657717995 90019476507455595986576993)
  ·
    refine ⟨67514607380591696989932745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90019476507455595986576993 67514607380591696989932745)
    ·
      refine ⟨50635955535443772742449559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67514607380591696989932745 50635955535443772742449559)
      ·
        refine ⟨75953933303165659113674339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50635955535443772742449559 75953933303165659113674339)
        ·
          refine ⟨113930899954748488670511509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75953933303165659113674339 113930899954748488670511509)
          ·
            refine ⟨5340510935378835406430227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 113930899954748488670511509 5340510935378835406430227)
            ·
              refine ⟨8010766403068253109645341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5340510935378835406430227 8010766403068253109645341)
              ·
                refine ⟨3004037401150594916117003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8010766403068253109645341 3004037401150594916117003)
                ·
                  refine ⟨4506056101725892374175505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004037401150594916117003 4506056101725892374175505)
                  ·
                    refine ⟨3379542076294419280631629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4506056101725892374175505 3379542076294419280631629)
                    ·
                      refine ⟨1267328278610407230236861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3379542076294419280631629 1267328278610407230236861)
                      ·
                        rfl

theorem cell23_2468113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_2468113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468113 prefixEnd_2468113 := by exact prefixLift 2468113
  have htrace : WordTrace (prefixWord ++ tailWord_2468113) baseStart_2468113 baseEnd_2468113 := by
    simpa [prefixWord, tailWord_2468113, baseEnd_2468113] using wordTrace_append hprefix tailTrace_2468113
  have hstable : (prefixWord ++ tailWord_2468113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468113).length < 2 ^ (prefixWord ++ tailWord_2468113).sum := by decide
  have hdescent : baseEnd_2468113 < baseStart_2468113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468127 : List Nat := [1, 1, 2, 4, 3, 1, 2, 4, 1, 2, 2]
def baseStart_2468127 : Nat := 118140960795 + 2468127 * 2 ^ 59
def prefixEnd_2468127 : Nat := 4983230072969 + 3 ^ 40 * 2468127 * 2
def baseEnd_2468127 : Nat := 1267335467339570175461797

theorem tailTrace_2468127 : CollatzResearch.WordTrace tailWord_2468127 prefixEnd_2468127 1267335467339570175461797 := by
  unfold tailWord_2468127
  simp only [CollatzResearch.WordTrace]
  refine ⟨90019987129404876377586635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60013324752936584251724423 90019987129404876377586635)
  ·
    refine ⟨135029980694107314566379953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90019987129404876377586635 135029980694107314566379953)
    ·
      refine ⟨101272485520580485924784965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135029980694107314566379953 101272485520580485924784965)
      ·
        refine ⟨18988591035108841110897181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101272485520580485924784965 18988591035108841110897181)
        ·
          refine ⟨7120721638165815416586443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18988591035108841110897181 7120721638165815416586443)
          ·
            refine ⟨10681082457248723124879665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7120721638165815416586443 10681082457248723124879665)
            ·
              refine ⟨8010811842936542343659749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10681082457248723124879665 8010811842936542343659749)
              ·
                refine ⟨1502027220550601689436203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8010811842936542343659749 1502027220550601689436203)
                ·
                  refine ⟨2253040830825902534154305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502027220550601689436203 2253040830825902534154305)
                  ·
                    refine ⟨1689780623119426900615729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2253040830825902534154305 1689780623119426900615729)
                    ·
                      refine ⟨1267335467339570175461797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1689780623119426900615729 1267335467339570175461797)
                      ·
                        rfl

theorem cell23_2468127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_2468127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468127 prefixEnd_2468127 := by exact prefixLift 2468127
  have htrace : WordTrace (prefixWord ++ tailWord_2468127) baseStart_2468127 baseEnd_2468127 := by
    simpa [prefixWord, tailWord_2468127, baseEnd_2468127] using wordTrace_append hprefix tailTrace_2468127
  have hstable : (prefixWord ++ tailWord_2468127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468127).length < 2 ^ (prefixWord ++ tailWord_2468127).sum := by decide
  have hdescent : baseEnd_2468127 < baseStart_2468127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468129 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 1, 9]
def baseStart_2468129 : Nat := 118140960795 + 2468129 * 2 ^ 59
def prefixEnd_2468129 : Nat := 4983230072969 + 3 ^ 40 * 2468129 * 2
def baseEnd_2468129 : Nat := 422445498100293055878929

theorem tailTrace_2468129 : CollatzResearch.WordTrace tailWord_2468129 prefixEnd_2468129 422445498100293055878929 := by
  unfold tailWord_2468129
  simp only [CollatzResearch.WordTrace]
  refine ⟨90020060075397630719159441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60013373383598420479439627 90020060075397630719159441)
  ·
    refine ⟨67515045056548223039369581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90020060075397630719159441 67515045056548223039369581)
    ·
      refine ⟨25318141896205583639763593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67515045056548223039369581 25318141896205583639763593)
      ·
        refine ⟨18988606422154187729822695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25318141896205583639763593 18988606422154187729822695)
        ·
          refine ⟨28482909633231281594734043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18988606422154187729822695 28482909633231281594734043)
          ·
            refine ⟨42724364449846922392101065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28482909633231281594734043 42724364449846922392101065)
            ·
              refine ⟨32043273337385191794075799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42724364449846922392101065 32043273337385191794075799)
              ·
                refine ⟨48064910006077787691113699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32043273337385191794075799 48064910006077787691113699)
                ·
                  refine ⟨72097365009116681536670549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48064910006077787691113699 72097365009116681536670549)
                  ·
                    refine ⟨422445498100293055878929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 72097365009116681536670549 422445498100293055878929)
                    ·
                      rfl

theorem cell23_2468129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_2468129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468129 prefixEnd_2468129 := by exact prefixLift 2468129
  have htrace : WordTrace (prefixWord ++ tailWord_2468129) baseStart_2468129 baseEnd_2468129 := by
    simpa [prefixWord, tailWord_2468129, baseEnd_2468129] using wordTrace_append hprefix tailTrace_2468129
  have hstable : (prefixWord ++ tailWord_2468129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468129).length < 2 ^ (prefixWord ++ tailWord_2468129).sum := by decide
  have hdescent : baseEnd_2468129 < baseStart_2468129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468143 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 2, 1, 3]
def baseStart_2468143 : Nat := 118140960795 + 2468143 * 2 ^ 59
def prefixEnd_2468143 : Nat := 4983230072969 + 3 ^ 40 * 2468143 * 2
def baseEnd_2468143 : Nat := 1267343683030042112861723

theorem tailTrace_2468143 : CollatzResearch.WordTrace tailWord_2468143 prefixEnd_2468143 1267343683030042112861723 := by
  unfold tailWord_2468143
  simp only [CollatzResearch.WordTrace]
  refine ⟨90020570697346911110169083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60013713798231274073446055 90020570697346911110169083)
  ·
    refine ⟨135030856046020366665253625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90020570697346911110169083 135030856046020366665253625)
    ·
      refine ⟨101273142034515274998940219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135030856046020366665253625 101273142034515274998940219)
      ·
        refine ⟨151909713051772912498410329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101273142034515274998940219 151909713051772912498410329)
        ·
          refine ⟨113932284788829684373807747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151909713051772912498410329 113932284788829684373807747)
          ·
            refine ⟨170898427183244526560711621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113932284788829684373807747 170898427183244526560711621)
            ·
              refine ⟨32043455096858348730133429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170898427183244526560711621 32043455096858348730133429)
              ·
                refine ⟨3004073915330470193450009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32043455096858348730133429 3004073915330470193450009)
                ·
                  refine ⟨2253055436497852645087507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3004073915330470193450009 2253055436497852645087507)
                  ·
                    refine ⟨3379583154746778967631261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2253055436497852645087507 3379583154746778967631261)
                    ·
                      refine ⟨1267343683030042112861723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3379583154746778967631261 1267343683030042112861723)
                      ·
                        rfl

theorem cell23_2468143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 1, 3].length) (baseStart_2468143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468143 prefixEnd_2468143 := by exact prefixLift 2468143
  have htrace : WordTrace (prefixWord ++ tailWord_2468143) baseStart_2468143 baseEnd_2468143 := by
    simpa [prefixWord, tailWord_2468143, baseEnd_2468143] using wordTrace_append hprefix tailTrace_2468143
  have hstable : (prefixWord ++ tailWord_2468143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468143).length < 2 ^ (prefixWord ++ tailWord_2468143).sum := by decide
  have hdescent : baseEnd_2468143 < baseStart_2468143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468161 : List Nat := [1, 2, 5, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_2468161 : Nat := 118140960795 + 2468161 * 2 ^ 59
def prefixEnd_2468161 : Nat := 4983230072969 + 3 ^ 40 * 2468161 * 2
def baseEnd_2468161 : Nat := 1267352925681823042436641

theorem tailTrace_2468161 : CollatzResearch.WordTrace tailWord_2468161 prefixEnd_2468161 1267352925681823042436641 := by
  unfold tailWord_2468161
  simp only [CollatzResearch.WordTrace]
  refine ⟨90021227211281700184324337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60014151474187800122882891 90021227211281700184324337)
  ·
    refine ⟨67515920408461275138243253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90021227211281700184324337 67515920408461275138243253)
    ·
      refine ⟨6329617538293244544210305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67515920408461275138243253 6329617538293244544210305)
      ·
        refine ⟨4747213153719933408157729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6329617538293244544210305 4747213153719933408157729)
        ·
          refine ⟨3560409865289950056118297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4747213153719933408157729 3560409865289950056118297)
          ·
            refine ⟨2670307398967462542088723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3560409865289950056118297 2670307398967462542088723)
            ·
              refine ⟨4005461098451193813133085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670307398967462542088723 4005461098451193813133085)
              ·
                refine ⟨1502047911919197679924907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4005461098451193813133085 1502047911919197679924907)
                ·
                  refine ⟨2253071867878796519887361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502047911919197679924907 2253071867878796519887361)
                  ·
                    refine ⟨1689803900909097389915521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2253071867878796519887361 1689803900909097389915521)
                    ·
                      refine ⟨1267352925681823042436641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1689803900909097389915521 1267352925681823042436641)
                      ·
                        rfl

theorem cell23_2468161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_2468161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468161 prefixEnd_2468161 := by exact prefixLift 2468161
  have htrace : WordTrace (prefixWord ++ tailWord_2468161) baseStart_2468161 baseEnd_2468161 := by
    simpa [prefixWord, tailWord_2468161, baseEnd_2468161] using wordTrace_append hprefix tailTrace_2468161
  have hstable : (prefixWord ++ tailWord_2468161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468161).length < 2 ^ (prefixWord ++ tailWord_2468161).sum := by decide
  have hdescent : baseEnd_2468161 < baseStart_2468161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468179 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 6]
def baseStart_2468179 : Nat := 118140960795 + 2468179 * 2 ^ 59
def prefixEnd_2468179 : Nat := 4983230072969 + 3 ^ 40 * 2468179 * 2
def baseEnd_2468179 : Nat := 1267362168333603972011557

theorem tailTrace_2468179 : CollatzResearch.WordTrace tailWord_2468179 prefixEnd_2468179 1267362168333603972011557 := by
  unfold tailWord_2468179
  simp only [CollatzResearch.WordTrace]
  refine ⟨90021883725216489258479591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60014589150144326172319727 90021883725216489258479591)
  ·
    refine ⟨135032825587824733887719387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90021883725216489258479591 135032825587824733887719387)
    ·
      refine ⟨202549238381737100831579081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135032825587824733887719387 202549238381737100831579081)
      ·
        refine ⟨151911928786302825623684311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202549238381737100831579081 151911928786302825623684311)
        ·
          refine ⟨227867893179454238435526467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151911928786302825623684311 227867893179454238435526467)
          ·
            refine ⟨341801839769181357653289701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227867893179454238435526467 341801839769181357653289701)
            ·
              refine ⟨64087844956721504559991819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 341801839769181357653289701 64087844956721504559991819)
              ·
                refine ⟨96131767435082256839987729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64087844956721504559991819 96131767435082256839987729)
                ·
                  refine ⟨72098825576311692629990797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96131767435082256839987729 72098825576311692629990797)
                  ·
                    refine ⟨27037059591116884736246549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72098825576311692629990797 27037059591116884736246549)
                    ·
                      refine ⟨1267362168333603972011557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27037059591116884736246549 1267362168333603972011557)
                      ·
                        rfl

theorem cell23_2468179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_2468179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468179 prefixEnd_2468179 := by exact prefixLift 2468179
  have htrace : WordTrace (prefixWord ++ tailWord_2468179) baseStart_2468179 baseEnd_2468179 := by
    simpa [prefixWord, tailWord_2468179, baseEnd_2468179] using wordTrace_append hprefix tailTrace_2468179
  have hstable : (prefixWord ++ tailWord_2468179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468179).length < 2 ^ (prefixWord ++ tailWord_2468179).sum := by decide
  have hdescent : baseEnd_2468179 < baseStart_2468179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468186 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3]
def baseStart_2468186 : Nat := 118140960795 + 2468186 * 2 ^ 59
def prefixEnd_2468186 : Nat := 4983230072969 + 3 ^ 40 * 2468186 * 2
def baseEnd_2468186 : Nat := 1267365762698185444624025

theorem tailTrace_2468186 : CollatzResearch.WordTrace tailWord_2468186 prefixEnd_2468186 1267365762698185444624025 := by
  unfold tailWord_2468186
  simp only [CollatzResearch.WordTrace]
  refine ⟨22505534759047782363496103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60014759357460752969322941 22505534759047782363496103)
  ·
    refine ⟨33758302138571673545244155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22505534759047782363496103 33758302138571673545244155)
    ·
      refine ⟨50637453207857510317866233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33758302138571673545244155 50637453207857510317866233)
      ·
        refine ⟨37978089905893132738399675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50637453207857510317866233 37978089905893132738399675)
        ·
          refine ⟨56967134858839699107599513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37978089905893132738399675 56967134858839699107599513)
          ·
            refine ⟨42725351144129774330699635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56967134858839699107599513 42725351144129774330699635)
            ·
              refine ⟨64088026716194661496049453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42725351144129774330699635 64088026716194661496049453)
              ·
                refine ⟨24033010018572998061018545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64088026716194661496049453 24033010018572998061018545)
                ·
                  refine ⟨18024757513929748545763909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24033010018572998061018545 18024757513929748545763909)
                  ·
                    refine ⟨3379642033861827852330733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18024757513929748545763909 3379642033861827852330733)
                    ·
                      refine ⟨1267365762698185444624025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3379642033861827852330733 1267365762698185444624025)
                      ·
                        rfl

theorem cell23_2468186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_2468186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468186 prefixEnd_2468186 := by exact prefixLift 2468186
  have htrace : WordTrace (prefixWord ++ tailWord_2468186) baseStart_2468186 baseEnd_2468186 := by
    simpa [prefixWord, tailWord_2468186, baseEnd_2468186] using wordTrace_append hprefix tailTrace_2468186
  have hstable : (prefixWord ++ tailWord_2468186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468186).length < 2 ^ (prefixWord ++ tailWord_2468186).sum := by decide
  have hdescent : baseEnd_2468186 < baseStart_2468186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468194 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_2468194 : Nat := 118140960795 + 2468194 * 2 ^ 59
def prefixEnd_2468194 : Nat := 4983230072969 + 3 ^ 40 * 2468194 * 2
def baseEnd_2468194 : Nat := 1267369870543421413323989

theorem tailTrace_2468194 : CollatzResearch.WordTrace tailWord_2468194 prefixEnd_2468194 1267369870543421413323989 := by
  unfold tailWord_2468194
  simp only [CollatzResearch.WordTrace]
  refine ⟨22505607705040536705068909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60014953880108097880183757 22505607705040536705068909)
  ·
    refine ⟨8439602889390201264400841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22505607705040536705068909 8439602889390201264400841)
    ·
      refine ⟨6329702167042650948300631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8439602889390201264400841 6329702167042650948300631)
      ·
        refine ⟨9494553250563976422450947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6329702167042650948300631 9494553250563976422450947)
        ·
          refine ⟨14241829875845964633676421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9494553250563976422450947 14241829875845964633676421)
          ·
            refine ⟨2670343101721118368814329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14241829875845964633676421 2670343101721118368814329)
            ·
              refine ⟨2002757326290838776610747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2670343101721118368814329 2002757326290838776610747)
              ·
                refine ⟨3004135989436258164916121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002757326290838776610747 3004135989436258164916121)
                ·
                  refine ⟨2253101992077193623687091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3004135989436258164916121 2253101992077193623687091)
                  ·
                    refine ⟨3379652988115790435530637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2253101992077193623687091 3379652988115790435530637)
                    ·
                      refine ⟨1267369870543421413323989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3379652988115790435530637 1267369870543421413323989)
                      ·
                        rfl

theorem cell23_2468194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_2468194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468194 prefixEnd_2468194 := by exact prefixLift 2468194
  have htrace : WordTrace (prefixWord ++ tailWord_2468194) baseStart_2468194 baseEnd_2468194 := by
    simpa [prefixWord, tailWord_2468194, baseEnd_2468194] using wordTrace_append hprefix tailTrace_2468194
  have hstable : (prefixWord ++ tailWord_2468194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468194).length < 2 ^ (prefixWord ++ tailWord_2468194).sum := by decide
  have hdescent : baseEnd_2468194 < baseStart_2468194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468196 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_2468196 : Nat := 118140960795 + 2468196 * 2 ^ 59
def prefixEnd_2468196 : Nat := 4983230072969 + 3 ^ 40 * 2468196 * 2
def baseEnd_2468196 : Nat := 1267370897504730405498979

theorem tailTrace_2468196 : CollatzResearch.WordTrace tailWord_2468196 prefixEnd_2468196 1267370897504730405498979 := by
  unfold tailWord_2468196
  simp only [CollatzResearch.WordTrace]
  refine ⟨45011251883077450580924221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60015002510769934107898961 45011251883077450580924221)
  ·
    refine ⟨16879219456154043967846583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45011251883077450580924221 16879219456154043967846583)
    ·
      refine ⟨25318829184231065951769875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16879219456154043967846583 25318829184231065951769875)
      ·
        refine ⟨37978243776346598927654813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25318829184231065951769875 37978243776346598927654813)
        ·
          refine ⟨14241841416129974597870555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37978243776346598927654813 14241841416129974597870555)
          ·
            refine ⟨21362762124194961896805833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14241841416129974597870555 21362762124194961896805833)
            ·
              refine ⟨16022071593146221422604375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21362762124194961896805833 16022071593146221422604375)
              ·
                refine ⟨24033107389719332133906563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16022071593146221422604375 24033107389719332133906563)
                ·
                  refine ⟨36049661084578998200859845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24033107389719332133906563 36049661084578998200859845)
                  ·
                    refine ⟨6759311453358562162661221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36049661084578998200859845 6759311453358562162661221)
                    ·
                      refine ⟨1267370897504730405498979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6759311453358562162661221 1267370897504730405498979)
                      ·
                        rfl

theorem cell23_2468196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_2468196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468196 prefixEnd_2468196 := by exact prefixLift 2468196
  have htrace : WordTrace (prefixWord ++ tailWord_2468196) baseStart_2468196 baseEnd_2468196 := by
    simpa [prefixWord, tailWord_2468196, baseEnd_2468196] using wordTrace_append hprefix tailTrace_2468196
  have hstable : (prefixWord ++ tailWord_2468196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468196).length < 2 ^ (prefixWord ++ tailWord_2468196).sum := by decide
  have hdescent : baseEnd_2468196 < baseStart_2468196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468204 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 1, 3, 2]
def baseStart_2468204 : Nat := 118140960795 + 2468204 * 2 ^ 59
def prefixEnd_2468204 : Nat := 4983230072969 + 3 ^ 40 * 2468204 * 2
def baseEnd_2468204 : Nat := 1267375005349966374198943

theorem tailTrace_2468204 : CollatzResearch.WordTrace tailWord_2468204 prefixEnd_2468204 1267375005349966374198943 := by
  unfold tailWord_2468204
  simp only [CollatzResearch.WordTrace]
  refine ⟨45011397775062959264069833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60015197033417279018759777 45011397775062959264069833)
  ·
    refine ⟨33758548331297219448052375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45011397775062959264069833 33758548331297219448052375)
    ·
      refine ⟨50637822496945829172078563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33758548331297219448052375 50637822496945829172078563)
      ·
        refine ⟨75956733745418743758117845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50637822496945829172078563 75956733745418743758117845)
        ·
          refine ⟨1780235947158251806830887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 75956733745418743758117845 1780235947158251806830887)
          ·
            refine ⟨2670353920737377710246331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780235947158251806830887 2670353920737377710246331)
            ·
              refine ⟨4005530881106066565369497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670353920737377710246331 4005530881106066565369497)
              ·
                refine ⟨3004148160829549924027123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4005530881106066565369497 3004148160829549924027123)
                ·
                  refine ⟨4506222241244324886040685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004148160829549924027123 4506222241244324886040685)
                  ·
                    refine ⟨1689833340466621832265257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4506222241244324886040685 1689833340466621832265257)
                    ·
                      refine ⟨1267375005349966374198943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1689833340466621832265257 1267375005349966374198943)
                      ·
                        rfl

theorem cell23_2468204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 3, 2].length) (baseStart_2468204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468204 prefixEnd_2468204 := by exact prefixLift 2468204
  have htrace : WordTrace (prefixWord ++ tailWord_2468204) baseStart_2468204 baseEnd_2468204 := by
    simpa [prefixWord, tailWord_2468204, baseEnd_2468204] using wordTrace_append hprefix tailTrace_2468204
  have hstable : (prefixWord ++ tailWord_2468204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468204).length < 2 ^ (prefixWord ++ tailWord_2468204).sum := by decide
  have hdescent : baseEnd_2468204 < baseStart_2468204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468273 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2468273 : Nat := 118140960795 + 2468273 * 2 ^ 59
def prefixEnd_2468273 : Nat := 4983230072969 + 3 ^ 40 * 2468273 * 2
def baseEnd_2468273 : Nat := 1267410435515126604236125

theorem tailTrace_2468273 : CollatzResearch.WordTrace tailWord_2468273 prefixEnd_2468273 1267410435515126604236125 := by
  unfold tailWord_2468273
  simp only [CollatzResearch.WordTrace]
  refine ⟨90025312186875943312401473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60016874791250628874934315 90025312186875943312401473)
  ·
    refine ⟨67518984140156957484301105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90025312186875943312401473 67518984140156957484301105)
    ·
      refine ⟨50639238105117718113225829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67518984140156957484301105 50639238105117718113225829)
      ·
        refine ⟨9494857144709572146229843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50639238105117718113225829 9494857144709572146229843)
        ·
          refine ⟨14242285717064358219344765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9494857144709572146229843 14242285717064358219344765)
          ·
            refine ⟨5340857143899134332254287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14242285717064358219344765 5340857143899134332254287)
            ·
              refine ⟨8011285715848701498381431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5340857143899134332254287 8011285715848701498381431)
              ·
                refine ⟨12016928573773052247572147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8011285715848701498381431 12016928573773052247572147)
                ·
                  refine ⟨18025392860659578371358221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12016928573773052247572147 18025392860659578371358221)
                  ·
                    refine ⟨6759522322747341889259333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18025392860659578371358221 6759522322747341889259333)
                    ·
                      refine ⟨1267410435515126604236125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6759522322747341889259333 1267410435515126604236125)
                      ·
                        rfl

theorem cell23_2468273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2468273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468273 prefixEnd_2468273 := by exact prefixLift 2468273
  have htrace : WordTrace (prefixWord ++ tailWord_2468273) baseStart_2468273 baseEnd_2468273 := by
    simpa [prefixWord, tailWord_2468273, baseEnd_2468273] using wordTrace_append hprefix tailTrace_2468273
  have hstable : (prefixWord ++ tailWord_2468273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468273).length < 2 ^ (prefixWord ++ tailWord_2468273).sum := by decide
  have hdescent : baseEnd_2468273 < baseStart_2468273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468310 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_2468310 : Nat := 118140960795 + 2468310 * 2 ^ 59
def prefixEnd_2468310 : Nat := 4983230072969 + 3 ^ 40 * 2468310 * 2
def baseEnd_2468310 : Nat := 1267429434299342959473455

theorem tailTrace_2468310 : CollatzResearch.WordTrace tailWord_2468310 prefixEnd_2468310 1267429434299342959473455 := by
  unfold tailWord_2468310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5626666355483868664468649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60017774458494599087665589 5626666355483868664468649)
  ·
    refine ⟨4219999766612901498351487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5626666355483868664468649 4219999766612901498351487)
    ·
      refine ⟨6329999649919352247527231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4219999766612901498351487 6329999649919352247527231)
      ·
        refine ⟨9494999474879028371290847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6329999649919352247527231 9494999474879028371290847)
        ·
          refine ⟨14242499212318542556936271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9494999474879028371290847 14242499212318542556936271)
          ·
            refine ⟨21363748818477813835404407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14242499212318542556936271 21363748818477813835404407)
            ·
              refine ⟨32045623227716720753106611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21363748818477813835404407 32045623227716720753106611)
              ·
                refine ⟨48068434841575081129659917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32045623227716720753106611 48068434841575081129659917)
                ·
                  refine ⟨18025663065590655423622469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48068434841575081129659917 18025663065590655423622469)
                  ·
                    refine ⟨3379811824798247891929213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18025663065590655423622469 3379811824798247891929213)
                    ·
                      refine ⟨1267429434299342959473455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3379811824798247891929213 1267429434299342959473455)
                      ·
                        rfl

theorem cell23_2468310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_2468310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468310 prefixEnd_2468310 := by exact prefixLift 2468310
  have htrace : WordTrace (prefixWord ++ tailWord_2468310) baseStart_2468310 baseEnd_2468310 := by
    simpa [prefixWord, tailWord_2468310, baseEnd_2468310] using wordTrace_append hprefix tailTrace_2468310
  have hstable : (prefixWord ++ tailWord_2468310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468310).length < 2 ^ (prefixWord ++ tailWord_2468310).sum := by decide
  have hdescent : baseEnd_2468310 < baseStart_2468310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468334 : List Nat := [4, 1, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_2468334 : Nat := 118140960795 + 2468334 * 2 ^ 59
def prefixEnd_2468334 : Nat := 4983230072969 + 3 ^ 40 * 2468334 * 2
def baseEnd_2468334 : Nat := 422480585945016955191115

theorem tailTrace_2468334 : CollatzResearch.WordTrace tailWord_2468334 prefixEnd_2468334 422480585945016955191115 := by
  unfold tailWord_2468334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11253442129956868841296507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60018358026436633820248037 11253442129956868841296507)
  ·
    refine ⟨16880163194935303261944761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11253442129956868841296507 16880163194935303261944761)
    ·
      refine ⟨12660122396201477446458571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16880163194935303261944761 12660122396201477446458571)
      ·
        refine ⟨18990183594302216169687857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12660122396201477446458571 18990183594302216169687857)
        ·
          refine ⟨14242637695726662127265893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18990183594302216169687857 14242637695726662127265893)
          ·
            refine ⟨2670494567948749148862355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14242637695726662127265893 2670494567948749148862355)
            ·
              refine ⟨4005741851923123723293533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670494567948749148862355 4005741851923123723293533)
              ·
                refine ⟨1502153194471171396235075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4005741851923123723293533 1502153194471171396235075)
                ·
                  refine ⟨2253229791706757094352613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502153194471171396235075 2253229791706757094352613)
                  ·
                    refine ⟨422480585945016955191115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2253229791706757094352613 422480585945016955191115)
                    ·
                      rfl

theorem cell23_2468334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_2468334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468334 prefixEnd_2468334 := by exact prefixLift 2468334
  have htrace : WordTrace (prefixWord ++ tailWord_2468334) baseStart_2468334 baseEnd_2468334 := by
    simpa [prefixWord, tailWord_2468334, baseEnd_2468334] using wordTrace_append hprefix tailTrace_2468334
  have hstable : (prefixWord ++ tailWord_2468334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468334).length < 2 ^ (prefixWord ++ tailWord_2468334).sum := by decide
  have hdescent : baseEnd_2468334 < baseStart_2468334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468357 : List Nat := [1, 3, 1, 1, 2, 2, 2, 6, 1, 1, 3]
def baseStart_2468357 : Nat := 118140960795 + 2468357 * 2 ^ 59
def prefixEnd_2468357 : Nat := 4983230072969 + 3 ^ 40 * 2468357 * 2
def baseEnd_2468357 : Nat := 1267453567890104275585739

theorem tailTrace_2468357 : CollatzResearch.WordTrace tailWord_2468357 prefixEnd_2468357 1267453567890104275585739 := by
  unfold tailWord_2468357
  simp only [CollatzResearch.WordTrace]
  refine ⟨90028375918571625658459325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60018917279047750438972883 90028375918571625658459325)
  ·
    refine ⟨33760640969464359621922247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90028375918571625658459325 33760640969464359621922247)
    ·
      refine ⟨50640961454196539432883371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33760640969464359621922247 50640961454196539432883371)
      ·
        refine ⟨75961442181294809149325057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50640961454196539432883371 75961442181294809149325057)
        ·
          refine ⟨56971081635971106861993793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75961442181294809149325057 56971081635971106861993793)
          ·
            refine ⟨42728311226978330146495345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56971081635971106861993793 42728311226978330146495345)
            ·
              refine ⟨32046233420233747609871509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42728311226978330146495345 32046233420233747609871509)
              ·
                refine ⟨1502167191573456919212727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32046233420233747609871509 1502167191573456919212727)
                ·
                  refine ⟨2253250787360185378819091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502167191573456919212727 2253250787360185378819091)
                  ·
                    refine ⟨3379876181040278068228637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2253250787360185378819091 3379876181040278068228637)
                    ·
                      refine ⟨1267453567890104275585739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3379876181040278068228637 1267453567890104275585739)
                      ·
                        rfl

theorem cell23_2468357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 1, 1, 3].length) (baseStart_2468357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468357 prefixEnd_2468357 := by exact prefixLift 2468357
  have htrace : WordTrace (prefixWord ++ tailWord_2468357) baseStart_2468357 baseEnd_2468357 := by
    simpa [prefixWord, tailWord_2468357, baseEnd_2468357] using wordTrace_append hprefix tailTrace_2468357
  have hstable : (prefixWord ++ tailWord_2468357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468357).length < 2 ^ (prefixWord ++ tailWord_2468357).sum := by decide
  have hdescent : baseEnd_2468357 < baseStart_2468357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468373 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_2468373 : Nat := 118140960795 + 2468373 * 2 ^ 59
def prefixEnd_2468373 : Nat := 4983230072969 + 3 ^ 40 * 2468373 * 2
def baseEnd_2468373 : Nat := 422487261193525404328555

theorem tailTrace_2468373 : CollatzResearch.WordTrace tailWord_2468373 prefixEnd_2468373 422487261193525404328555 := by
  unfold tailWord_2468373
  simp only [CollatzResearch.WordTrace]
  refine ⟨90028959486513660391041773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60019306324342440260694515 90028959486513660391041773)
  ·
    refine ⟨33760859807442622646640665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90028959486513660391041773 33760859807442622646640665)
    ·
      refine ⟨25320644855581966984980499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33760859807442622646640665 25320644855581966984980499)
      ·
        refine ⟨37980967283372950477470749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25320644855581966984980499 37980967283372950477470749)
        ·
          refine ⟨14242862731264856429051531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37980967283372950477470749 14242862731264856429051531)
          ·
            refine ⟨21364294096897284643577297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14242862731264856429051531 21364294096897284643577297)
            ·
              refine ⟨16023220572672963482682973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21364294096897284643577297 16023220572672963482682973)
              ·
                refine ⟨6008707714752361306006115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16023220572672963482682973 6008707714752361306006115)
                ·
                  refine ⟨9013061572128541959009173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6008707714752361306006115 9013061572128541959009173)
                  ·
                    refine ⟨422487261193525404328555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9013061572128541959009173 422487261193525404328555)
                    ·
                      rfl

theorem cell23_2468373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_2468373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468373 prefixEnd_2468373 := by exact prefixLift 2468373
  have htrace : WordTrace (prefixWord ++ tailWord_2468373) baseStart_2468373 baseEnd_2468373 := by
    simpa [prefixWord, tailWord_2468373, baseEnd_2468373] using wordTrace_append hprefix tailTrace_2468373
  have hstable : (prefixWord ++ tailWord_2468373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468373).length < 2 ^ (prefixWord ++ tailWord_2468373).sum := by decide
  have hdescent : baseEnd_2468373 < baseStart_2468373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468380 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2468380 : Nat := 118140960795 + 2468380 * 2 ^ 59
def prefixEnd_2468380 : Nat := 4983230072969 + 3 ^ 40 * 2468380 * 2
def baseEnd_2468380 : Nat := 1267465377945157685598133

theorem tailTrace_2468380 : CollatzResearch.WordTrace tailWord_2468380 prefixEnd_2468380 1267465377945157685598133 := by
  unfold tailWord_2468380
  simp only [CollatzResearch.WordTrace]
  refine ⟨45014607398744150293273297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60019476531658867057697729 45014607398744150293273297)
  ·
    refine ⟨33760955549058112719954973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45014607398744150293273297 33760955549058112719954973)
    ·
      refine ⟨12660358330896792269983115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33760955549058112719954973 12660358330896792269983115)
      ·
        refine ⟨18990537496345188404974673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12660358330896792269983115 18990537496345188404974673)
        ·
          refine ⟨14242903122258891303731005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18990537496345188404974673 14242903122258891303731005)
          ·
            refine ⟨5341088670847084238899127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14242903122258891303731005 5341088670847084238899127)
            ·
              refine ⟨8011633006270626358348691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341088670847084238899127 8011633006270626358348691)
              ·
                refine ⟨12017449509405939537523037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8011633006270626358348691 12017449509405939537523037)
                ·
                  refine ⟨4506543566027227326571139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12017449509405939537523037 4506543566027227326571139)
                  ·
                    refine ⟨6759815349040840989856709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4506543566027227326571139 6759815349040840989856709)
                    ·
                      refine ⟨1267465377945157685598133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6759815349040840989856709 1267465377945157685598133)
                      ·
                        rfl

theorem cell23_2468380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2468380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468380 prefixEnd_2468380 := by exact prefixLift 2468380
  have htrace : WordTrace (prefixWord ++ tailWord_2468380) baseStart_2468380 baseEnd_2468380 := by
    simpa [prefixWord, tailWord_2468380, baseEnd_2468380] using wordTrace_append hprefix tailTrace_2468380
  have hstable : (prefixWord ++ tailWord_2468380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468380).length < 2 ^ (prefixWord ++ tailWord_2468380).sum := by decide
  have hdescent : baseEnd_2468380 < baseStart_2468380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468384 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2468384 : Nat := 118140960795 + 2468384 * 2 ^ 59
def prefixEnd_2468384 : Nat := 4983230072969 + 3 ^ 40 * 2468384 * 2
def baseEnd_2468384 : Nat := 1267467431867775669948115

theorem tailTrace_2468384 : CollatzResearch.WordTrace tailWord_2468384 prefixEnd_2468384 1267467431867775669948115 := by
  unfold tailWord_2468384
  simp only [CollatzResearch.WordTrace]
  refine ⟨45014680344736904634846103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60019573792982539513128137 45014680344736904634846103)
  ·
    refine ⟨67522020517105356952269155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45014680344736904634846103 67522020517105356952269155)
    ·
      refine ⟨101283030775658035428403733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67522020517105356952269155 101283030775658035428403733)
      ·
        refine ⟨4747642067608970410706425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 101283030775658035428403733 4747642067608970410706425)
        ·
          refine ⟨3560731550706727808029819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4747642067608970410706425 3560731550706727808029819)
          ·
            refine ⟨5341097326060091712044729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560731550706727808029819 5341097326060091712044729)
            ·
              refine ⟨4005822994545068784033547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5341097326060091712044729 4005822994545068784033547)
              ·
                refine ⟨6008734491817603176050321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4005822994545068784033547 6008734491817603176050321)
                ·
                  refine ⟨4506550868863202382037741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6008734491817603176050321 4506550868863202382037741)
                  ·
                    refine ⟨1689956575823700893264153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4506550868863202382037741 1689956575823700893264153)
                    ·
                      refine ⟨1267467431867775669948115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1689956575823700893264153 1267467431867775669948115)
                      ·
                        rfl

theorem cell23_2468384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2468384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468384 prefixEnd_2468384 := by exact prefixLift 2468384
  have htrace : WordTrace (prefixWord ++ tailWord_2468384) baseStart_2468384 baseEnd_2468384 := by
    simpa [prefixWord, tailWord_2468384, baseEnd_2468384] using wordTrace_append hprefix tailTrace_2468384
  have hstable : (prefixWord ++ tailWord_2468384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468384).length < 2 ^ (prefixWord ++ tailWord_2468384).sum := by decide
  have hdescent : baseEnd_2468384 < baseStart_2468384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468400 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 3]
def baseStart_2468400 : Nat := 118140960795 + 2468400 * 2 ^ 59
def prefixEnd_2468400 : Nat := 4983230072969 + 3 ^ 40 * 2468400 * 2
def baseEnd_2468400 : Nat := 1267475647558247607348041

theorem tailTrace_2468400 : CollatzResearch.WordTrace tailWord_2468400 prefixEnd_2468400 1267475647558247607348041 := by
  unfold tailWord_2468400
  simp only [CollatzResearch.WordTrace]
  refine ⟨45014972128707922001137327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60019962838277229334849769 45014972128707922001137327)
  ·
    refine ⟨67522458193061883001705991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45014972128707922001137327 67522458193061883001705991)
    ·
      refine ⟨101283687289592824502558987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67522458193061883001705991 101283687289592824502558987)
      ·
        refine ⟨151925530934389236753838481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101283687289592824502558987 151925530934389236753838481)
        ·
          refine ⟨113944148200791927565378861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151925530934389236753838481 113944148200791927565378861)
          ·
            refine ⟨42729055575296972837017073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113944148200791927565378861 42729055575296972837017073)
            ·
              refine ⟨32046791681472729627762805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42729055575296972837017073 32046791681472729627762805)
              ·
                refine ⟨3004386720138068402602763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32046791681472729627762805 3004386720138068402602763)
                ·
                  refine ⟨4506580080207102603904145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004386720138068402602763 4506580080207102603904145)
                  ·
                    refine ⟨3379935060155326952928109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4506580080207102603904145 3379935060155326952928109)
                    ·
                      refine ⟨1267475647558247607348041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3379935060155326952928109 1267475647558247607348041)
                      ·
                        rfl

theorem cell23_2468400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 3].length) (baseStart_2468400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468400 prefixEnd_2468400 := by exact prefixLift 2468400
  have htrace : WordTrace (prefixWord ++ tailWord_2468400) baseStart_2468400 baseEnd_2468400 := by
    simpa [prefixWord, tailWord_2468400, baseEnd_2468400] using wordTrace_append hprefix tailTrace_2468400
  have hstable : (prefixWord ++ tailWord_2468400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468400).length < 2 ^ (prefixWord ++ tailWord_2468400).sum := by decide
  have hdescent : baseEnd_2468400 < baseStart_2468400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468430 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_2468430 : Nat := 118140960795 + 2468430 * 2 ^ 59
def prefixEnd_2468430 : Nat := 4983230072969 + 3 ^ 40 * 2468430 * 2
def baseEnd_2468430 : Nat := 1267491051977882489972903

theorem tailTrace_2468430 : CollatzResearch.WordTrace tailWord_2468430 prefixEnd_2468430 1267491051977882489972903 := by
  unfold tailWord_2468430
  simp only [CollatzResearch.WordTrace]
  refine ⟨11253879805913394890733343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60020692298204772750577829 11253879805913394890733343)
  ·
    refine ⟨16880819708870092336100015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11253879805913394890733343 16880819708870092336100015)
    ·
      refine ⟨25321229563305138504150023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16880819708870092336100015 25321229563305138504150023)
      ·
        refine ⟨37981844344957707756225035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25321229563305138504150023 37981844344957707756225035)
        ·
          refine ⟨56972766517436561634337553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37981844344957707756225035 56972766517436561634337553)
          ·
            refine ⟨42729574888077421225753165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56972766517436561634337553 42729574888077421225753165)
            ·
              refine ⟨16023590583029032959657437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42729574888077421225753165 16023590583029032959657437)
              ·
                refine ⟨6008846468635887359871539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16023590583029032959657437 6008846468635887359871539)
                ·
                  refine ⟨9013269702953831039807309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6008846468635887359871539 9013269702953831039807309)
                  ·
                    refine ⟨3379976138607686639927741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9013269702953831039807309 3379976138607686639927741)
                    ·
                      refine ⟨1267491051977882489972903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3379976138607686639927741 1267491051977882489972903)
                      ·
                        rfl

theorem cell23_2468430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_2468430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468430 prefixEnd_2468430 := by exact prefixLift 2468430
  have htrace : WordTrace (prefixWord ++ tailWord_2468430) baseStart_2468430 baseEnd_2468430 := by
    simpa [prefixWord, tailWord_2468430, baseEnd_2468430] using wordTrace_append hprefix tailTrace_2468430
  have hstable : (prefixWord ++ tailWord_2468430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468430).length < 2 ^ (prefixWord ++ tailWord_2468430).sum := by decide
  have hdescent : baseEnd_2468430 < baseStart_2468430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468463 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 2, 6]
def baseStart_2468463 : Nat := 118140960795 + 2468463 * 2 ^ 59
def prefixEnd_2468463 : Nat := 4983230072969 + 3 ^ 40 * 2468463 * 2
def baseEnd_2468463 : Nat := 422502665613160286953417

theorem tailTrace_2468463 : CollatzResearch.WordTrace tailWord_2468463 prefixEnd_2468463 422502665613160286953417 := by
  unfold tailWord_2468463
  simp only [CollatzResearch.WordTrace]
  refine ⟨90032242056187605761818043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60021494704125070507878695 90032242056187605761818043)
  ·
    refine ⟨135048363084281408642727065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90032242056187605761818043 135048363084281408642727065)
    ·
      refine ⟨101286272313211056482045299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135048363084281408642727065 101286272313211056482045299)
      ·
        refine ⟨151929408469816584723067949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101286272313211056482045299 151929408469816584723067949)
        ·
          refine ⟨56973528176181219271150481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151929408469816584723067949 56973528176181219271150481)
          ·
            refine ⟨42730146132135914453362861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56973528176181219271150481 42730146132135914453362861)
            ·
              refine ⟨16023804799550967920011073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42730146132135914453362861 16023804799550967920011073)
              ·
                refine ⟨12017853599663225940008305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16023804799550967920011073 12017853599663225940008305)
                ·
                  refine ⟨9013390199747419455006229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12017853599663225940008305 9013390199747419455006229)
                  ·
                    refine ⟨422502665613160286953417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9013390199747419455006229 422502665613160286953417)
                    ·
                      rfl

theorem cell23_2468463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_2468463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468463 prefixEnd_2468463 := by exact prefixLift 2468463
  have htrace : WordTrace (prefixWord ++ tailWord_2468463) baseStart_2468463 baseEnd_2468463 := by
    simpa [prefixWord, tailWord_2468463, baseEnd_2468463] using wordTrace_append hprefix tailTrace_2468463
  have hstable : (prefixWord ++ tailWord_2468463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468463).length < 2 ^ (prefixWord ++ tailWord_2468463).sum := by decide
  have hdescent : baseEnd_2468463 < baseStart_2468463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468540 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_2468540 : Nat := 118140960795 + 2468540 * 2 ^ 59
def prefixEnd_2468540 : Nat := 4983230072969 + 3 ^ 40 * 2468540 * 2
def baseEnd_2468540 : Nat := 422515844949959019865799

theorem tailTrace_2468540 : CollatzResearch.WordTrace tailWord_2468540 prefixEnd_2468540 422515844949959019865799 := by
  unfold tailWord_2468540
  simp only [CollatzResearch.WordTrace]
  refine ⟨45017525238454323956185537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60023366984605765274914049 45017525238454323956185537)
  ·
    refine ⟨33763143928840742967139153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45017525238454323956185537 33763143928840742967139153)
    ·
      refine ⟨25322357946630557225354365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33763143928840742967139153 25322357946630557225354365)
      ·
        refine ⟨9495884229986458959507887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25322357946630557225354365 9495884229986458959507887)
        ·
          refine ⟨14243826344979688439261831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9495884229986458959507887 14243826344979688439261831)
          ·
            refine ⟨21365739517469532658892747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14243826344979688439261831 21365739517469532658892747)
            ·
              refine ⟨32048609276204298988339121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21365739517469532658892747 32048609276204298988339121)
              ·
                refine ⟨24036456957153224241254341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32048609276204298988339121 24036456957153224241254341)
                ·
                  refine ⟨4506835679466229545235189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24036456957153224241254341 4506835679466229545235189)
                  ·
                    refine ⟨422515844949959019865799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4506835679466229545235189 422515844949959019865799)
                    ·
                      rfl

theorem cell23_2468540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_2468540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468540 prefixEnd_2468540 := by exact prefixLift 2468540
  have htrace : WordTrace (prefixWord ++ tailWord_2468540) baseStart_2468540 baseEnd_2468540 := by
    simpa [prefixWord, tailWord_2468540, baseEnd_2468540] using wordTrace_append hprefix tailTrace_2468540
  have hstable : (prefixWord ++ tailWord_2468540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468540).length < 2 ^ (prefixWord ++ tailWord_2468540).sum := by decide
  have hdescent : baseEnd_2468540 < baseStart_2468540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468577 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_2468577 : Nat := 118140960795 + 2468577 * 2 ^ 59
def prefixEnd_2468577 : Nat := 4983230072969 + 3 ^ 40 * 2468577 * 2
def baseEnd_2468577 : Nat := 1267566533634093414834727

theorem tailTrace_2468577 : CollatzResearch.WordTrace tailWord_2468577 prefixEnd_2468577 1267566533634093414834727 := by
  unfold tailWord_2468577
  simp only [CollatzResearch.WordTrace]
  refine ⟨90036399977774603231467985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60024266651849735487645323 90036399977774603231467985)
  ·
    refine ⟨67527299983330952423600989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90036399977774603231467985 67527299983330952423600989)
    ·
      refine ⟨25322737493749107158850371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67527299983330952423600989 25322737493749107158850371)
      ·
        refine ⟨37984106240623660738275557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25322737493749107158850371 37984106240623660738275557)
        ·
          refine ⟨7122019920116936388426667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37984106240623660738275557 7122019920116936388426667)
          ·
            refine ⟨10683029880175404582640001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7122019920116936388426667 10683029880175404582640001)
            ·
              refine ⟨8012272410131553436980001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10683029880175404582640001 8012272410131553436980001)
              ·
                refine ⟨6009204307598665077735001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8012272410131553436980001 6009204307598665077735001)
                ·
                  refine ⟨4506903230698998808301251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6009204307598665077735001 4506903230698998808301251)
                  ·
                    refine ⟨6760354846048498212451877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4506903230698998808301251 6760354846048498212451877)
                    ·
                      refine ⟨1267566533634093414834727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6760354846048498212451877 1267566533634093414834727)
                      ·
                        rfl

theorem cell23_2468577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_2468577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468577 prefixEnd_2468577 := by exact prefixLift 2468577
  have htrace : WordTrace (prefixWord ++ tailWord_2468577) baseStart_2468577 baseEnd_2468577 := by
    simpa [prefixWord, tailWord_2468577, baseEnd_2468577] using wordTrace_append hprefix tailTrace_2468577
  have hstable : (prefixWord ++ tailWord_2468577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468577).length < 2 ^ (prefixWord ++ tailWord_2468577).sum := by decide
  have hdescent : baseEnd_2468577 < baseStart_2468577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468594 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 2, 4, 2]
def baseStart_2468594 : Nat := 118140960795 + 2468594 * 2 ^ 59
def prefixEnd_2468594 : Nat := 4983230072969 + 3 ^ 40 * 2468594 * 2
def baseEnd_2468594 : Nat := 1267575262805219848322149

theorem tailTrace_2468594 : CollatzResearch.WordTrace tailWord_2468594 prefixEnd_2468594 1267575262805219848322149 := by
  unfold tailWord_2468594
  simp only [CollatzResearch.WordTrace]
  refine ⟨22509255004678253783709209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60024680012475343423224557 22509255004678253783709209)
  ·
    refine ⟨16881941253508690337781907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22509255004678253783709209 16881941253508690337781907)
    ·
      refine ⟨25322911880263035506672861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16881941253508690337781907 25322911880263035506672861)
      ·
        refine ⟨9496091955098638315002323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25322911880263035506672861 9496091955098638315002323)
        ·
          refine ⟨14244137932647957472503485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9496091955098638315002323 14244137932647957472503485)
          ·
            refine ⟨5341551724742984052188807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14244137932647957472503485 5341551724742984052188807)
            ·
              refine ⟨8012327587114476078283211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341551724742984052188807 8012327587114476078283211)
              ·
                refine ⟨12018491380671714117424817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8012327587114476078283211 12018491380671714117424817)
                ·
                  refine ⟨9013868535503785588068613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12018491380671714117424817 9013868535503785588068613)
                  ·
                    refine ⟨1690100350406959797762865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9013868535503785588068613 1690100350406959797762865)
                    ·
                      refine ⟨1267575262805219848322149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1690100350406959797762865 1267575262805219848322149)
                      ·
                        rfl

theorem cell23_2468594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_2468594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468594 prefixEnd_2468594 := by exact prefixLift 2468594
  have htrace : WordTrace (prefixWord ++ tailWord_2468594) baseStart_2468594 baseEnd_2468594 := by
    simpa [prefixWord, tailWord_2468594, baseEnd_2468594] using wordTrace_append hprefix tailTrace_2468594
  have hstable : (prefixWord ++ tailWord_2468594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468594).length < 2 ^ (prefixWord ++ tailWord_2468594).sum := by decide
  have hdescent : baseEnd_2468594 < baseStart_2468594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468600 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 6]
def baseStart_2468600 : Nat := 118140960795 + 2468600 * 2 ^ 59
def prefixEnd_2468600 : Nat := 4983230072969 + 3 ^ 40 * 2468600 * 2
def baseEnd_2468600 : Nat := 140842038187682980538569

theorem tailTrace_2468600 : CollatzResearch.WordTrace tailWord_2468600 prefixEnd_2468600 140842038187682980538569 := by
  unfold tailWord_2468600
  simp only [CollatzResearch.WordTrace]
  refine ⟨45018619428345639079777627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60024825904460852106370169 45018619428345639079777627)
  ·
    refine ⟨67527929142518458619666441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45018619428345639079777627 67527929142518458619666441)
    ·
      refine ⟨50645946856888843964749831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67527929142518458619666441 50645946856888843964749831)
      ·
        refine ⟨75968920285333265947124747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50645946856888843964749831 75968920285333265947124747)
        ·
          refine ⟨113953380427999898920687121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75968920285333265947124747 113953380427999898920687121)
          ·
            refine ⟨85465035320999924190515341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113953380427999898920687121 85465035320999924190515341)
            ·
              refine ⟨32049388245374971571443253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85465035320999924190515341 32049388245374971571443253)
              ·
                refine ⟨3004630148003903584822805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32049388245374971571443253 3004630148003903584822805)
                ·
                  refine ⟨140842038187682980538569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3004630148003903584822805 140842038187682980538569)
                  ·
                    rfl

theorem cell23_2468600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 6].length) (baseStart_2468600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468600 prefixEnd_2468600 := by exact prefixLift 2468600
  have htrace : WordTrace (prefixWord ++ tailWord_2468600) baseStart_2468600 baseEnd_2468600 := by
    simpa [prefixWord, tailWord_2468600, baseEnd_2468600] using wordTrace_append hprefix tailTrace_2468600
  have hstable : (prefixWord ++ tailWord_2468600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468600).length < 2 ^ (prefixWord ++ tailWord_2468600).sum := by decide
  have hdescent : baseEnd_2468600 < baseStart_2468600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468627 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 5, 1, 3]
def baseStart_2468627 : Nat := 118140960795 + 2468627 * 2 ^ 59
def prefixEnd_2468627 : Nat := 4983230072969 + 3 ^ 40 * 2468627 * 2
def baseEnd_2468627 : Nat := 1267592207666818219209497

theorem tailTrace_2468627 : CollatzResearch.WordTrace tailWord_2468627 prefixEnd_2468627 1267592207666818219209497 := by
  unfold tailWord_2468627
  simp only [CollatzResearch.WordTrace]
  refine ⟨90038223627593461770788135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60025482418395641180525423 90038223627593461770788135)
  ·
    refine ⟨135057335441390192656182203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90038223627593461770788135 135057335441390192656182203)
    ·
      refine ⟨202586003162085288984273305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135057335441390192656182203 202586003162085288984273305)
      ·
        refine ⟨151939502371563966738204979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202586003162085288984273305 151939502371563966738204979)
        ·
          refine ⟨227909253557345950107307469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151939502371563966738204979 227909253557345950107307469)
          ·
            refine ⟨85465970084004731290240301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227909253557345950107307469 85465970084004731290240301)
            ·
              refine ⟨32049738781501774233840113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85465970084004731290240301 32049738781501774233840113)
              ·
                refine ⟨24037304086126330675380085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32049738781501774233840113 24037304086126330675380085)
                ·
                  refine ⟨2253497258074343500816883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24037304086126330675380085 2253497258074343500816883)
                  ·
                    refine ⟨3380245887111515251225325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2253497258074343500816883 3380245887111515251225325)
                    ·
                      refine ⟨1267592207666818219209497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3380245887111515251225325 1267592207666818219209497)
                      ·
                        rfl

theorem cell23_2468627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 1, 3].length) (baseStart_2468627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468627 prefixEnd_2468627 := by exact prefixLift 2468627
  have htrace : WordTrace (prefixWord ++ tailWord_2468627) baseStart_2468627 baseEnd_2468627 := by
    simpa [prefixWord, tailWord_2468627, baseEnd_2468627] using wordTrace_append hprefix tailTrace_2468627
  have hstable : (prefixWord ++ tailWord_2468627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468627).length < 2 ^ (prefixWord ++ tailWord_2468627).sum := by decide
  have hdescent : baseEnd_2468627 < baseStart_2468627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468684 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2468684 : Nat := 118140960795 + 2468684 * 2 ^ 59
def prefixEnd_2468684 : Nat := 4983230072969 + 3 ^ 40 * 2468684 * 2
def baseEnd_2468684 : Nat := 1267621476064124496196735

theorem tailTrace_2468684 : CollatzResearch.WordTrace tailWord_2468684 prefixEnd_2468684 1267621476064124496196735 := by
  unfold tailWord_2468684
  simp only [CollatzResearch.WordTrace]
  refine ⟨45020151294193480252806553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60026868392257973670408737 45020151294193480252806553)
  ·
    refine ⟨33765113470645110189604915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45020151294193480252806553 33765113470645110189604915)
    ·
      refine ⟨50647670205967665284407373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33765113470645110189604915 50647670205967665284407373)
      ·
        refine ⟨18992876327237874481652765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50647670205967665284407373 18992876327237874481652765)
        ·
          refine ⟨7122328622714202930619787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18992876327237874481652765 7122328622714202930619787)
          ·
            refine ⟨10683492934071304395929681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7122328622714202930619787 10683492934071304395929681)
            ·
              refine ⟨8012619700553478296947261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10683492934071304395929681 8012619700553478296947261)
              ·
                refine ⟨3004732387707554361355223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8012619700553478296947261 3004732387707554361355223)
                ·
                  refine ⟨4507098581561331542032835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004732387707554361355223 4507098581561331542032835)
                  ·
                    refine ⟨6760647872341997313049253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4507098581561331542032835 6760647872341997313049253)
                    ·
                      refine ⟨1267621476064124496196735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6760647872341997313049253 1267621476064124496196735)
                      ·
                        rfl

theorem cell23_2468684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2468684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468684 prefixEnd_2468684 := by exact prefixLift 2468684
  have htrace : WordTrace (prefixWord ++ tailWord_2468684) baseStart_2468684 baseEnd_2468684 := by
    simpa [prefixWord, tailWord_2468684, baseEnd_2468684] using wordTrace_append hprefix tailTrace_2468684
  have hstable : (prefixWord ++ tailWord_2468684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468684).length < 2 ^ (prefixWord ++ tailWord_2468684).sum := by decide
  have hdescent : baseEnd_2468684 < baseStart_2468684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468707 : List Nat := [1, 1, 1, 5, 3, 2, 2, 8]
def baseStart_2468707 : Nat := 118140960795 + 2468707 * 2 ^ 59
def prefixEnd_2468707 : Nat := 4983230072969 + 3 ^ 40 * 2468707 * 2
def baseEnd_2468707 : Nat := 46949380967376959489227

theorem tailTrace_2468707 : CollatzResearch.WordTrace tailWord_2468707 prefixEnd_2468707 46949380967376959489227 := by
  unfold tailWord_2468707
  simp only [CollatzResearch.WordTrace]
  refine ⟨90041141467303635433700375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60027427644869090289133583 90041141467303635433700375)
  ·
    refine ⟨135061712200955453150550563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90041141467303635433700375 135061712200955453150550563)
    ·
      refine ⟨202592568301433179725825845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135061712200955453150550563 202592568301433179725825845)
      ·
        refine ⟨18993053278259360599296173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202592568301433179725825845 18993053278259360599296173)
        ·
          refine ⟨7122394979347260224736065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18993053278259360599296173 7122394979347260224736065)
          ·
            refine ⟨5341796234510445168552049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7122394979347260224736065 5341796234510445168552049)
            ·
              refine ⟨4006347175882833876414037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5341796234510445168552049 4006347175882833876414037)
              ·
                refine ⟨46949380967376959489227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4006347175882833876414037 46949380967376959489227)
                ·
                  rfl

theorem cell23_2468707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 8].length) (baseStart_2468707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468707 prefixEnd_2468707 := by exact prefixLift 2468707
  have htrace : WordTrace (prefixWord ++ tailWord_2468707) baseStart_2468707 baseEnd_2468707 := by
    simpa [prefixWord, tailWord_2468707, baseEnd_2468707] using wordTrace_append hprefix tailTrace_2468707
  have hstable : (prefixWord ++ tailWord_2468707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468707).length < 2 ^ (prefixWord ++ tailWord_2468707).sum := by decide
  have hdescent : baseEnd_2468707 < baseStart_2468707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468711 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 2, 4]
def baseStart_2468711 : Nat := 118140960795 + 2468711 * 2 ^ 59
def prefixEnd_2468711 : Nat := 4983230072969 + 3 ^ 40 * 2468711 * 2
def baseEnd_2468711 : Nat := 422545113347265296853037

theorem tailTrace_2468711 : CollatzResearch.WordTrace tailWord_2468711 prefixEnd_2468711 422545113347265296853037 := by
  unfold tailWord_2468711
  simp only [CollatzResearch.WordTrace]
  refine ⟨90041287359289144116845987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60027524906192762744563991 90041287359289144116845987)
  ·
    refine ⟨135061931038933716175268981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90041287359289144116845987 135061931038933716175268981)
    ·
      refine ⟨12662056034900035891431467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135061931038933716175268981 12662056034900035891431467)
      ·
        refine ⟨18993084052350053837147201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12662056034900035891431467 18993084052350053837147201)
        ·
          refine ⟨14244813039262540377860401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18993084052350053837147201 14244813039262540377860401)
          ·
            refine ⟨10683609779446905283395301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14244813039262540377860401 10683609779446905283395301)
            ·
              refine ⟨2003176833646294740636619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10683609779446905283395301 2003176833646294740636619)
              ·
                refine ⟨3004765250469442110954929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003176833646294740636619 3004765250469442110954929)
                ·
                  refine ⟨2253573937852081583216197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3004765250469442110954929 2253573937852081583216197)
                  ·
                    refine ⟨422545113347265296853037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2253573937852081583216197 422545113347265296853037)
                    ·
                      rfl

theorem cell23_2468711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_2468711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468711 prefixEnd_2468711 := by exact prefixLift 2468711
  have htrace : WordTrace (prefixWord ++ tailWord_2468711) baseStart_2468711 baseEnd_2468711 := by
    simpa [prefixWord, tailWord_2468711, baseEnd_2468711] using wordTrace_append hprefix tailTrace_2468711
  have hstable : (prefixWord ++ tailWord_2468711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468711).length < 2 ^ (prefixWord ++ tailWord_2468711).sum := by decide
  have hdescent : baseEnd_2468711 < baseStart_2468711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468718 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2468718 : Nat := 118140960795 + 2468718 * 2 ^ 59
def prefixEnd_2468718 : Nat := 4983230072969 + 3 ^ 40 * 2468718 * 2
def baseEnd_2468718 : Nat := 1267638934406377363171579

theorem tailTrace_2468718 : CollatzResearch.WordTrace tailWord_2468718 prefixEnd_2468718 1267638934406377363171579 := by
  unfold tailWord_2468718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255192833782973039043851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60027695113509189541567205 11255192833782973039043851)
  ·
    refine ⟨16882789250674459558565777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11255192833782973039043851 16882789250674459558565777)
    ·
      refine ⟨12662091938005844668924333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16882789250674459558565777 12662091938005844668924333)
      ·
        refine ⟨4748284476752191750846625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12662091938005844668924333 4748284476752191750846625)
        ·
          refine ⟨3561213357564143813134969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4748284476752191750846625 3561213357564143813134969)
          ·
            refine ⟨2670910018173107859851227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3561213357564143813134969 2670910018173107859851227)
            ·
              refine ⟨4006365027259661789776841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670910018173107859851227 4006365027259661789776841)
              ·
                refine ⟨3004773770444746342332631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4006365027259661789776841 3004773770444746342332631)
                ·
                  refine ⟨4507160655667119513498947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004773770444746342332631 4507160655667119513498947)
                  ·
                    refine ⟨6760740983500679270248421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4507160655667119513498947 6760740983500679270248421)
                    ·
                      refine ⟨1267638934406377363171579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6760740983500679270248421 1267638934406377363171579)
                      ·
                        rfl

theorem cell23_2468718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2468718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468718 prefixEnd_2468718 := by exact prefixLift 2468718
  have htrace : WordTrace (prefixWord ++ tailWord_2468718) baseStart_2468718 baseEnd_2468718 := by
    simpa [prefixWord, tailWord_2468718, baseEnd_2468718] using wordTrace_append hprefix tailTrace_2468718
  have hstable : (prefixWord ++ tailWord_2468718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468718).length < 2 ^ (prefixWord ++ tailWord_2468718).sum := by decide
  have hdescent : baseEnd_2468718 < baseStart_2468718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468721 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 1, 2, 3]
def baseStart_2468721 : Nat := 118140960795 + 2468721 * 2 ^ 59
def prefixEnd_2468721 : Nat := 4983230072969 + 3 ^ 40 * 2468721 * 2
def baseEnd_2468721 : Nat := 1267640474848340851434065

theorem tailTrace_2468721 : CollatzResearch.WordTrace tailWord_2468721 prefixEnd_2468721 1267640474848340851434065 := by
  unfold tailWord_2468721
  simp only [CollatzResearch.WordTrace]
  refine ⟨90041652089252915824710017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60027768059501943883140011 90041652089252915824710017)
  ·
    refine ⟨67531239066939686868532513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90041652089252915824710017 67531239066939686868532513)
    ·
      refine ⟨50648429300204765151399385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67531239066939686868532513 50648429300204765151399385)
      ·
        refine ⟨37986321975153573863549539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50648429300204765151399385 37986321975153573863549539)
        ·
          refine ⟨56979482962730360795324309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37986321975153573863549539 56979482962730360795324309)
          ·
            refine ⟨2670913263877985662280827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56979482962730360795324309 2670913263877985662280827)
            ·
              refine ⟨4006369895816978493421241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670913263877985662280827 4006369895816978493421241)
              ·
                refine ⟨3004777421862733870065931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4006369895816978493421241 3004777421862733870065931)
                ·
                  refine ⟨4507166132794100805098897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004777421862733870065931 4507166132794100805098897)
                  ·
                    refine ⟨3380374599595575603824173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4507166132794100805098897 3380374599595575603824173)
                    ·
                      refine ⟨1267640474848340851434065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3380374599595575603824173 1267640474848340851434065)
                      ·
                        rfl

theorem cell23_2468721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_2468721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468721 prefixEnd_2468721 := by exact prefixLift 2468721
  have htrace : WordTrace (prefixWord ++ tailWord_2468721) baseStart_2468721 baseEnd_2468721 := by
    simpa [prefixWord, tailWord_2468721, baseEnd_2468721] using wordTrace_append hprefix tailTrace_2468721
  have hstable : (prefixWord ++ tailWord_2468721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468721).length < 2 ^ (prefixWord ++ tailWord_2468721).sum := by decide
  have hdescent : baseEnd_2468721 < baseStart_2468721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468757 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_2468757 : Nat := 118140960795 + 2468757 * 2 ^ 59
def prefixEnd_2468757 : Nat := 4983230072969 + 3 ^ 40 * 2468757 * 2
def baseEnd_2468757 : Nat := 1267658960151902710583899

theorem tailTrace_2468757 : CollatzResearch.WordTrace tailWord_2468757 prefixEnd_2468757 1267658960151902710583899 := by
  unfold tailWord_2468757
  simp only [CollatzResearch.WordTrace]
  refine ⟨90042965117122493973020525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60028643411414995982013683 90042965117122493973020525)
  ·
    refine ⟨33766111918920935239882697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90042965117122493973020525 33766111918920935239882697)
    ·
      refine ⟨25324583939190701429912023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33766111918920935239882697 25324583939190701429912023)
      ·
        refine ⟨37986875908786052144868035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25324583939190701429912023 37986875908786052144868035)
        ·
          refine ⟨56980313863179078217302053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37986875908786052144868035 56980313863179078217302053)
          ·
            refine ⟨10683808849346077165744135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56980313863179078217302053 10683808849346077165744135)
            ·
              refine ⟨16025713274019115748616203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10683808849346077165744135 16025713274019115748616203)
              ·
                refine ⟨24038569911028673622924305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16025713274019115748616203 24038569911028673622924305)
                ·
                  refine ⟨18028927433271505217193229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24038569911028673622924305 18028927433271505217193229)
                  ·
                    refine ⟨6760847787476814456447461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18028927433271505217193229 6760847787476814456447461)
                    ·
                      refine ⟨1267658960151902710583899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6760847787476814456447461 1267658960151902710583899)
                      ·
                        rfl

theorem cell23_2468757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_2468757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468757 prefixEnd_2468757 := by exact prefixLift 2468757
  have htrace : WordTrace (prefixWord ++ tailWord_2468757) baseStart_2468757 baseEnd_2468757 := by
    simpa [prefixWord, tailWord_2468757, baseEnd_2468757] using wordTrace_append hprefix tailTrace_2468757
  have hstable : (prefixWord ++ tailWord_2468757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468757).length < 2 ^ (prefixWord ++ tailWord_2468757).sum := by decide
  have hdescent : baseEnd_2468757 < baseStart_2468757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468758 : List Nat := [5, 3, 1, 1, 1, 3, 1, 8]
def baseStart_2468758 : Nat := 118140960795 + 2468758 * 2 ^ 59
def prefixEnd_2468758 : Nat := 4983230072969 + 3 ^ 40 * 2468758 * 2
def baseEnd_2468758 : Nat := 46950350875279896543385

theorem tailTrace_2468758 : CollatzResearch.WordTrace tailWord_2468758 prefixEnd_2468758 46950350875279896543385 := by
  unfold tailWord_2468758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627687599382429446487933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60028667726745914095871285 5627687599382429446487933)
  ·
    refine ⟨2110382849768411042432975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5627687599382429446487933 2110382849768411042432975)
    ·
      refine ⟨3165574274652616563649463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2110382849768411042432975 3165574274652616563649463)
      ·
        refine ⟨4748361411978924845474195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3165574274652616563649463 4748361411978924845474195)
        ·
          refine ⟨7122542117968387268211293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4748361411978924845474195 7122542117968387268211293)
          ·
            refine ⟨2670953294238145225579235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7122542117968387268211293 2670953294238145225579235)
            ·
              refine ⟨4006429941357217838368853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670953294238145225579235 4006429941357217838368853)
              ·
                refine ⟨46950350875279896543385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4006429941357217838368853 46950350875279896543385)
                ·
                  rfl

theorem cell23_2468758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_2468758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468758 prefixEnd_2468758 := by exact prefixLift 2468758
  have htrace : WordTrace (prefixWord ++ tailWord_2468758) baseStart_2468758 baseEnd_2468758 := by
    simpa [prefixWord, tailWord_2468758, baseEnd_2468758] using wordTrace_append hprefix tailTrace_2468758
  have hstable : (prefixWord ++ tailWord_2468758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468758).length < 2 ^ (prefixWord ++ tailWord_2468758).sum := by decide
  have hdescent : baseEnd_2468758 < baseStart_2468758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468767 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 1, 8]
def baseStart_2468767 : Nat := 118140960795 + 2468767 * 2 ^ 59
def prefixEnd_2468767 : Nat := 4983230072969 + 3 ^ 40 * 2468767 * 2
def baseEnd_2468767 : Nat := 422554698319482557152951

theorem tailTrace_2468767 : CollatzResearch.WordTrace tailWord_2468767 prefixEnd_2468767 422554698319482557152951 := by
  unfold tailWord_2468767
  simp only [CollatzResearch.WordTrace]
  refine ⟨90043329847086265680884555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60028886564724177120589703 90043329847086265680884555)
  ·
    refine ⟨135064994770629398521326833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90043329847086265680884555 135064994770629398521326833)
    ·
      refine ⟨101298746077972048890995125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135064994770629398521326833 101298746077972048890995125)
      ·
        refine ⟨9496757444809879583530793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101298746077972048890995125 9496757444809879583530793)
        ·
          refine ⟨7122568083607409687648095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9496757444809879583530793 7122568083607409687648095)
          ·
            refine ⟨10683852125411114531472143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7122568083607409687648095 10683852125411114531472143)
            ·
              refine ⟨16025778188116671797208215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10683852125411114531472143 16025778188116671797208215)
              ·
                refine ⟨24038667282175007695812323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16025778188116671797208215 24038667282175007695812323)
                ·
                  refine ⟨36058000923262511543718485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24038667282175007695812323 36058000923262511543718485)
                  ·
                    refine ⟨422554698319482557152951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36058000923262511543718485 422554698319482557152951)
                    ·
                      rfl

theorem cell23_2468767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_2468767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468767 prefixEnd_2468767 := by exact prefixLift 2468767
  have htrace : WordTrace (prefixWord ++ tailWord_2468767) baseStart_2468767 baseEnd_2468767 := by
    simpa [prefixWord, tailWord_2468767, baseEnd_2468767] using wordTrace_append hprefix tailTrace_2468767
  have hstable : (prefixWord ++ tailWord_2468767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468767).length < 2 ^ (prefixWord ++ tailWord_2468767).sum := by decide
  have hdescent : baseEnd_2468767 < baseStart_2468767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468777 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 2, 4, 3]
def baseStart_2468777 : Nat := 118140960795 + 2468777 * 2 ^ 59
def prefixEnd_2468777 : Nat := 4983230072969 + 3 ^ 40 * 2468777 * 2
def baseEnd_2468777 : Nat := 1267669229764992632333807

theorem tailTrace_2468777 : CollatzResearch.WordTrace tailWord_2468777 prefixEnd_2468777 1267669229764992632333807 := by
  unfold tailWord_2468777
  simp only [CollatzResearch.WordTrace]
  refine ⟨90043694577050037388748585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60029129718033358259165723 90043694577050037388748585)
  ·
    refine ⟨67532770932787528041561439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90043694577050037388748585 67532770932787528041561439)
    ·
      refine ⟨101299156399181292062342159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67532770932787528041561439 101299156399181292062342159)
      ·
        refine ⟨151948734598771938093513239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101299156399181292062342159 151948734598771938093513239)
        ·
          refine ⟨227923101898157907140269859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151948734598771938093513239 227923101898157907140269859)
          ·
            refine ⟨341884652847236860710404789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227923101898157907140269859 341884652847236860710404789)
            ·
              refine ⟨32051686204428455691600449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 341884652847236860710404789 32051686204428455691600449)
              ·
                refine ⟨24038764653321341768700337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32051686204428455691600449 24038764653321341768700337)
                ·
                  refine ⟨18029073489991006326525253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24038764653321341768700337 18029073489991006326525253)
                  ·
                    refine ⟨3380451279373313686223485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18029073489991006326525253 3380451279373313686223485)
                    ·
                      refine ⟨1267669229764992632333807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3380451279373313686223485 1267669229764992632333807)
                      ·
                        rfl

theorem cell23_2468777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4, 3].length) (baseStart_2468777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468777 prefixEnd_2468777 := by exact prefixLift 2468777
  have htrace : WordTrace (prefixWord ++ tailWord_2468777) baseStart_2468777 baseEnd_2468777 := by
    simpa [prefixWord, tailWord_2468777, baseEnd_2468777] using wordTrace_append hprefix tailTrace_2468777
  have hstable : (prefixWord ++ tailWord_2468777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468777).length < 2 ^ (prefixWord ++ tailWord_2468777).sum := by decide
  have hdescent : baseEnd_2468777 < baseStart_2468777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468808 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 4, 2, 2]
def baseStart_2468808 : Nat := 118140960795 + 2468808 * 2 ^ 59
def prefixEnd_2468808 : Nat := 4983230072969 + 3 ^ 40 * 2468808 * 2
def baseEnd_2468808 : Nat := 1267685147665282011046165

theorem tailTrace_2468808 : CollatzResearch.WordTrace tailWord_2468808 prefixEnd_2468808 1267685147665282011046165 := by
  unfold tailWord_2468808
  simp only [CollatzResearch.WordTrace]
  refine ⟨45022412619968864841563539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60029883493291819788751385 45022412619968864841563539)
  ·
    refine ⟨67533618929953297262345309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45022412619968864841563539 67533618929953297262345309)
    ·
      refine ⟨25325107098732486473379491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67533618929953297262345309 25325107098732486473379491)
      ·
        refine ⟨37987660648098729710069237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25325107098732486473379491 37987660648098729710069237)
        ·
          refine ⟨3561343185759255910318991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37987660648098729710069237 3561343185759255910318991)
          ·
            refine ⟨5342014778638883865478487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561343185759255910318991 5342014778638883865478487)
            ·
              refine ⟨8013022167958325798217731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5342014778638883865478487 8013022167958325798217731)
              ·
                refine ⟨12019533251937488697326597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8013022167958325798217731 12019533251937488697326597)
                ·
                  refine ⟨2253662484738279130748737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12019533251937488697326597 2253662484738279130748737)
                  ·
                    refine ⟨1690246863553709348061553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2253662484738279130748737 1690246863553709348061553)
                    ·
                      refine ⟨1267685147665282011046165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1690246863553709348061553 1267685147665282011046165)
                      ·
                        rfl

theorem cell23_2468808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_2468808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468808 prefixEnd_2468808 := by exact prefixLift 2468808
  have htrace : WordTrace (prefixWord ++ tailWord_2468808) baseStart_2468808 baseEnd_2468808 := by
    simpa [prefixWord, tailWord_2468808, baseEnd_2468808] using wordTrace_append hprefix tailTrace_2468808
  have hstable : (prefixWord ++ tailWord_2468808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468808).length < 2 ^ (prefixWord ++ tailWord_2468808).sum := by decide
  have hdescent : baseEnd_2468808 < baseStart_2468808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468814 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_2468814 : Nat := 118140960795 + 2468814 * 2 ^ 59
def prefixEnd_2468814 : Nat := 4983230072969 + 3 ^ 40 * 2468814 * 2
def baseEnd_2468814 : Nat := 140854247616578776396793

theorem tailTrace_2468814 : CollatzResearch.WordTrace tailWord_2468814 prefixEnd_2468814 140854247616578776396793 := by
  unfold tailWord_2468814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255630509739499088480687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60030029385277328471896997 11255630509739499088480687)
  ·
    refine ⟨16883445764609248632721031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11255630509739499088480687 16883445764609248632721031)
    ·
      refine ⟨25325168646913872949081547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16883445764609248632721031 25325168646913872949081547)
      ·
        refine ⟨37987752970370809423622321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25325168646913872949081547 37987752970370809423622321)
        ·
          refine ⟨28490814727778107067716741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37987752970370809423622321 28490814727778107067716741)
          ·
            refine ⟨5342027761458395075196889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28490814727778107067716741 5342027761458395075196889)
            ·
              refine ⟨4006520821093796306397667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5342027761458395075196889 4006520821093796306397667)
              ·
                refine ⟨6009781231640694459596501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006520821093796306397667 6009781231640694459596501)
                ·
                  refine ⟨140854247616578776396793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6009781231640694459596501 140854247616578776396793)
                  ·
                    rfl

theorem cell23_2468814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_2468814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468814 prefixEnd_2468814 := by exact prefixLift 2468814
  have htrace : WordTrace (prefixWord ++ tailWord_2468814) baseStart_2468814 baseEnd_2468814 := by
    simpa [prefixWord, tailWord_2468814, baseEnd_2468814] using wordTrace_append hprefix tailTrace_2468814
  have hstable : (prefixWord ++ tailWord_2468814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468814).length < 2 ^ (prefixWord ++ tailWord_2468814).sum := by decide
  have hdescent : baseEnd_2468814 < baseStart_2468814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468824 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 2, 3, 3]
def baseStart_2468824 : Nat := 118140960795 + 2468824 * 2 ^ 59
def prefixEnd_2468824 : Nat := 4983230072969 + 3 ^ 40 * 2468824 * 2
def baseEnd_2468824 : Nat := 1267693363355753948446091

theorem tailTrace_2468824 : CollatzResearch.WordTrace tailWord_2468824 prefixEnd_2468824 1267693363355753948446091 := by
  unfold tailWord_2468824
  simp only [CollatzResearch.WordTrace]
  refine ⟨45022704403939882207854763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60030272538586509610473017 45022704403939882207854763)
  ·
    refine ⟨67534056605909823311782145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45022704403939882207854763 67534056605909823311782145)
    ·
      refine ⟨50650542454432367483836609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67534056605909823311782145 50650542454432367483836609)
      ·
        refine ⟨37987906840824275612877457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50650542454432367483836609 37987906840824275612877457)
        ·
          refine ⟨28490930130618206709658093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37987906840824275612877457 28490930130618206709658093)
          ·
            refine ⟨10684098798981827516121785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28490930130618206709658093 10684098798981827516121785)
            ·
              refine ⟨8013074099236370637091339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10684098798981827516121785 8013074099236370637091339)
              ·
                refine ⟨12019611148854555955637009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8013074099236370637091339 12019611148854555955637009)
                ·
                  refine ⟨9014708361640916966727757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12019611148854555955637009 9014708361640916966727757)
                  ·
                    refine ⟨3380515635615343862522909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9014708361640916966727757 3380515635615343862522909)
                    ·
                      refine ⟨1267693363355753948446091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3380515635615343862522909 1267693363355753948446091)
                      ·
                        rfl

theorem cell23_2468824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_2468824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468824 prefixEnd_2468824 := by exact prefixLift 2468824
  have htrace : WordTrace (prefixWord ++ tailWord_2468824) baseStart_2468824 baseEnd_2468824 := by
    simpa [prefixWord, tailWord_2468824, baseEnd_2468824] using wordTrace_append hprefix tailTrace_2468824
  have hstable : (prefixWord ++ tailWord_2468824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468824).length < 2 ^ (prefixWord ++ tailWord_2468824).sum := by decide
  have hdescent : baseEnd_2468824 < baseStart_2468824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468825 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 2, 2, 2]
def baseStart_2468825 : Nat := 118140960795 + 2468825 * 2 ^ 59
def prefixEnd_2468825 : Nat := 4983230072969 + 3 ^ 40 * 2468825 * 2
def baseEnd_2468825 : Nat := 1267693876836408444533587

theorem tailTrace_2468825 : CollatzResearch.WordTrace tailWord_2468825 prefixEnd_2468825 1267693876836408444533587 := by
  unfold tailWord_2468825
  simp only [CollatzResearch.WordTrace]
  refine ⟨90045445280876141586495929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60030296853917427724330619 90045445280876141586495929)
  ·
    refine ⟨67534083960657106189871947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90045445280876141586495929 67534083960657106189871947)
    ·
      refine ⟨101301125940985659284807921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67534083960657106189871947 101301125940985659284807921)
      ·
        refine ⟨75975844455739244463605941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101301125940985659284807921 75975844455739244463605941)
        ·
          refine ⟨7122735417725554168463057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75975844455739244463605941 7122735417725554168463057)
          ·
            refine ⟨5342051563294165626347293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7122735417725554168463057 5342051563294165626347293)
            ·
              refine ⟨2003269336235312109880235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5342051563294165626347293 2003269336235312109880235)
              ·
                refine ⟨3004904004352968164820353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003269336235312109880235 3004904004352968164820353)
                ·
                  refine ⟨2253678003264726123615265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3004904004352968164820353 2253678003264726123615265)
                  ·
                    refine ⟨1690258502448544592711449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2253678003264726123615265 1690258502448544592711449)
                    ·
                      refine ⟨1267693876836408444533587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1690258502448544592711449 1267693876836408444533587)
                      ·
                        rfl

theorem cell23_2468825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 2, 2, 2].length) (baseStart_2468825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468825 prefixEnd_2468825 := by exact prefixLift 2468825
  have htrace : WordTrace (prefixWord ++ tailWord_2468825) baseStart_2468825 baseEnd_2468825 := by
    simpa [prefixWord, tailWord_2468825, baseEnd_2468825] using wordTrace_append hprefix tailTrace_2468825
  have hstable : (prefixWord ++ tailWord_2468825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468825).length < 2 ^ (prefixWord ++ tailWord_2468825).sum := by decide
  have hdescent : baseEnd_2468825 < baseStart_2468825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468901 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 2, 2, 3]
def baseStart_2468901 : Nat := 118140960795 + 2468901 * 2 ^ 59
def prefixEnd_2468901 : Nat := 4983230072969 + 3 ^ 40 * 2468901 * 2
def baseEnd_2468901 : Nat := 1267732901366150147183237

theorem tailTrace_2468901 : CollatzResearch.WordTrace tailWord_2468901 prefixEnd_2468901 1267732901366150147183237 := by
  unfold tailWord_2468901
  simp only [CollatzResearch.WordTrace]
  refine ⟨90048217228600806566262557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60032144819067204377508371 90048217228600806566262557)
  ·
    refine ⟨33768081460725302462348459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90048217228600806566262557 33768081460725302462348459)
    ·
      refine ⟨50652122191087953693522689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33768081460725302462348459 50652122191087953693522689)
      ·
        refine ⟨37989091643315965270142017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50652122191087953693522689 37989091643315965270142017)
        ·
          refine ⟨28491818732486973952606513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37989091643315965270142017 28491818732486973952606513)
          ·
            refine ⟨21368864049365230464454885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28491818732486973952606513 21368864049365230464454885)
            ·
              refine ⟨4006662009255980712085291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21368864049365230464454885 4006662009255980712085291)
              ·
                refine ⟨6009993013883971068127937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006662009255980712085291 6009993013883971068127937)
                ·
                  refine ⟨4507494760412978301095953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6009993013883971068127937 4507494760412978301095953)
                  ·
                    refine ⟨3380621070309733725821965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4507494760412978301095953 3380621070309733725821965)
                    ·
                      refine ⟨1267732901366150147183237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3380621070309733725821965 1267732901366150147183237)
                      ·
                        rfl

theorem cell23_2468901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_2468901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468901 prefixEnd_2468901 := by exact prefixLift 2468901
  have htrace : WordTrace (prefixWord ++ tailWord_2468901) baseStart_2468901 baseEnd_2468901 := by
    simpa [prefixWord, tailWord_2468901, baseEnd_2468901] using wordTrace_append hprefix tailTrace_2468901
  have hstable : (prefixWord ++ tailWord_2468901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468901).length < 2 ^ (prefixWord ++ tailWord_2468901).sum := by decide
  have hdescent : baseEnd_2468901 < baseStart_2468901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468918 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2468918 : Nat := 118140960795 + 2468918 * 2 ^ 59
def prefixEnd_2468918 : Nat := 4983230072969 + 3 ^ 40 * 2468918 * 2
def baseEnd_2468918 : Nat := 1267741630537276580670659

theorem tailTrace_2468918 : CollatzResearch.WordTrace tailWord_2468918 prefixEnd_2468918 1267741630537276580670659 := by
  unfold tailWord_2468918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5628052329346201154351963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60032558179692812313087605 5628052329346201154351963)
  ·
    refine ⟨8442078494019301731527945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5628052329346201154351963 8442078494019301731527945)
    ·
      refine ⟨6331558870514476298645959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8442078494019301731527945 6331558870514476298645959)
      ·
        refine ⟨9497338305771714447968939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6331558870514476298645959 9497338305771714447968939)
        ·
          refine ⟨14246007458657571671953409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9497338305771714447968939 14246007458657571671953409)
          ·
            refine ⟨10684505593993178753965057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14246007458657571671953409 10684505593993178753965057)
            ·
              refine ⟨8013379195494884065473793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10684505593993178753965057 8013379195494884065473793)
              ·
                refine ⟨6010034396621163049105345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8013379195494884065473793 6010034396621163049105345)
                ·
                  refine ⟨4507525797465872286829009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6010034396621163049105345 4507525797465872286829009)
                  ·
                    refine ⟨3380644348099404215121757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4507525797465872286829009 3380644348099404215121757)
                    ·
                      refine ⟨1267741630537276580670659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3380644348099404215121757 1267741630537276580670659)
                      ·
                        rfl

theorem cell23_2468918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2468918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468918 prefixEnd_2468918 := by exact prefixLift 2468918
  have htrace : WordTrace (prefixWord ++ tailWord_2468918) baseStart_2468918 baseEnd_2468918 := by
    simpa [prefixWord, tailWord_2468918, baseEnd_2468918] using wordTrace_append hprefix tailTrace_2468918
  have hstable : (prefixWord ++ tailWord_2468918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468918).length < 2 ^ (prefixWord ++ tailWord_2468918).sum := by decide
  have hdescent : baseEnd_2468918 < baseStart_2468918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468921 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 6]
def baseStart_2468921 : Nat := 118140960795 + 2468921 * 2 ^ 59
def prefixEnd_2468921 : Nat := 4983230072969 + 3 ^ 40 * 2468921 * 2
def baseEnd_2468921 : Nat := 140860352331026674325905

theorem tailTrace_2468921 : CollatzResearch.WordTrace tailWord_2468921 prefixEnd_2468921 140860352331026674325905 := by
  unfold tailWord_2468921
  simp only [CollatzResearch.WordTrace]
  refine ⟨90048946688528349981990617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60032631125685566654660411 90048946688528349981990617)
  ·
    refine ⟨67536710016396262486492963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90048946688528349981990617 67536710016396262486492963)
    ·
      refine ⟨101305065024594393729739445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67536710016396262486492963 101305065024594393729739445)
      ·
        refine ⟨9497349846055724412163073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101305065024594393729739445 9497349846055724412163073)
        ·
          refine ⟨7123012384541793309122305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9497349846055724412163073 7123012384541793309122305)
          ·
            refine ⟨5342259288406344981841729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7123012384541793309122305 5342259288406344981841729)
            ·
              refine ⟨4006694466304758736381297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5342259288406344981841729 4006694466304758736381297)
              ·
                refine ⟨3005020849728569052285973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4006694466304758736381297 3005020849728569052285973)
                ·
                  refine ⟨140860352331026674325905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3005020849728569052285973 140860352331026674325905)
                  ·
                    rfl

theorem cell23_2468921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 6].length) (baseStart_2468921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468921 prefixEnd_2468921 := by exact prefixLift 2468921
  have htrace : WordTrace (prefixWord ++ tailWord_2468921) baseStart_2468921 baseEnd_2468921 := by
    simpa [prefixWord, tailWord_2468921, baseEnd_2468921] using wordTrace_append hprefix tailTrace_2468921
  have hstable : (prefixWord ++ tailWord_2468921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468921).length < 2 ^ (prefixWord ++ tailWord_2468921).sum := by decide
  have hdescent : baseEnd_2468921 < baseStart_2468921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468925 : List Nat := [1, 4, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_2468925 : Nat := 118140960795 + 2468925 * 2 ^ 59
def prefixEnd_2468925 : Nat := 4983230072969 + 3 ^ 40 * 2468925 * 2
def baseEnd_2468925 : Nat := 422581741633952684427709

theorem tailTrace_2468925 : CollatzResearch.WordTrace tailWord_2468925 prefixEnd_2468925 422581741633952684427709 := by
  unfold tailWord_2468925
  simp only [CollatzResearch.WordTrace]
  refine ⟨90049092580513858665136229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60032728387009239110090819 90049092580513858665136229)
  ·
    refine ⟨16884204858846348499713043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90049092580513858665136229 16884204858846348499713043)
    ·
      refine ⟨25326307288269522749569565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16884204858846348499713043 25326307288269522749569565)
      ·
        refine ⟨9497365233101071031088587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25326307288269522749569565 9497365233101071031088587)
        ·
          refine ⟨14246047849651606546632881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9497365233101071031088587 14246047849651606546632881)
          ·
            refine ⟨10684535887238704909974661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14246047849651606546632881 10684535887238704909974661)
            ·
              refine ⟨2003350478857257170620249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10684535887238704909974661 2003350478857257170620249)
              ·
                refine ⟨1502512859142942877965187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003350478857257170620249 1502512859142942877965187)
                ·
                  refine ⟨2253769288714414316947781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502512859142942877965187 2253769288714414316947781)
                  ·
                    refine ⟨422581741633952684427709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2253769288714414316947781 422581741633952684427709)
                    ·
                      rfl

theorem cell23_2468925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_2468925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468925 prefixEnd_2468925 := by exact prefixLift 2468925
  have htrace : WordTrace (prefixWord ++ tailWord_2468925) baseStart_2468925 baseEnd_2468925 := by
    simpa [prefixWord, tailWord_2468925, baseEnd_2468925] using wordTrace_append hprefix tailTrace_2468925
  have hstable : (prefixWord ++ tailWord_2468925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468925).length < 2 ^ (prefixWord ++ tailWord_2468925).sum := by decide
  have hdescent : baseEnd_2468925 < baseStart_2468925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468931 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 3, 1, 3]
def baseStart_2468931 : Nat := 118140960795 + 2468931 * 2 ^ 59
def prefixEnd_2468931 : Nat := 4983230072969 + 3 ^ 40 * 2468931 * 2
def baseEnd_2468931 : Nat := 1267748305785785029808099

theorem tailTrace_2468931 : CollatzResearch.WordTrace tailWord_2468931 prefixEnd_2468931 1267748305785785029808099 := by
  unfold tailWord_2468931
  simp only [CollatzResearch.WordTrace]
  refine ⟨90049311418492121689854647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60032874278994747793236431 90049311418492121689854647)
  ·
    refine ⟨135073967127738182534781971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90049311418492121689854647 135073967127738182534781971)
    ·
      refine ⟨202610950691607273802172957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135073967127738182534781971 202610950691607273802172957)
      ·
        refine ⟨75979106509352727675814859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202610950691607273802172957 75979106509352727675814859)
        ·
          refine ⟨113968659764029091513722289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75979106509352727675814859 113968659764029091513722289)
          ·
            refine ⟨85476494823021818635291717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113968659764029091513722289 85476494823021818635291717)
            ·
              refine ⟨16026842779316590994117197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85476494823021818635291717 16026842779316590994117197)
              ·
                refine ⟨6010066042243721622793949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16026842779316590994117197 6010066042243721622793949)
                ·
                  refine ⟨2253774765841395608547731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6010066042243721622793949 2253774765841395608547731)
                  ·
                    refine ⟨3380662148762093412821597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2253774765841395608547731 3380662148762093412821597)
                    ·
                      refine ⟨1267748305785785029808099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3380662148762093412821597 1267748305785785029808099)
                      ·
                        rfl

theorem cell23_2468931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_2468931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468931 prefixEnd_2468931 := by exact prefixLift 2468931
  have htrace : WordTrace (prefixWord ++ tailWord_2468931) baseStart_2468931 baseEnd_2468931 := by
    simpa [prefixWord, tailWord_2468931, baseEnd_2468931] using wordTrace_append hprefix tailTrace_2468931
  have hstable : (prefixWord ++ tailWord_2468931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468931).length < 2 ^ (prefixWord ++ tailWord_2468931).sum := by decide
  have hdescent : baseEnd_2468931 < baseStart_2468931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468965 : List Nat := [1, 3, 1, 3, 2, 1, 4, 3, 1, 1, 3]
def baseStart_2468965 : Nat := 118140960795 + 2468965 * 2 ^ 59
def prefixEnd_2468965 : Nat := 4983230072969 + 3 ^ 40 * 2468965 * 2
def baseEnd_2468965 : Nat := 1267765764128037896782943

theorem tailTrace_2468965 : CollatzResearch.WordTrace tailWord_2468965 prefixEnd_2468965 1267765764128037896782943 := by
  unfold tailWord_2468965
  simp only [CollatzResearch.WordTrace]
  refine ⟨90050551500368945496592349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60033701000245963664394899 90050551500368945496592349)
  ·
    refine ⟨33768956812638354561222131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90050551500368945496592349 33768956812638354561222131)
    ·
      refine ⟨50653435218957531841833197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33768956812638354561222131 50653435218957531841833197)
      ·
        refine ⟨18995038207109074440687449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50653435218957531841833197 18995038207109074440687449)
        ·
          refine ⟨14246278655331805830515587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18995038207109074440687449 14246278655331805830515587)
          ·
            refine ⟨21369417982997708745773381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14246278655331805830515587 21369417982997708745773381)
            ·
              refine ⟨4006765871812070389832509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21369417982997708745773381 4006765871812070389832509)
              ·
                refine ⟨1502537201929526396187191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4006765871812070389832509 1502537201929526396187191)
                ·
                  refine ⟨2253805802894289594280787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502537201929526396187191 2253805802894289594280787)
                  ·
                    refine ⟨3380708704341434391421181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2253805802894289594280787 3380708704341434391421181)
                    ·
                      refine ⟨1267765764128037896782943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3380708704341434391421181 1267765764128037896782943)
                      ·
                        rfl

theorem cell23_2468965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_2468965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468965 prefixEnd_2468965 := by exact prefixLift 2468965
  have htrace : WordTrace (prefixWord ++ tailWord_2468965) baseStart_2468965 baseEnd_2468965 := by
    simpa [prefixWord, tailWord_2468965, baseEnd_2468965] using wordTrace_append hprefix tailTrace_2468965
  have hstable : (prefixWord ++ tailWord_2468965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468965).length < 2 ^ (prefixWord ++ tailWord_2468965).sum := by decide
  have hdescent : baseEnd_2468965 < baseStart_2468965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468984 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_2468984 : Nat := 118140960795 + 2468984 * 2 ^ 59
def prefixEnd_2468984 : Nat := 4983230072969 + 3 ^ 40 * 2468984 * 2
def baseEnd_2468984 : Nat := 1267775520260473322445355

theorem tailTrace_2468984 : CollatzResearch.WordTrace tailWord_2468984 prefixEnd_2468984 1267775520260473322445355 := by
  unfold tailWord_2468984
  simp only [CollatzResearch.WordTrace]
  refine ⟨45025622243650055870767003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60034162991533407827689337 45025622243650055870767003)
  ·
    refine ⟨67538433365475083806150505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45025622243650055870767003 67538433365475083806150505)
    ·
      refine ⟨50653825024106312854612879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67538433365475083806150505 50653825024106312854612879)
      ·
        refine ⟨75980737536159469281919319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50653825024106312854612879 75980737536159469281919319)
        ·
          refine ⟨113971106304239203922878979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75980737536159469281919319 113971106304239203922878979)
          ·
            refine ⟨170956659456358805884318469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113971106304239203922878979 170956659456358805884318469)
            ·
              refine ⟨32054373648067276103309713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170956659456358805884318469 32054373648067276103309713)
              ·
                refine ⟨24040780236050457077482285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32054373648067276103309713 24040780236050457077482285)
                ·
                  refine ⟨9015292588518921404055857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24040780236050457077482285 9015292588518921404055857)
                  ·
                    refine ⟨6761469441389191053041893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9015292588518921404055857 6761469441389191053041893)
                    ·
                      refine ⟨1267775520260473322445355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6761469441389191053041893 1267775520260473322445355)
                      ·
                        rfl

theorem cell23_2468984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_2468984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2468984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2468984 prefixEnd_2468984 := by exact prefixLift 2468984
  have htrace : WordTrace (prefixWord ++ tailWord_2468984) baseStart_2468984 baseEnd_2468984 := by
    simpa [prefixWord, tailWord_2468984, baseEnd_2468984] using wordTrace_append hprefix tailTrace_2468984
  have hstable : (prefixWord ++ tailWord_2468984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468984).length < 2 ^ (prefixWord ++ tailWord_2468984).sum := by decide
  have hdescent : baseEnd_2468984 < baseStart_2468984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469001 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 4]
def baseStart_2469001 : Nat := 118140960795 + 2469001 * 2 ^ 59
def prefixEnd_2469001 : Nat := 4983230072969 + 3 ^ 40 * 2469001 * 2
def baseEnd_2469001 : Nat := 1267784249431599755932777

theorem tailTrace_2469001 : CollatzResearch.WordTrace tailWord_2469001 prefixEnd_2469001 1267784249431599755932777 := by
  unfold tailWord_2469001
  simp only [CollatzResearch.WordTrace]
  refine ⟨90051864528238523644902857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60034576352159015763268571 90051864528238523644902857)
  ·
    refine ⟨67538898396178892733677143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90051864528238523644902857 67538898396178892733677143)
    ·
      refine ⟨101308347594268339100515715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67538898396178892733677143 101308347594268339100515715)
      ·
        refine ⟨151962521391402508650773573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101308347594268339100515715 151962521391402508650773573)
        ·
          refine ⟨28492972760887970372020045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151962521391402508650773573 28492972760887970372020045)
          ·
            refine ⟨10684864785332988889507517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28492972760887970372020045 10684864785332988889507517)
            ·
              refine ⟨4006824294499870833565319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10684864785332988889507517 4006824294499870833565319)
              ·
                refine ⟨6010236441749806250347979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006824294499870833565319 6010236441749806250347979)
                ·
                  refine ⟨9015354662624709375521969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6010236441749806250347979 9015354662624709375521969)
                  ·
                    refine ⟨6761515996968532031641477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9015354662624709375521969 6761515996968532031641477)
                    ·
                      refine ⟨1267784249431599755932777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6761515996968532031641477 1267784249431599755932777)
                      ·
                        rfl

theorem cell23_2469001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 4].length) (baseStart_2469001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469001 prefixEnd_2469001 := by exact prefixLift 2469001
  have htrace : WordTrace (prefixWord ++ tailWord_2469001) baseStart_2469001 baseEnd_2469001 := by
    simpa [prefixWord, tailWord_2469001, baseEnd_2469001] using wordTrace_append hprefix tailTrace_2469001
  have hstable : (prefixWord ++ tailWord_2469001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469001).length < 2 ^ (prefixWord ++ tailWord_2469001).sum := by decide
  have hdescent : baseEnd_2469001 < baseStart_2469001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469021 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_2469021 : Nat := 118140960795 + 2469021 * 2 ^ 59
def prefixEnd_2469021 : Nat := 4983230072969 + 3 ^ 40 * 2469021 * 2
def baseEnd_2469021 : Nat := 1267794519044689677682685

theorem tailTrace_2469021 : CollatzResearch.WordTrace tailWord_2469021 prefixEnd_2469021 1267794519044689677682685 := by
  unfold tailWord_2469021
  simp only [CollatzResearch.WordTrace]
  refine ⟨90052593988166067060630917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60035062658777378040420611 90052593988166067060630917)
  ·
    refine ⟨16884861372781137573868297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90052593988166067060630917 16884861372781137573868297)
    ·
      refine ⟨12663646029585853180401223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16884861372781137573868297 12663646029585853180401223)
      ·
        refine ⟨18995469044378779770601835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12663646029585853180401223 18995469044378779770601835)
        ·
          refine ⟨28493203566568169655902753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18995469044378779770601835 28493203566568169655902753)
          ·
            refine ⟨21369902674926127241927065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28493203566568169655902753 21369902674926127241927065)
            ·
              refine ⟨16027427006194595431445299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21369902674926127241927065 16027427006194595431445299)
              ·
                refine ⟨24041140509291893147167949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16027427006194595431445299 24041140509291893147167949)
                ·
                  refine ⟨9015427690984459930187981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24041140509291893147167949 9015427690984459930187981)
                  ·
                    refine ⟨3380785384119172473820493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9015427690984459930187981 3380785384119172473820493)
                    ·
                      refine ⟨1267794519044689677682685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3380785384119172473820493 1267794519044689677682685)
                      ·
                        rfl

theorem cell23_2469021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_2469021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469021 prefixEnd_2469021 := by exact prefixLift 2469021
  have htrace : WordTrace (prefixWord ++ tailWord_2469021) baseStart_2469021 baseEnd_2469021 := by
    simpa [prefixWord, tailWord_2469021, baseEnd_2469021] using wordTrace_append hprefix tailTrace_2469021
  have hstable : (prefixWord ++ tailWord_2469021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469021).length < 2 ^ (prefixWord ++ tailWord_2469021).sum := by decide
  have hdescent : baseEnd_2469021 < baseStart_2469021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469055 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 2, 1, 3]
def baseStart_2469055 : Nat := 118140960795 + 2469055 * 2 ^ 59
def prefixEnd_2469055 : Nat := 4983230072969 + 3 ^ 40 * 2469055 * 2
def baseEnd_2469055 : Nat := 1267811977386942544657529

theorem tailTrace_2469055 : CollatzResearch.WordTrace tailWord_2469055 prefixEnd_2469055 1267811977386942544657529 := by
  unfold tailWord_2469055
  simp only [CollatzResearch.WordTrace]
  refine ⟨90053834070042890867368619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60035889380028593911579079 90053834070042890867368619)
  ·
    refine ⟨135080751105064336301052929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90053834070042890867368619 135080751105064336301052929)
    ·
      refine ⟨101310563328798252225789697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135080751105064336301052929 101310563328798252225789697)
      ·
        refine ⟨75982922496598689169342273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101310563328798252225789697 75982922496598689169342273)
        ·
          refine ⟨56987191872449016877006705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75982922496598689169342273 56987191872449016877006705)
          ·
            refine ⟨42740393904336762657755029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56987191872449016877006705 42740393904336762657755029)
            ·
              refine ⟨2003455964265785749582267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42740393904336762657755029 2003455964265785749582267)
              ·
                refine ⟨3005183946398678624373401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003455964265785749582267 3005183946398678624373401)
                ·
                  refine ⟨2253887959799008968280051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3005183946398678624373401 2253887959799008968280051)
                  ·
                    refine ⟨3380831939698513452420077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2253887959799008968280051 3380831939698513452420077)
                    ·
                      refine ⟨1267811977386942544657529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3380831939698513452420077 1267811977386942544657529)
                      ·
                        rfl

theorem cell23_2469055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 2, 1, 3].length) (baseStart_2469055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469055 prefixEnd_2469055 := by exact prefixLift 2469055
  have htrace : WordTrace (prefixWord ++ tailWord_2469055) baseStart_2469055 baseEnd_2469055 := by
    simpa [prefixWord, tailWord_2469055, baseEnd_2469055] using wordTrace_append hprefix tailTrace_2469055
  have hstable : (prefixWord ++ tailWord_2469055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469055).length < 2 ^ (prefixWord ++ tailWord_2469055).sum := by decide
  have hdescent : baseEnd_2469055 < baseStart_2469055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469104 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_2469104 : Nat := 118140960795 + 2469104 * 2 ^ 59
def prefixEnd_2469104 : Nat := 4983230072969 + 3 ^ 40 * 2469104 * 2
def baseEnd_2469104 : Nat := 1267837137939012852944803

theorem tailTrace_2469104 : CollatzResearch.WordTrace tailWord_2469104 prefixEnd_2469104 1267837137939012852944803 := by
  unfold tailWord_2469104
  simp only [CollatzResearch.WordTrace]
  refine ⟨45027810623432686117951183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60037080831243581490601577 45027810623432686117951183)
  ·
    refine ⟨67541715935149029176926775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45027810623432686117951183 67541715935149029176926775)
    ·
      refine ⟨101312573902723543765390163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67541715935149029176926775 101312573902723543765390163)
      ·
        refine ⟨151968860854085315648085245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101312573902723543765390163 151968860854085315648085245)
        ·
          refine ⟨56988322820281993368031967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151968860854085315648085245 56988322820281993368031967)
          ·
            refine ⟨85482484230422990052047951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56988322820281993368031967 85482484230422990052047951)
            ·
              refine ⟨128223726345634485078071927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85482484230422990052047951 128223726345634485078071927)
              ·
                refine ⟨192335589518451727617107891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128223726345634485078071927 192335589518451727617107891)
                ·
                  refine ⟨288503384277677591425661837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192335589518451727617107891 288503384277677591425661837)
                  ·
                    refine ⟨108188769104129096784623189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 288503384277677591425661837 108188769104129096784623189)
                    ·
                      refine ⟨1267837137939012852944803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 108188769104129096784623189 1267837137939012852944803)
                      ·
                        rfl

theorem cell23_2469104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_2469104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469104 prefixEnd_2469104 := by exact prefixLift 2469104
  have htrace : WordTrace (prefixWord ++ tailWord_2469104) baseStart_2469104 baseEnd_2469104 := by
    simpa [prefixWord, tailWord_2469104, baseEnd_2469104] using wordTrace_append hprefix tailTrace_2469104
  have hstable : (prefixWord ++ tailWord_2469104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469104).length < 2 ^ (prefixWord ++ tailWord_2469104).sum := by decide
  have hdescent : baseEnd_2469104 < baseStart_2469104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469111 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 3]
def baseStart_2469111 : Nat := 118140960795 + 2469111 * 2 ^ 59
def prefixEnd_2469111 : Nat := 4983230072969 + 3 ^ 40 * 2469111 * 2
def baseEnd_2469111 : Nat := 1267840732303594325557271

theorem tailTrace_2469111 : CollatzResearch.WordTrace tailWord_2469111 prefixEnd_2469111 1267840732303594325557271 := by
  unfold tailWord_2469111
  simp only [CollatzResearch.WordTrace]
  refine ⟨90055876557840012431407187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60037251038560008287604791 90055876557840012431407187)
  ·
    refine ⟨135083814836760018647110781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90055876557840012431407187 135083814836760018647110781)
    ·
      refine ⟨50656430563785006992666543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135083814836760018647110781 50656430563785006992666543)
      ·
        refine ⟨75984645845677510488999815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50656430563785006992666543 75984645845677510488999815)
        ·
          refine ⟨113976968768516265733499723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75984645845677510488999815 113976968768516265733499723)
          ·
            refine ⟨170965453152774398600249585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113976968768516265733499723 170965453152774398600249585)
            ·
              refine ⟨128224089864580798950187189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170965453152774398600249585 128224089864580798950187189)
              ·
                refine ⟨12021008424804449901580049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128224089864580798950187189 12021008424804449901580049)
                ·
                  refine ⟨9015756318603337426185037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12021008424804449901580049 9015756318603337426185037)
                  ·
                    refine ⟨3380908619476251534819389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9015756318603337426185037 3380908619476251534819389)
                    ·
                      refine ⟨1267840732303594325557271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3380908619476251534819389 1267840732303594325557271)
                      ·
                        rfl

theorem cell23_2469111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_2469111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469111 prefixEnd_2469111 := by exact prefixLift 2469111
  have htrace : WordTrace (prefixWord ++ tailWord_2469111) baseStart_2469111 baseEnd_2469111 := by
    simpa [prefixWord, tailWord_2469111, baseEnd_2469111] using wordTrace_append hprefix tailTrace_2469111
  have hstable : (prefixWord ++ tailWord_2469111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469111).length < 2 ^ (prefixWord ++ tailWord_2469111).sum := by decide
  have hdescent : baseEnd_2469111 < baseStart_2469111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469118 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_2469118 : Nat := 118140960795 + 2469118 * 2 ^ 59
def prefixEnd_2469118 : Nat := 4983230072969 + 3 ^ 40 * 2469118 * 2
def baseEnd_2469118 : Nat := 140871591852019533129971

theorem tailTrace_2469118 : CollatzResearch.WordTrace tailWord_2469118 prefixEnd_2469118 140871591852019533129971 := by
  unfold tailWord_2469118
  simp only [CollatzResearch.WordTrace]
  refine ⟨11257016483601831578364001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60037421245876435084608005 11257016483601831578364001)
  ·
    refine ⟨8442762362701373683773001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11257016483601831578364001 8442762362701373683773001)
    ·
      refine ⟨6332071772026030262829751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8442762362701373683773001 6332071772026030262829751)
      ·
        refine ⟨9498107658039045394244627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6332071772026030262829751 9498107658039045394244627)
        ·
          refine ⟨14247161487058568091366941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9498107658039045394244627 14247161487058568091366941)
          ·
            refine ⟨5342685557646963034262603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14247161487058568091366941 5342685557646963034262603)
            ·
              refine ⟨8014028336470444551393905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5342685557646963034262603 8014028336470444551393905)
              ·
                refine ⟨6010521252352833413545429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8014028336470444551393905 6010521252352833413545429)
                ·
                  refine ⟨140871591852019533129971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6010521252352833413545429 140871591852019533129971)
                  ·
                    rfl

theorem cell23_2469118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_2469118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469118 prefixEnd_2469118 := by exact prefixLift 2469118
  have htrace : WordTrace (prefixWord ++ tailWord_2469118) baseStart_2469118 baseEnd_2469118 := by
    simpa [prefixWord, tailWord_2469118, baseEnd_2469118] using wordTrace_append hprefix tailTrace_2469118
  have hstable : (prefixWord ++ tailWord_2469118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469118).length < 2 ^ (prefixWord ++ tailWord_2469118).sum := by decide
  have hdescent : baseEnd_2469118 < baseStart_2469118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469131 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 1, 7]
def baseStart_2469131 : Nat := 118140960795 + 2469131 * 2 ^ 59
def prefixEnd_2469131 : Nat := 4983230072969 + 3 ^ 40 * 2469131 * 2
def baseEnd_2469131 : Nat := 422617000638894749102393

theorem tailTrace_2469131 : CollatzResearch.WordTrace tailWord_2469131 prefixEnd_2469131 422617000638894749102393 := by
  unfold tailWord_2469131
  simp only [CollatzResearch.WordTrace]
  refine ⟨90056606017767555847135247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60037737345178370564756831 90056606017767555847135247)
  ·
    refine ⟨135084909026651333770702871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90056606017767555847135247 135084909026651333770702871)
    ·
      refine ⟨202627363539977000656054307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135084909026651333770702871 202627363539977000656054307)
      ·
        refine ⟨303941045309965500984081461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202627363539977000656054307 303941045309965500984081461)
        ·
          refine ⟨28494472997809265717257637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 303941045309965500984081461 28494472997809265717257637)
          ·
            refine ⟨5342713687089237321985807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28494472997809265717257637 5342713687089237321985807)
            ·
              refine ⟨8014070530633855982978711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5342713687089237321985807 8014070530633855982978711)
              ·
                refine ⟨12021105795950783974468067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8014070530633855982978711 12021105795950783974468067)
                ·
                  refine ⟨18031658693926175961702101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12021105795950783974468067 18031658693926175961702101)
                  ·
                    refine ⟨422617000638894749102393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18031658693926175961702101 422617000638894749102393)
                    ·
                      rfl

theorem cell23_2469131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 7].length) (baseStart_2469131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469131 prefixEnd_2469131 := by exact prefixLift 2469131
  have htrace : WordTrace (prefixWord ++ tailWord_2469131) baseStart_2469131 baseEnd_2469131 := by
    simpa [prefixWord, tailWord_2469131, baseEnd_2469131] using wordTrace_append hprefix tailTrace_2469131
  have hstable : (prefixWord ++ tailWord_2469131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469131).length < 2 ^ (prefixWord ++ tailWord_2469131).sum := by decide
  have hdescent : baseEnd_2469131 < baseStart_2469131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469168 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 2, 4, 2]
def baseStart_2469168 : Nat := 118140960795 + 2469168 * 2 ^ 59
def prefixEnd_2469168 : Nat := 4983230072969 + 3 ^ 40 * 2469168 * 2
def baseEnd_2469168 : Nat := 1267870000700900602544509

theorem tailTrace_2469168 : CollatzResearch.WordTrace tailWord_2469168 prefixEnd_2469168 1267870000700900602544509 := by
  unfold tailWord_2469168
  simp only [CollatzResearch.WordTrace]
  refine ⟨45028977759316755583116079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60038637012422340777488105 45028977759316755583116079)
  ·
    refine ⟨67543466638975133374674119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45028977759316755583116079 67543466638975133374674119)
    ·
      refine ⟨101315199958462700062011179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67543466638975133374674119 101315199958462700062011179)
      ·
        refine ⟨151972799937694050093016769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101315199958462700062011179 151972799937694050093016769)
        ·
          refine ⟨113979599953270537569762577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151972799937694050093016769 113979599953270537569762577)
          ·
            refine ⟨85484699964952903177321933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113979599953270537569762577 85484699964952903177321933)
            ·
              refine ⟨32056762486857338691495725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85484699964952903177321933 32056762486857338691495725)
              ·
                refine ⟨12021285932571502009310897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32056762486857338691495725 12021285932571502009310897)
                ·
                  refine ⟨9015964449428626506983173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12021285932571502009310897 9015964449428626506983173)
                  ·
                    refine ⟨1690493334267867470059345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9015964449428626506983173 1690493334267867470059345)
                    ·
                      refine ⟨1267870000700900602544509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1690493334267867470059345 1267870000700900602544509)
                      ·
                        rfl

theorem cell23_2469168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 4, 2].length) (baseStart_2469168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469168 prefixEnd_2469168 := by exact prefixLift 2469168
  have htrace : WordTrace (prefixWord ++ tailWord_2469168) baseStart_2469168 baseEnd_2469168 := by
    simpa [prefixWord, tailWord_2469168, baseEnd_2469168] using wordTrace_append hprefix tailTrace_2469168
  have hstable : (prefixWord ++ tailWord_2469168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469168).length < 2 ^ (prefixWord ++ tailWord_2469168).sum := by decide
  have hdescent : baseEnd_2469168 < baseStart_2469168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469178 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 3, 4]
def baseStart_2469178 : Nat := 118140960795 + 2469178 * 2 ^ 59
def prefixEnd_2469178 : Nat := 4983230072969 + 3 ^ 40 * 2469178 * 2
def baseEnd_2469178 : Nat := 422625045169148521139821

theorem tailTrace_2469178 : CollatzResearch.WordTrace tailWord_2469178 prefixEnd_2469178 422625045169148521139821 := by
  unfold tailWord_2469178
  simp only [CollatzResearch.WordTrace]
  refine ⟨22514580062149320718524047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60038880165731521916064125 22514580062149320718524047)
  ·
    refine ⟨33771870093223981077786071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22514580062149320718524047 33771870093223981077786071)
    ·
      refine ⟨50657805139835971616679107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33771870093223981077786071 50657805139835971616679107)
      ·
        refine ⟨75986707709753957425018661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50657805139835971616679107 75986707709753957425018661)
        ·
          refine ⟨14247507695578867017190999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75986707709753957425018661 14247507695578867017190999)
          ·
            refine ⟨21371261543368300525786499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14247507695578867017190999 21371261543368300525786499)
            ·
              refine ⟨32056892315052450788679749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21371261543368300525786499 32056892315052450788679749)
              ·
                refine ⟨6010667309072334522877453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32056892315052450788679749 6010667309072334522877453)
                ·
                  refine ⟨2254000240902125446079045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6010667309072334522877453 2254000240902125446079045)
                  ·
                    refine ⟨422625045169148521139821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2254000240902125446079045 422625045169148521139821)
                    ·
                      rfl

theorem cell23_2469178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_2469178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469178 prefixEnd_2469178 := by exact prefixLift 2469178
  have htrace : WordTrace (prefixWord ++ tailWord_2469178) baseStart_2469178 baseEnd_2469178 := by
    simpa [prefixWord, tailWord_2469178, baseEnd_2469178] using wordTrace_append hprefix tailTrace_2469178
  have hstable : (prefixWord ++ tailWord_2469178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469178).length < 2 ^ (prefixWord ++ tailWord_2469178).sum := by decide
  have hdescent : baseEnd_2469178 < baseStart_2469178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469191 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 8]
def baseStart_2469191 : Nat := 118140960795 + 2469191 * 2 ^ 59
def prefixEnd_2469191 : Nat := 4983230072969 + 3 ^ 40 * 2469191 * 2
def baseEnd_2469191 : Nat := 140875756750661556950767

theorem tailTrace_2469191 : CollatzResearch.WordTrace tailWord_2469191 prefixEnd_2469191 140875756750661556950767 := by
  unfold tailWord_2469191
  simp only [CollatzResearch.WordTrace]
  refine ⟨90058794397550186094319427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60039196265033457396212951 90058794397550186094319427)
  ·
    refine ⟨135088191596325279141479141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90058794397550186094319427 135088191596325279141479141)
    ·
      refine ⟨25329035924310989839027339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135088191596325279141479141 25329035924310989839027339)
      ·
        refine ⟨37993553886466484758541009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25329035924310989839027339 37993553886466484758541009)
        ·
          refine ⟨28495165414849863568905757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37993553886466484758541009 28495165414849863568905757)
          ·
            refine ⟨10685687030568698838339659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28495165414849863568905757 10685687030568698838339659)
            ·
              refine ⟨16028530545853048257509489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10685687030568698838339659 16028530545853048257509489)
              ·
                refine ⟨12021397909389786193132117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16028530545853048257509489 12021397909389786193132117)
                ·
                  refine ⟨140875756750661556950767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12021397909389786193132117 140875756750661556950767)
                  ·
                    rfl

theorem cell23_2469191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 8].length) (baseStart_2469191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469191 prefixEnd_2469191 := by exact prefixLift 2469191
  have htrace : WordTrace (prefixWord ++ tailWord_2469191) baseStart_2469191 baseEnd_2469191 := by
    simpa [prefixWord, tailWord_2469191, baseEnd_2469191] using wordTrace_append hprefix tailTrace_2469191
  have hstable : (prefixWord ++ tailWord_2469191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469191).length < 2 ^ (prefixWord ++ tailWord_2469191).sum := by decide
  have hdescent : baseEnd_2469191 < baseStart_2469191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469205 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_2469205 : Nat := 118140960795 + 2469205 * 2 ^ 59
def prefixEnd_2469205 : Nat := 4983230072969 + 3 ^ 40 * 2469205 * 2
def baseEnd_2469205 : Nat := 1267888999485116957781839

theorem tailTrace_2469205 : CollatzResearch.WordTrace tailWord_2469205 prefixEnd_2469205 1267888999485116957781839 := by
  unfold tailWord_2469205
  simp only [CollatzResearch.WordTrace]
  refine ⟨90059305019499466485329069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60039536679666310990219379 90059305019499466485329069)
  ·
    refine ⟨33772239382312299931998401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90059305019499466485329069 33772239382312299931998401)
    ·
      refine ⟨25329179536734224948998801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33772239382312299931998401 25329179536734224948998801)
      ·
        refine ⟨18996884652550668711749101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25329179536734224948998801 18996884652550668711749101)
        ·
          refine ⟨7123831744706500766905913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18996884652550668711749101 7123831744706500766905913)
          ·
            refine ⟨5342873808529875575179435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7123831744706500766905913 5342873808529875575179435)
            ·
              refine ⟨8014310712794813362769153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5342873808529875575179435 8014310712794813362769153)
              ·
                refine ⟨6010733034596110022076865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8014310712794813362769153 6010733034596110022076865)
                ·
                  refine ⟨4508049775947082516557649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6010733034596110022076865 4508049775947082516557649)
                  ·
                    refine ⟨3381037331960311887418237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4508049775947082516557649 3381037331960311887418237)
                    ·
                      refine ⟨1267888999485116957781839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3381037331960311887418237 1267888999485116957781839)
                      ·
                        rfl

theorem cell23_2469205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_2469205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469205 prefixEnd_2469205 := by exact prefixLift 2469205
  have htrace : WordTrace (prefixWord ++ tailWord_2469205) baseStart_2469205 baseEnd_2469205 := by
    simpa [prefixWord, tailWord_2469205, baseEnd_2469205] using wordTrace_append hprefix tailTrace_2469205
  have hstable : (prefixWord ++ tailWord_2469205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469205).length < 2 ^ (prefixWord ++ tailWord_2469205).sum := by decide
  have hdescent : baseEnd_2469205 < baseStart_2469205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469269 : List Nat := [1, 3, 2, 1, 1, 2, 6, 2, 1, 1, 3]
def baseStart_2469269 : Nat := 118140960795 + 2469269 * 2 ^ 59
def prefixEnd_2469269 : Nat := 4983230072969 + 3 ^ 40 * 2469269 * 2
def baseEnd_2469269 : Nat := 1267921862247004707381545

theorem tailTrace_2469269 : CollatzResearch.WordTrace tailWord_2469269 prefixEnd_2469269 1267921862247004707381545 := by
  unfold tailWord_2469269
  simp only [CollatzResearch.WordTrace]
  refine ⟨90061639291267605415658861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60041092860845070277105907 90061639291267605415658861)
  ·
    refine ⟨33773114734225352030872073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90061639291267605415658861 33773114734225352030872073)
    ·
      refine ⟨25329836050669014023154055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33773114734225352030872073 25329836050669014023154055)
      ·
        refine ⟨37994754076003521034731083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25329836050669014023154055 37994754076003521034731083)
        ·
          refine ⟨56992131114005281552096625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37994754076003521034731083 56992131114005281552096625)
          ·
            refine ⟨42744098335503961164072469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56992131114005281552096625 42744098335503961164072469)
            ·
              refine ⟨2003629609476748179565897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42744098335503961164072469 2003629609476748179565897)
              ·
                refine ⟨1502722207107561134674423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003629609476748179565897 1502722207107561134674423)
                ·
                  refine ⟨2254083310661341702011635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502722207107561134674423 2254083310661341702011635)
                  ·
                    refine ⟨3381124965992012553017453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2254083310661341702011635 3381124965992012553017453)
                    ·
                      refine ⟨1267921862247004707381545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3381124965992012553017453 1267921862247004707381545)
                      ·
                        rfl

theorem cell23_2469269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_2469269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469269 prefixEnd_2469269 := by exact prefixLift 2469269
  have htrace : WordTrace (prefixWord ++ tailWord_2469269) baseStart_2469269 baseEnd_2469269 := by
    simpa [prefixWord, tailWord_2469269, baseEnd_2469269] using wordTrace_append hprefix tailTrace_2469269
  have hstable : (prefixWord ++ tailWord_2469269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469269).length < 2 ^ (prefixWord ++ tailWord_2469269).sum := by decide
  have hdescent : baseEnd_2469269 < baseStart_2469269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469312 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 1, 2, 3]
def baseStart_2469312 : Nat := 118140960795 + 2469312 * 2 ^ 59
def prefixEnd_2469312 : Nat := 4983230072969 + 3 ^ 40 * 2469312 * 2
def baseEnd_2469312 : Nat := 1267943941915148039143847

theorem tailTrace_2469312 : CollatzResearch.WordTrace tailWord_2469312 prefixEnd_2469312 1267943941915148039143847 := by
  unfold tailWord_2469312
  simp only [CollatzResearch.WordTrace]
  refine ⟨45031603815055911879737095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60042138420074549172982793 45031603815055911879737095)
  ·
    refine ⟨67547405722583867819605643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45031603815055911879737095 67547405722583867819605643)
    ·
      refine ⟨101321108583875801729408465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67547405722583867819605643 101321108583875801729408465)
      ·
        refine ⟨75990831437906851297056349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101321108583875801729408465 75990831437906851297056349)
        ·
          refine ⟨28496561789215069236396131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75990831437906851297056349 28496561789215069236396131)
          ·
            refine ⟨42744842683822603854594197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28496561789215069236396131 42744842683822603854594197)
            ·
              refine ⟨2003664500804184555684103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42744842683822603854594197 2003664500804184555684103)
              ·
                refine ⟨3005496751206276833526155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003664500804184555684103 3005496751206276833526155)
                ·
                  refine ⟨4508245126809415250289233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005496751206276833526155 4508245126809415250289233)
                  ·
                    refine ⟨3381183845107061437716925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4508245126809415250289233 3381183845107061437716925)
                    ·
                      refine ⟨1267943941915148039143847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3381183845107061437716925 1267943941915148039143847)
                      ·
                        rfl

theorem cell23_2469312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 2, 3].length) (baseStart_2469312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469312 prefixEnd_2469312 := by exact prefixLift 2469312
  have htrace : WordTrace (prefixWord ++ tailWord_2469312) baseStart_2469312 baseEnd_2469312 := by
    simpa [prefixWord, tailWord_2469312, baseEnd_2469312] using wordTrace_append hprefix tailTrace_2469312
  have hstable : (prefixWord ++ tailWord_2469312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469312).length < 2 ^ (prefixWord ++ tailWord_2469312).sum := by decide
  have hdescent : baseEnd_2469312 < baseStart_2469312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469335 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 5, 3, 2]
def baseStart_2469335 : Nat := 118140960795 + 2469335 * 2 ^ 59
def prefixEnd_2469335 : Nat := 4983230072969 + 3 ^ 40 * 2469335 * 2
def baseEnd_2469335 : Nat := 1267955751970201449156241

theorem tailTrace_2469335 : CollatzResearch.WordTrace tailWord_2469335 prefixEnd_2469335 1267955751970201449156241 := by
  unfold tailWord_2469335
  simp only [CollatzResearch.WordTrace]
  refine ⟨90064046509028498687561459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60042697672685665791707639 90064046509028498687561459)
  ·
    refine ⟨135096069763542748031342189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90064046509028498687561459 135096069763542748031342189)
    ·
      refine ⟨50661026161328530511753321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135096069763542748031342189 50661026161328530511753321)
      ·
        refine ⟨37995769620996397883814991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50661026161328530511753321 37995769620996397883814991)
        ·
          refine ⟨56993654431494596825722487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37995769620996397883814991 56993654431494596825722487)
          ·
            refine ⟨85490481647241895238583731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56993654431494596825722487 85490481647241895238583731)
            ·
              refine ⟨128235722470862842857875597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85490481647241895238583731 128235722470862842857875597)
              ·
                refine ⟨48088395926573566071703349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128235722470862842857875597 48088395926573566071703349)
                ·
                  refine ⟨4508287118116271819222189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48088395926573566071703349 4508287118116271819222189)
                  ·
                    refine ⟨1690607669293601932208321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4508287118116271819222189 1690607669293601932208321)
                    ·
                      refine ⟨1267955751970201449156241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1690607669293601932208321 1267955751970201449156241)
                      ·
                        rfl

theorem cell23_2469335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_2469335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469335 prefixEnd_2469335 := by exact prefixLift 2469335
  have htrace : WordTrace (prefixWord ++ tailWord_2469335) baseStart_2469335 baseEnd_2469335 := by
    simpa [prefixWord, tailWord_2469335, baseEnd_2469335] using wordTrace_append hprefix tailTrace_2469335
  have hstable : (prefixWord ++ tailWord_2469335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469335).length < 2 ^ (prefixWord ++ tailWord_2469335).sum := by decide
  have hdescent : baseEnd_2469335 < baseStart_2469335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469348 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_2469348 : Nat := 118140960795 + 2469348 * 2 ^ 59
def prefixEnd_2469348 : Nat := 4983230072969 + 3 ^ 40 * 2469348 * 2
def baseEnd_2469348 : Nat := 1267962427218709898293681

theorem tailTrace_2469348 : CollatzResearch.WordTrace tailWord_2469348 prefixEnd_2469348 1267962427218709898293681 := by
  unfold tailWord_2469348
  simp only [CollatzResearch.WordTrace]
  refine ⟨45032260328990700953892349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60043013771987601271856465 45032260328990700953892349)
  ·
    refine ⟨16887097623371512857709631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45032260328990700953892349 16887097623371512857709631)
    ·
      refine ⟨25330646435057269286564447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16887097623371512857709631 25330646435057269286564447)
      ·
        refine ⟨37995969652585903929846671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25330646435057269286564447 37995969652585903929846671)
        ·
          refine ⟨56993954478878855894770007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37995969652585903929846671 56993954478878855894770007)
          ·
            refine ⟨85490931718318283842155011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56993954478878855894770007 85490931718318283842155011)
            ·
              refine ⟨128236397577477425763232517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85490931718318283842155011 128236397577477425763232517)
              ·
                refine ⟨24044324545777017330606097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128236397577477425763232517 24044324545777017330606097)
                ·
                  refine ⟨18033243409332762997954573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24044324545777017330606097 18033243409332762997954573)
                  ·
                    refine ⟨6762466278499786124232965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18033243409332762997954573 6762466278499786124232965)
                    ·
                      refine ⟨1267962427218709898293681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6762466278499786124232965 1267962427218709898293681)
                      ·
                        rfl

theorem cell23_2469348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_2469348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469348 prefixEnd_2469348 := by exact prefixLift 2469348
  have htrace : WordTrace (prefixWord ++ tailWord_2469348) baseStart_2469348 baseEnd_2469348 := by
    simpa [prefixWord, tailWord_2469348, baseEnd_2469348] using wordTrace_append hprefix tailTrace_2469348
  have hstable : (prefixWord ++ tailWord_2469348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469348).length < 2 ^ (prefixWord ++ tailWord_2469348).sum := by decide
  have hdescent : baseEnd_2469348 < baseStart_2469348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469368 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_2469368 : Nat := 118140960795 + 2469368 * 2 ^ 59
def prefixEnd_2469368 : Nat := 4983230072969 + 3 ^ 40 * 2469368 * 2
def baseEnd_2469368 : Nat := 1267972696831799820043589

theorem tailTrace_2469368 : CollatzResearch.WordTrace tailWord_2469368 prefixEnd_2469368 1267972696831799820043589 := by
  unfold tailWord_2469368
  simp only [CollatzResearch.WordTrace]
  refine ⟨45032625058954472661756379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60043500078605963549008505 45032625058954472661756379)
  ·
    refine ⟨67548937588431708992634569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45032625058954472661756379 67548937588431708992634569)
    ·
      refine ⟨50661703191323781744475927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67548937588431708992634569 50661703191323781744475927)
      ·
        refine ⟨75992554786985672616713891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50661703191323781744475927 75992554786985672616713891)
        ·
          refine ⟨113988832180478508925070837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75992554786985672616713891 113988832180478508925070837)
          ·
            refine ⟨10686453016919860211725391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113988832180478508925070837 10686453016919860211725391)
            ·
              refine ⟨16029679525379790317588087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10686453016919860211725391 16029679525379790317588087)
              ·
                refine ⟨24044519288069685476382131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16029679525379790317588087 24044519288069685476382131)
                ·
                  refine ⟨36066778932104528214573197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24044519288069685476382131 36066778932104528214573197)
                  ·
                    refine ⟨13525042099539198080464949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36066778932104528214573197 13525042099539198080464949)
                    ·
                      refine ⟨1267972696831799820043589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13525042099539198080464949 1267972696831799820043589)
                      ·
                        rfl

theorem cell23_2469368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_2469368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469368 prefixEnd_2469368 := by exact prefixLift 2469368
  have htrace : WordTrace (prefixWord ++ tailWord_2469368) baseStart_2469368 baseEnd_2469368 := by
    simpa [prefixWord, tailWord_2469368, baseEnd_2469368] using wordTrace_append hprefix tailTrace_2469368
  have hstable : (prefixWord ++ tailWord_2469368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469368).length < 2 ^ (prefixWord ++ tailWord_2469368).sum := by decide
  have hdescent : baseEnd_2469368 < baseStart_2469368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469439 : List Nat := [1, 1, 2, 2, 3, 5, 2, 2, 5]
def baseStart_2469439 : Nat := 118140960795 + 2469439 * 2 ^ 59
def prefixEnd_2469439 : Nat := 4983230072969 + 3 ^ 40 * 2469439 * 2
def baseEnd_2469439 : Nat := 140889905995363226917307

theorem tailTrace_2469439 : CollatzResearch.WordTrace tailWord_2469439 prefixEnd_2469439 140889905995363226917307 := by
  unfold tailWord_2469439
  simp only [CollatzResearch.WordTrace]
  refine ⟨90067839700651724449347371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60045226467101149632898247 90067839700651724449347371)
  ·
    refine ⟨135101759550977586674021057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90067839700651724449347371 135101759550977586674021057)
    ·
      refine ⟨101326319663233190005515793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135101759550977586674021057 101326319663233190005515793)
      ·
        refine ⟨75994739747424892504136845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101326319663233190005515793 75994739747424892504136845)
        ·
          refine ⟨28498027405284334689051317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75994739747424892504136845 28498027405284334689051317)
          ·
            refine ⟨2671690069245406377098561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28498027405284334689051317 2671690069245406377098561)
            ·
              refine ⟨2003767551934054782823921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2671690069245406377098561 2003767551934054782823921)
              ·
                refine ⟨1502825663950541087117941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003767551934054782823921 1502825663950541087117941)
                ·
                  refine ⟨140889905995363226917307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1502825663950541087117941 140889905995363226917307)
                  ·
                    rfl

theorem cell23_2469439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 5].length) (baseStart_2469439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469439 prefixEnd_2469439 := by exact prefixLift 2469439
  have htrace : WordTrace (prefixWord ++ tailWord_2469439) baseStart_2469439 baseEnd_2469439 := by
    simpa [prefixWord, tailWord_2469439, baseEnd_2469439] using wordTrace_append hprefix tailTrace_2469439
  have hstable : (prefixWord ++ tailWord_2469439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469439).length < 2 ^ (prefixWord ++ tailWord_2469439).sum := by decide
  have hdescent : baseEnd_2469439 < baseStart_2469439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469448 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 4, 8]
def baseStart_2469448 : Nat := 118140960795 + 2469448 * 2 ^ 59
def prefixEnd_2469448 : Nat := 4983230072969 + 3 ^ 40 * 2469448 * 2
def baseEnd_2469448 : Nat := 422671258428053169014407

theorem tailTrace_2469448 : CollatzResearch.WordTrace tailWord_2469448 prefixEnd_2469448 422671258428053169014407 := by
  unfold tailWord_2469448
  simp only [CollatzResearch.WordTrace]
  refine ⟨45034083978809559493212499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60045445305079412657616665 45034083978809559493212499)
  ·
    refine ⟨67551125968214339239818749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45034083978809559493212499 67551125968214339239818749)
    ·
      refine ⟨25331672238080377214932031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67551125968214339239818749 25331672238080377214932031)
      ·
        refine ⟨37997508357120565822398047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25331672238080377214932031 37997508357120565822398047)
        ·
          refine ⟨56996262535680848733597071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37997508357120565822398047 56996262535680848733597071)
          ·
            refine ⟨85494393803521273100395607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56996262535680848733597071 85494393803521273100395607)
            ·
              refine ⟨128241590705281909650593411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85494393803521273100395607 128241590705281909650593411)
              ·
                refine ⟨192362386057922864475890117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128241590705281909650593411 192362386057922864475890117)
                ·
                  refine ⟨36067947385860537089229397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192362386057922864475890117 36067947385860537089229397)
                  ·
                    refine ⟨422671258428053169014407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36067947385860537089229397 422671258428053169014407)
                    ·
                      rfl

theorem cell23_2469448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_2469448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469448 prefixEnd_2469448 := by exact prefixLift 2469448
  have htrace : WordTrace (prefixWord ++ tailWord_2469448) baseStart_2469448 baseEnd_2469448 := by
    simpa [prefixWord, tailWord_2469448, baseEnd_2469448] using wordTrace_append hprefix tailTrace_2469448
  have hstable : (prefixWord ++ tailWord_2469448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469448).length < 2 ^ (prefixWord ++ tailWord_2469448).sum := by decide
  have hdescent : baseEnd_2469448 < baseStart_2469448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469469 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2469469 : Nat := 118140960795 + 2469469 * 2 ^ 59
def prefixEnd_2469469 : Nat := 4983230072969 + 3 ^ 40 * 2469469 * 2
def baseEnd_2469469 : Nat := 422674852792634641626875

theorem tailTrace_2469469 : CollatzResearch.WordTrace tailWord_2469469 prefixEnd_2469469 422674852792634641626875 := by
  unfold tailWord_2469469
  simp only [CollatzResearch.WordTrace]
  refine ⟨90068933890543039572939461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60045955927028693048626307 90068933890543039572939461)
  ·
    refine ⟨16887925104476819919926149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90068933890543039572939461 16887925104476819919926149)
    ·
      refine ⟨3166485957089403734986153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16887925104476819919926149 3166485957089403734986153)
      ·
        refine ⟨2374864467817052801239615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3166485957089403734986153 2374864467817052801239615)
        ·
          refine ⟨3562296701725579201859423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374864467817052801239615 3562296701725579201859423)
          ·
            refine ⟨5343445052588368802789135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562296701725579201859423 5343445052588368802789135)
            ·
              refine ⟨8015167578882553204183703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5343445052588368802789135 8015167578882553204183703)
              ·
                refine ⟨12022751368323829806275555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8015167578882553204183703 12022751368323829806275555)
                ·
                  refine ⟨18034127052485744709413333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12022751368323829806275555 18034127052485744709413333)
                  ·
                    refine ⟨422674852792634641626875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18034127052485744709413333 422674852792634641626875)
                    ·
                      rfl

theorem cell23_2469469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2469469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469469 prefixEnd_2469469 := by exact prefixLift 2469469
  have htrace : WordTrace (prefixWord ++ tailWord_2469469) baseStart_2469469 baseEnd_2469469 := by
    simpa [prefixWord, tailWord_2469469, baseEnd_2469469] using wordTrace_append hprefix tailTrace_2469469
  have hstable : (prefixWord ++ tailWord_2469469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469469).length < 2 ^ (prefixWord ++ tailWord_2469469).sum := by decide
  have hdescent : baseEnd_2469469 < baseStart_2469469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469525 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_2469525 : Nat := 118140960795 + 2469525 * 2 ^ 59
def prefixEnd_2469525 : Nat := 4983230072969 + 3 ^ 40 * 2469525 * 2
def baseEnd_2469525 : Nat := 422684437764851901926789

theorem tailTrace_2469525 : CollatzResearch.WordTrace tailWord_2469525 prefixEnd_2469525 422684437764851901926789 := by
  unfold tailWord_2469525
  simp only [CollatzResearch.WordTrace]
  refine ⟨90070976378340161136978029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60047317585560107424652019 90070976378340161136978029)
  ·
    refine ⟨33776616141877560426366761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90070976378340161136978029 33776616141877560426366761)
    ·
      refine ⟨25332462106408170319775071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33776616141877560426366761 25332462106408170319775071)
      ·
        refine ⟨37998693159612255479662607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25332462106408170319775071 37998693159612255479662607)
        ·
          refine ⟨56998039739418383219493911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37998693159612255479662607 56998039739418383219493911)
          ·
            refine ⟨85497059609127574829240867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56998039739418383219493911 85497059609127574829240867)
            ·
              refine ⟨128245589413691362243861301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85497059609127574829240867 128245589413691362243861301)
              ·
                refine ⟨12023024007533565210361997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128245589413691362243861301 12023024007533565210361997)
                ·
                  refine ⟨4508634002825086953885749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12023024007533565210361997 4508634002825086953885749)
                  ·
                    refine ⟨422684437764851901926789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4508634002825086953885749 422684437764851901926789)
                    ·
                      rfl

theorem cell23_2469525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_2469525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469525 prefixEnd_2469525 := by exact prefixLift 2469525
  have htrace : WordTrace (prefixWord ++ tailWord_2469525) baseStart_2469525 baseEnd_2469525 := by
    simpa [prefixWord, tailWord_2469525, baseEnd_2469525] using wordTrace_append hprefix tailTrace_2469525
  have hstable : (prefixWord ++ tailWord_2469525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469525).length < 2 ^ (prefixWord ++ tailWord_2469525).sum := by decide
  have hdescent : baseEnd_2469525 < baseStart_2469525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469550 : List Nat := [4, 1, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2469550 : Nat := 118140960795 + 2469550 * 2 ^ 59
def prefixEnd_2469550 : Nat := 4983230072969 + 3 ^ 40 * 2469550 * 2
def baseEnd_2469550 : Nat := 422688716770306035989251

theorem tailTrace_2469550 : CollatzResearch.WordTrace tailWord_2469550 prefixEnd_2469550 422688716770306035989251 := by
  unfold tailWord_2469550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11258986025406198800829763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60047925468833060271092069 11258986025406198800829763)
  ·
    refine ⟨16888479038109298201244645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11258986025406198800829763 16888479038109298201244645)
    ·
      refine ⟨3166589819645493412733371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16888479038109298201244645 3166589819645493412733371)
      ·
        refine ⟨4749884729468240119100057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3166589819645493412733371 4749884729468240119100057)
        ·
          refine ⟨3562413547101180089325043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4749884729468240119100057 3562413547101180089325043)
          ·
            refine ⟨5343620320651770133987565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562413547101180089325043 5343620320651770133987565)
            ·
              refine ⟨2003857620244413800245337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5343620320651770133987565 2003857620244413800245337)
              ·
                refine ⟨1502893215183310350184003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003857620244413800245337 1502893215183310350184003)
                ·
                  refine ⟨2254339822774965525276005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502893215183310350184003 2254339822774965525276005)
                  ·
                    refine ⟨422688716770306035989251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2254339822774965525276005 422688716770306035989251)
                    ·
                      rfl

theorem cell23_2469550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2469550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469550 prefixEnd_2469550 := by exact prefixLift 2469550
  have htrace : WordTrace (prefixWord ++ tailWord_2469550) baseStart_2469550 baseEnd_2469550 := by
    simpa [prefixWord, tailWord_2469550, baseEnd_2469550] using wordTrace_append hprefix tailTrace_2469550
  have hstable : (prefixWord ++ tailWord_2469550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469550).length < 2 ^ (prefixWord ++ tailWord_2469550).sum := by decide
  have hdescent : baseEnd_2469550 < baseStart_2469550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469572 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_2469572 : Nat := 118140960795 + 2469572 * 2 ^ 59
def prefixEnd_2469572 : Nat := 4983230072969 + 3 ^ 40 * 2469572 * 2
def baseEnd_2469572 : Nat := 422692482295105673964217

theorem tailTrace_2469572 : CollatzResearch.WordTrace tailWord_2469572 prefixEnd_2469572 422692482295105673964217 := by
  unfold tailWord_2469572
  simp only [CollatzResearch.WordTrace]
  refine ⟨45036345304584944081969485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60048460406113258775959313 45036345304584944081969485)
  ·
    refine ⟨16888629489219354030738557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45036345304584944081969485 16888629489219354030738557)
    ·
      refine ⟨6333236058457257761526959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16888629489219354030738557 6333236058457257761526959)
      ·
        refine ⟨9499854087685886642290439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6333236058457257761526959 9499854087685886642290439)
        ·
          refine ⟨14249781131528829963435659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9499854087685886642290439 14249781131528829963435659)
          ·
            refine ⟨21374671697293244945153489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14249781131528829963435659 21374671697293244945153489)
            ·
              refine ⟨16031003772969933708865117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21374671697293244945153489 16031003772969933708865117)
              ·
                refine ⟨6011626414863725140824419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16031003772969933708865117 6011626414863725140824419)
                ·
                  refine ⟨9017439622295587711236629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6011626414863725140824419 9017439622295587711236629)
                  ·
                    refine ⟨422692482295105673964217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9017439622295587711236629 422692482295105673964217)
                    ·
                      rfl

theorem cell23_2469572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_2469572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469572 prefixEnd_2469572 := by exact prefixLift 2469572
  have htrace : WordTrace (prefixWord ++ tailWord_2469572) baseStart_2469572 baseEnd_2469572 := by
    simpa [prefixWord, tailWord_2469572, baseEnd_2469572] using wordTrace_append hprefix tailTrace_2469572
  have hstable : (prefixWord ++ tailWord_2469572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469572).length < 2 ^ (prefixWord ++ tailWord_2469572).sum := by decide
  have hdescent : baseEnd_2469572 < baseStart_2469572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469575 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_2469575 : Nat := 118140960795 + 2469575 * 2 ^ 59
def prefixEnd_2469575 : Nat := 4983230072969 + 3 ^ 40 * 2469575 * 2
def baseEnd_2469575 : Nat := 1268078987327280510155137

theorem tailTrace_2469575 : CollatzResearch.WordTrace tailWord_2469575 prefixEnd_2469575 1268078987327280510155137 := by
  unfold tailWord_2469575
  simp only [CollatzResearch.WordTrace]
  refine ⟨90072800028159019676298179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60048533352106013117532119 90072800028159019676298179)
  ·
    refine ⟨135109200042238529514447269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90072800028159019676298179 135109200042238529514447269)
    ·
      refine ⟨25332975007919724283958863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135109200042238529514447269 25332975007919724283958863)
      ·
        refine ⟨37999462511879586425938295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25332975007919724283958863 37999462511879586425938295)
        ·
          refine ⟨56999193767819379638907443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37999462511879586425938295 56999193767819379638907443)
          ·
            refine ⟨85498790651729069458361165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56999193767819379638907443 85498790651729069458361165)
            ·
              refine ⟨32062046494398401046885437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85498790651729069458361165 32062046494398401046885437)
              ·
                refine ⟨12023267435399400392582039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32062046494398401046885437 12023267435399400392582039)
                ·
                  refine ⟨18034901153099100588873059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12023267435399400392582039 18034901153099100588873059)
                  ·
                    refine ⟨27052351729648650883309589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18034901153099100588873059 27052351729648650883309589)
                    ·
                      refine ⟨1268078987327280510155137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27052351729648650883309589 1268078987327280510155137)
                      ·
                        rfl

theorem cell23_2469575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_2469575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469575 prefixEnd_2469575 := by exact prefixLift 2469575
  have htrace : WordTrace (prefixWord ++ tailWord_2469575) baseStart_2469575 baseEnd_2469575 := by
    simpa [prefixWord, tailWord_2469575, baseEnd_2469575] using wordTrace_append hprefix tailTrace_2469575
  have hstable : (prefixWord ++ tailWord_2469575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469575).length < 2 ^ (prefixWord ++ tailWord_2469575).sum := by decide
  have hdescent : baseEnd_2469575 < baseStart_2469575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469579 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 3, 2, 2]
def baseStart_2469579 : Nat := 118140960795 + 2469579 * 2 ^ 59
def prefixEnd_2469579 : Nat := 4983230072969 + 3 ^ 40 * 2469579 * 2
def baseEnd_2469579 : Nat := 1268081041249898494505119

theorem tailTrace_2469579 : CollatzResearch.WordTrace tailWord_2469579 prefixEnd_2469579 1268081041249898494505119 := by
  unfold tailWord_2469579
  simp only [CollatzResearch.WordTrace]
  refine ⟨90072945920144528359443791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60048630613429685572962527 90072945920144528359443791)
  ·
    refine ⟨135109418880216792539165687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90072945920144528359443791 135109418880216792539165687)
    ·
      refine ⟨202664128320325188808748531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135109418880216792539165687 202664128320325188808748531)
      ·
        refine ⟨303996192480487783213122797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202664128320325188808748531 303996192480487783213122797)
        ·
          refine ⟨113998572180182918704921049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303996192480487783213122797 113998572180182918704921049)
          ·
            refine ⟨85498929135137189028690787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113998572180182918704921049 85498929135137189028690787)
            ·
              refine ⟨128248393702705783543036181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85498929135137189028690787 128248393702705783543036181)
              ·
                refine ⟨6011643454814333603579821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128248393702705783543036181 6011643454814333603579821)
                ·
                  refine ⟨2254366295555375101342433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6011643454814333603579821 2254366295555375101342433)
                  ·
                    refine ⟨1690774721666531326006825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2254366295555375101342433 1690774721666531326006825)
                    ·
                      refine ⟨1268081041249898494505119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1690774721666531326006825 1268081041249898494505119)
                      ·
                        rfl

theorem cell23_2469579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 2, 2].length) (baseStart_2469579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469579 prefixEnd_2469579 := by exact prefixLift 2469579
  have htrace : WordTrace (prefixWord ++ tailWord_2469579) baseStart_2469579 baseEnd_2469579 := by
    simpa [prefixWord, tailWord_2469579, baseEnd_2469579] using wordTrace_append hprefix tailTrace_2469579
  have hstable : (prefixWord ++ tailWord_2469579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469579).length < 2 ^ (prefixWord ++ tailWord_2469579).sum := by decide
  have hdescent : baseEnd_2469579 < baseStart_2469579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469585 : List Nat := [1, 2, 2, 1, 2, 4, 2, 9]
def baseStart_2469585 : Nat := 118140960795 + 2469585 * 2 ^ 59
def prefixEnd_2469585 : Nat := 4983230072969 + 3 ^ 40 * 2469585 * 2
def baseEnd_2469585 : Nat := 46966078597549091519633

theorem tailTrace_2469585 : CollatzResearch.WordTrace tailWord_2469585 prefixEnd_2469585 46966078597549091519633 := by
  unfold tailWord_2469585
  simp only [CollatzResearch.WordTrace]
  refine ⟨90073164758122791384162209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60048776505415194256108139 90073164758122791384162209)
  ·
    refine ⟨67554873568592093538121657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90073164758122791384162209 67554873568592093538121657)
    ·
      refine ⟨50666155176444070153591243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67554873568592093538121657 50666155176444070153591243)
      ·
        refine ⟨75999232764666105230386865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50666155176444070153591243 75999232764666105230386865)
        ·
          refine ⟨56999424573499578922790149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75999232764666105230386865 56999424573499578922790149)
          ·
            refine ⟨10687392107531171048023153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56999424573499578922790149 10687392107531171048023153)
            ·
              refine ⟨8015544080648378286017365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10687392107531171048023153 8015544080648378286017365)
              ·
                refine ⟨46966078597549091519633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8015544080648378286017365 46966078597549091519633)
                ·
                  rfl

theorem cell23_2469585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 9].length) (baseStart_2469585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469585 prefixEnd_2469585 := by exact prefixLift 2469585
  have htrace : WordTrace (prefixWord ++ tailWord_2469585) baseStart_2469585 baseEnd_2469585 := by
    simpa [prefixWord, tailWord_2469585, baseEnd_2469585] using wordTrace_append hprefix tailTrace_2469585
  have hstable : (prefixWord ++ tailWord_2469585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469585).length < 2 ^ (prefixWord ++ tailWord_2469585).sum := by decide
  have hdescent : baseEnd_2469585 < baseStart_2469585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469592 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2469592 : Nat := 118140960795 + 2469592 * 2 ^ 59
def prefixEnd_2469592 : Nat := 4983230072969 + 3 ^ 40 * 2469592 * 2
def baseEnd_2469592 : Nat := 1268087716498406943642559

theorem tailTrace_2469592 : CollatzResearch.WordTrace tailWord_2469592 prefixEnd_2469592 1268087716498406943642559 := by
  unfold tailWord_2469592
  simp only [CollatzResearch.WordTrace]
  refine ⟨45036710034548715789833515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60048946712731621053111353 45036710034548715789833515)
  ·
    refine ⟨67555065051823073684750273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45036710034548715789833515 67555065051823073684750273)
    ·
      refine ⟨50666298788867305263562705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67555065051823073684750273 50666298788867305263562705)
      ·
        refine ⟨37999724091650478947672029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50666298788867305263562705 37999724091650478947672029)
        ·
          refine ⟨14249896534368929605377011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37999724091650478947672029 14249896534368929605377011)
          ·
            refine ⟨21374844801553394408065517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14249896534368929605377011 21374844801553394408065517)
            ·
              refine ⟨8015566800582522903024569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21374844801553394408065517 8015566800582522903024569)
              ·
                refine ⟨6011675100436892177268427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8015566800582522903024569 6011675100436892177268427)
                ·
                  refine ⟨9017512650655338265902641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6011675100436892177268427 9017512650655338265902641)
                  ·
                    refine ⟨6763134487991503699426981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9017512650655338265902641 6763134487991503699426981)
                    ·
                      refine ⟨1268087716498406943642559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6763134487991503699426981 1268087716498406943642559)
                      ·
                        rfl

theorem cell23_2469592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2469592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469592 prefixEnd_2469592 := by exact prefixLift 2469592
  have htrace : WordTrace (prefixWord ++ tailWord_2469592) baseStart_2469592 baseEnd_2469592 := by
    simpa [prefixWord, tailWord_2469592, baseEnd_2469592] using wordTrace_append hprefix tailTrace_2469592
  have hstable : (prefixWord ++ tailWord_2469592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469592).length < 2 ^ (prefixWord ++ tailWord_2469592).sum := by decide
  have hdescent : baseEnd_2469592 < baseStart_2469592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469607 : List Nat := [1, 1, 5, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2469607 : Nat := 118140960795 + 2469607 * 2 ^ 59
def prefixEnd_2469607 : Nat := 4983230072969 + 3 ^ 40 * 2469607 * 2
def baseEnd_2469607 : Nat := 1268095418708224384954991

theorem tailTrace_2469607 : CollatzResearch.WordTrace tailWord_2469607 prefixEnd_2469607 1268095418708224384954991 := by
  unfold tailWord_2469607
  simp only [CollatzResearch.WordTrace]
  refine ⟨90073967164043089141463075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60049311442695392760975383 90073967164043089141463075)
  ·
    refine ⟨135110950746064633712194613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90073967164043089141463075 135110950746064633712194613)
    ·
      refine ⟨12666651632443559410518245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135110950746064633712194613 12666651632443559410518245)
      ·
        refine ⟨2374997181083167389472171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12666651632443559410518245 2374997181083167389472171)
        ·
          refine ⟨3562495771624751084208257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374997181083167389472171 3562495771624751084208257)
          ·
            refine ⟨2671871828718563313156193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3562495771624751084208257 2671871828718563313156193)
            ·
              refine ⟨2003903871538922484867145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2671871828718563313156193 2003903871538922484867145)
              ·
                refine ⟨1502927903654191863650359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003903871538922484867145 1502927903654191863650359)
                ·
                  refine ⟨2254391855481287795475539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502927903654191863650359 2254391855481287795475539)
                  ·
                    refine ⟨3381587783221931693213309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2254391855481287795475539 3381587783221931693213309)
                    ·
                      refine ⟨1268095418708224384954991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3381587783221931693213309 1268095418708224384954991)
                      ·
                        rfl

theorem cell23_2469607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2469607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469607 prefixEnd_2469607 := by exact prefixLift 2469607
  have htrace : WordTrace (prefixWord ++ tailWord_2469607) baseStart_2469607 baseEnd_2469607 := by
    simpa [prefixWord, tailWord_2469607, baseEnd_2469607] using wordTrace_append hprefix tailTrace_2469607
  have hstable : (prefixWord ++ tailWord_2469607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469607).length < 2 ^ (prefixWord ++ tailWord_2469607).sum := by decide
  have hdescent : baseEnd_2469607 < baseStart_2469607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469615 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 1, 9]
def baseStart_2469615 : Nat := 118140960795 + 2469615 * 2 ^ 59
def prefixEnd_2469615 : Nat := 4983230072969 + 3 ^ 40 * 2469615 * 2
def baseEnd_2469615 : Nat := 422699842184486784551651

theorem tailTrace_2469615 : CollatzResearch.WordTrace tailWord_2469615 prefixEnd_2469615 422699842184486784551651 := by
  unfold tailWord_2469615
  simp only [CollatzResearch.WordTrace]
  refine ⟨90074258948014106507754299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60049505965342737671836199 90074258948014106507754299)
  ·
    refine ⟨135111388422021159761631449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90074258948014106507754299 135111388422021159761631449)
    ·
      refine ⟨101333541316515869821223587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135111388422021159761631449 101333541316515869821223587)
      ·
        refine ⟨152000311974773804731835381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101333541316515869821223587 152000311974773804731835381)
        ·
          refine ⟨14250029247635044193609567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152000311974773804731835381 14250029247635044193609567)
          ·
            refine ⟨21375043871452566290414351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14250029247635044193609567 21375043871452566290414351)
            ·
              refine ⟨32062565807178849435621527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21375043871452566290414351 32062565807178849435621527)
              ·
                refine ⟨48093848710768274153432291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32062565807178849435621527 48093848710768274153432291)
                ·
                  refine ⟨72140773066152411230148437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48093848710768274153432291 72140773066152411230148437)
                  ·
                    refine ⟨422699842184486784551651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 72140773066152411230148437 422699842184486784551651)
                    ·
                      rfl

theorem cell23_2469615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_2469615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469615 prefixEnd_2469615 := by exact prefixLift 2469615
  have htrace : WordTrace (prefixWord ++ tailWord_2469615) baseStart_2469615 baseEnd_2469615 := by
    simpa [prefixWord, tailWord_2469615, baseEnd_2469615] using wordTrace_append hprefix tailTrace_2469615
  have hstable : (prefixWord ++ tailWord_2469615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469615).length < 2 ^ (prefixWord ++ tailWord_2469615).sum := by decide
  have hdescent : baseEnd_2469615 < baseStart_2469615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469625 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_2469625 : Nat := 118140960795 + 2469625 * 2 ^ 59
def prefixEnd_2469625 : Nat := 4983230072969 + 3 ^ 40 * 2469625 * 2
def baseEnd_2469625 : Nat := 1268104661360005314529907

theorem tailTrace_2469625 : CollatzResearch.WordTrace tailWord_2469625 prefixEnd_2469625 1268104661360005314529907 := by
  unfold tailWord_2469625
  simp only [CollatzResearch.WordTrace]
  refine ⟨90074623677977878215618329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60049749118651918810412219 90074623677977878215618329)
  ·
    refine ⟨67555967758483408661713747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90074623677977878215618329 67555967758483408661713747)
    ·
      refine ⟨101333951637725112992570621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67555967758483408661713747 101333951637725112992570621)
      ·
        refine ⟨38000231864146917372213983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101333951637725112992570621 38000231864146917372213983)
        ·
          refine ⟨57000347796220376058320975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38000231864146917372213983 57000347796220376058320975)
          ·
            refine ⟨85500521694330564087481463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57000347796220376058320975 85500521694330564087481463)
            ·
              refine ⟨128250782541495846131222195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85500521694330564087481463 128250782541495846131222195)
              ·
                refine ⟨192376173812243769196833293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128250782541495846131222195 192376173812243769196833293)
                ·
                  refine ⟨72141065179591413448812485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192376173812243769196833293 72141065179591413448812485)
                  ·
                    refine ⟨13526449721173390021652341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72141065179591413448812485 13526449721173390021652341)
                    ·
                      refine ⟨1268104661360005314529907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13526449721173390021652341 1268104661360005314529907)
                      ·
                        rfl

theorem cell23_2469625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_2469625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469625 prefixEnd_2469625 := by exact prefixLift 2469625
  have htrace : WordTrace (prefixWord ++ tailWord_2469625) baseStart_2469625 baseEnd_2469625 := by
    simpa [prefixWord, tailWord_2469625, baseEnd_2469625] using wordTrace_append hprefix tailTrace_2469625
  have hstable : (prefixWord ++ tailWord_2469625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469625).length < 2 ^ (prefixWord ++ tailWord_2469625).sum := by decide
  have hdescent : baseEnd_2469625 < baseStart_2469625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469650 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_2469650 : Nat := 118140960795 + 2469650 * 2 ^ 59
def prefixEnd_2469650 : Nat := 4983230072969 + 3 ^ 40 * 2469650 * 2
def baseEnd_2469650 : Nat := 1268117498376367716717293

theorem tailTrace_2469650 : CollatzResearch.WordTrace tailWord_2469650 prefixEnd_2469650 1268117498376367716717293 := by
  unfold tailWord_2469650
  simp only [CollatzResearch.WordTrace]
  refine ⟨22518883875721826871319601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60050357001924871656852269 22518883875721826871319601)
  ·
    refine ⟨16889162906791370153489701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22518883875721826871319601 16889162906791370153489701)
    ·
      refine ⟨3166718045023381903779319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16889162906791370153489701 3166718045023381903779319)
      ·
        refine ⟨4750077067535072855668979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3166718045023381903779319 4750077067535072855668979)
        ·
          refine ⟨7125115601302609283503469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4750077067535072855668979 7125115601302609283503469)
          ·
            refine ⟨2671918350488478481313801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7125115601302609283503469 2671918350488478481313801)
            ·
              refine ⟨2003938762866358860985351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2671918350488478481313801 2003938762866358860985351)
              ·
                refine ⟨3005908144299538291478027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003938762866358860985351 3005908144299538291478027)
                ·
                  refine ⟨4508862216449307437217041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005908144299538291478027 4508862216449307437217041)
                  ·
                    refine ⟨3381646662336980577912781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4508862216449307437217041 3381646662336980577912781)
                    ·
                      refine ⟨1268117498376367716717293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3381646662336980577912781 1268117498376367716717293)
                      ·
                        rfl

theorem cell23_2469650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_2469650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469650 prefixEnd_2469650 := by exact prefixLift 2469650
  have htrace : WordTrace (prefixWord ++ tailWord_2469650) baseStart_2469650 baseEnd_2469650 := by
    simpa [prefixWord, tailWord_2469650, baseEnd_2469650] using wordTrace_append hprefix tailTrace_2469650
  have hstable : (prefixWord ++ tailWord_2469650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469650).length < 2 ^ (prefixWord ++ tailWord_2469650).sum := by decide
  have hdescent : baseEnd_2469650 < baseStart_2469650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469692 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 7]
def baseStart_2469692 : Nat := 118140960795 + 2469692 * 2 ^ 59
def prefixEnd_2469692 : Nat := 4983230072969 + 3 ^ 40 * 2469692 * 2
def baseEnd_2469692 : Nat := 140904340507095172488011

theorem tailTrace_2469692 : CollatzResearch.WordTrace tailWord_2469692 prefixEnd_2469692 140904340507095172488011 := by
  unfold tailWord_2469692
  simp only [CollatzResearch.WordTrace]
  refine ⟨45038533684367574329153665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60051378245823432438871553 45038533684367574329153665)
  ·
    refine ⟨33778900263275680746865249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45038533684367574329153665 33778900263275680746865249)
    ·
      refine ⟨25334175197456760560148937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33778900263275680746865249 25334175197456760560148937)
      ·
        refine ⟨19000631398092570420111703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25334175197456760560148937 19000631398092570420111703)
        ·
          refine ⟨28500947097138855630167555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19000631398092570420111703 28500947097138855630167555)
          ·
            refine ⟨42751420645708283445251333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28500947097138855630167555 42751420645708283445251333)
            ·
              refine ⟨8015891371070303145984625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42751420645708283445251333 8015891371070303145984625)
              ·
                refine ⟨6011918528302727359488469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8015891371070303145984625 6011918528302727359488469)
                ·
                  refine ⟨140904340507095172488011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6011918528302727359488469 140904340507095172488011)
                  ·
                    rfl

theorem cell23_2469692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_2469692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469692 prefixEnd_2469692 := by exact prefixLift 2469692
  have htrace : WordTrace (prefixWord ++ tailWord_2469692) baseStart_2469692 baseEnd_2469692 := by
    simpa [prefixWord, tailWord_2469692, baseEnd_2469692] using wordTrace_append hprefix tailTrace_2469692
  have hstable : (prefixWord ++ tailWord_2469692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469692).length < 2 ^ (prefixWord ++ tailWord_2469692).sum := by decide
  have hdescent : baseEnd_2469692 < baseStart_2469692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469729 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 2, 5, 2]
def baseStart_2469729 : Nat := 118140960795 + 2469729 * 2 ^ 59
def prefixEnd_2469729 : Nat := 4983230072969 + 3 ^ 40 * 2469729 * 2
def baseEnd_2469729 : Nat := 1268158063348072907629429

theorem tailTrace_2469729 : CollatzResearch.WordTrace tailWord_2469729 prefixEnd_2469729 1268158063348072907629429 := by
  unfold tailWord_2469729
  simp only [CollatzResearch.WordTrace]
  refine ⟨90078416869601103977404241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60052277913067402651602827 90078416869601103977404241)
  ·
    refine ⟨67558812652200827983053181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90078416869601103977404241 67558812652200827983053181)
    ·
      refine ⟨25334554744575310493644943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67558812652200827983053181 25334554744575310493644943)
      ·
        refine ⟨38001832116862965740467415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25334554744575310493644943 38001832116862965740467415)
        ·
          refine ⟨57002748175294448610701123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38001832116862965740467415 57002748175294448610701123)
          ·
            refine ⟨85504122262941672916051685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57002748175294448610701123 85504122262941672916051685)
            ·
              refine ⟨16032022924301563671759691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85504122262941672916051685 16032022924301563671759691)
              ·
                refine ⟨24048034386452345507639537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16032022924301563671759691 24048034386452345507639537)
                ·
                  refine ⟨18036025789839259130729653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24048034386452345507639537 18036025789839259130729653)
                  ·
                    refine ⟨1690877417797430543505905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18036025789839259130729653 1690877417797430543505905)
                    ·
                      refine ⟨1268158063348072907629429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1690877417797430543505905 1268158063348072907629429)
                      ·
                        rfl

theorem cell23_2469729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_2469729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469729 prefixEnd_2469729 := by exact prefixLift 2469729
  have htrace : WordTrace (prefixWord ++ tailWord_2469729) baseStart_2469729 baseEnd_2469729 := by
    simpa [prefixWord, tailWord_2469729, baseEnd_2469729] using wordTrace_append hprefix tailTrace_2469729
  have hstable : (prefixWord ++ tailWord_2469729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469729).length < 2 ^ (prefixWord ++ tailWord_2469729).sum := by decide
  have hdescent : baseEnd_2469729 < baseStart_2469729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469759 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 4, 4, 2]
def baseStart_2469759 : Nat := 118140960795 + 2469759 * 2 ^ 59
def prefixEnd_2469759 : Nat := 4983230072969 + 3 ^ 40 * 2469759 * 2
def baseEnd_2469759 : Nat := 1268173467767707790254291

theorem tailTrace_2469759 : CollatzResearch.WordTrace tailWord_2469759 prefixEnd_2469759 1268173467767707790254291 := by
  unfold tailWord_2469759
  simp only [CollatzResearch.WordTrace]
  refine ⟨90079511059492419100996331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60053007372994946067330887 90079511059492419100996331)
  ·
    refine ⟨135119266589238628651494497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90079511059492419100996331 135119266589238628651494497)
    ·
      refine ⟨101339449941928971488620873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135119266589238628651494497 101339449941928971488620873)
      ·
        refine ⟨76004587456446728616465655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101339449941928971488620873 76004587456446728616465655)
        ·
          refine ⟨114006881184670092924698483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76004587456446728616465655 114006881184670092924698483)
          ·
            refine ⟨171010321777005139387047725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114006881184670092924698483 171010321777005139387047725)
            ·
              refine ⟨64128870666376927270142897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171010321777005139387047725 64128870666376927270142897)
              ·
                refine ⟨48096652999782695452607173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64128870666376927270142897 48096652999782695452607173)
                ·
                  refine ⟨9018122437459255397363845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48096652999782695452607173 9018122437459255397363845)
                  ·
                    refine ⟨1690897957023610387005721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9018122437459255397363845 1690897957023610387005721)
                    ·
                      refine ⟨1268173467767707790254291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1690897957023610387005721 1268173467767707790254291)
                      ·
                        rfl

theorem cell23_2469759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 4, 2].length) (baseStart_2469759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469759 prefixEnd_2469759 := by exact prefixLift 2469759
  have htrace : WordTrace (prefixWord ++ tailWord_2469759) baseStart_2469759 baseEnd_2469759 := by
    simpa [prefixWord, tailWord_2469759, baseEnd_2469759] using wordTrace_append hprefix tailTrace_2469759
  have hstable : (prefixWord ++ tailWord_2469759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469759).length < 2 ^ (prefixWord ++ tailWord_2469759).sum := by decide
  have hdescent : baseEnd_2469759 < baseStart_2469759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469772 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2469772 : Nat := 118140960795 + 2469772 * 2 ^ 59
def prefixEnd_2469772 : Nat := 4983230072969 + 3 ^ 40 * 2469772 * 2
def baseEnd_2469772 : Nat := 1268180143016216239391731

theorem tailTrace_2469772 : CollatzResearch.WordTrace tailWord_2469772 prefixEnd_2469772 1268180143016216239391731 := by
  unfold tailWord_2469772
  simp only [CollatzResearch.WordTrace]
  refine ⟨45039992604222661160609785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60053323472296881547479713 45039992604222661160609785)
  ·
    refine ⟨33779994453166995870457339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45039992604222661160609785 33779994453166995870457339)
    ·
      refine ⟨50669991679750493805686009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33779994453166995870457339 50669991679750493805686009)
      ·
        refine ⟨38002493759812870354264507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50669991679750493805686009 38002493759812870354264507)
        ·
          refine ⟨57003740639719305531396761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38002493759812870354264507 57003740639719305531396761)
          ·
            refine ⟨42752805479789479148547571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57003740639719305531396761 42752805479789479148547571)
            ·
              refine ⟨64129208219684218722821357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42752805479789479148547571 64129208219684218722821357)
              ·
                refine ⟨24048453082381582021058009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64129208219684218722821357 24048453082381582021058009)
                ·
                  refine ⟨18036339811786186515793507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24048453082381582021058009 18036339811786186515793507)
                  ·
                    refine ⟨27054509717679279773690261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18036339811786186515793507 27054509717679279773690261)
                    ·
                      refine ⟨1268180143016216239391731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27054509717679279773690261 1268180143016216239391731)
                      ·
                        rfl

theorem cell23_2469772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2469772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469772 prefixEnd_2469772 := by exact prefixLift 2469772
  have htrace : WordTrace (prefixWord ++ tailWord_2469772) baseStart_2469772 baseEnd_2469772 := by
    simpa [prefixWord, tailWord_2469772, baseEnd_2469772] using wordTrace_append hprefix tailTrace_2469772
  have hstable : (prefixWord ++ tailWord_2469772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469772).length < 2 ^ (prefixWord ++ tailWord_2469772).sum := by decide
  have hdescent : baseEnd_2469772 < baseStart_2469772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469793 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2469793 : Nat := 118140960795 + 2469793 * 2 ^ 59
def prefixEnd_2469793 : Nat := 4983230072969 + 3 ^ 40 * 2469793 * 2
def baseEnd_2469793 : Nat := 1268190926109960657229135

theorem tailTrace_2469793 : CollatzResearch.WordTrace tailWord_2469793 prefixEnd_2469793 1268190926109960657229135 := by
  unfold tailWord_2469793
  simp only [CollatzResearch.WordTrace]
  refine ⟨90080751141369242907734033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60053834094246161938489355 90080751141369242907734033)
  ·
    refine ⟨67560563356026932180800525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90080751141369242907734033 67560563356026932180800525)
    ·
      refine ⟨25335211258510099567800197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67560563356026932180800525 25335211258510099567800197)
      ·
        refine ⟨4750352110970643668962537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25335211258510099567800197 4750352110970643668962537)
        ·
          refine ⟨3562764083227982751721903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4750352110970643668962537 3562764083227982751721903)
          ·
            refine ⟨5344146124841974127582855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562764083227982751721903 5344146124841974127582855)
            ·
              refine ⟨8016219187262961191374283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5344146124841974127582855 8016219187262961191374283)
              ·
                refine ⟨12024328780894441787061425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8016219187262961191374283 12024328780894441787061425)
                ·
                  refine ⟨9018246585670831340296069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12024328780894441787061425 9018246585670831340296069)
                  ·
                    refine ⟨1690921234813280876305513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9018246585670831340296069 1690921234813280876305513)
                    ·
                      refine ⟨1268190926109960657229135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1690921234813280876305513 1268190926109960657229135)
                      ·
                        rfl

theorem cell23_2469793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2469793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469793 prefixEnd_2469793 := by exact prefixLift 2469793
  have htrace : WordTrace (prefixWord ++ tailWord_2469793) baseStart_2469793 baseEnd_2469793 := by
    simpa [prefixWord, tailWord_2469793, baseEnd_2469793] using wordTrace_append hprefix tailTrace_2469793
  have hstable : (prefixWord ++ tailWord_2469793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469793).length < 2 ^ (prefixWord ++ tailWord_2469793).sum := by decide
  have hdescent : baseEnd_2469793 < baseStart_2469793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469813 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_2469813 : Nat := 118140960795 + 2469813 * 2 ^ 59
def prefixEnd_2469813 : Nat := 4983230072969 + 3 ^ 40 * 2469813 * 2
def baseEnd_2469813 : Nat := 1268201195723050578979043

theorem tailTrace_2469813 : CollatzResearch.WordTrace tailWord_2469813 prefixEnd_2469813 1268201195723050578979043 := by
  unfold tailWord_2469813
  simp only [CollatzResearch.WordTrace]
  refine ⟨90081480601296786323462093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60054320400864524215641395 90081480601296786323462093)
  ·
    refine ⟨33780555225486294871298285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90081480601296786323462093 33780555225486294871298285)
    ·
      refine ⟨12667708209557360576736857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33780555225486294871298285 12667708209557360576736857)
      ·
        refine ⟨9500781157168020432552643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12667708209557360576736857 9500781157168020432552643)
        ·
          refine ⟨14251171735752030648828965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9500781157168020432552643 14251171735752030648828965)
          ·
            refine ⟨2672094700453505746655431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14251171735752030648828965 2672094700453505746655431)
            ·
              refine ⟨4008142050680258619983147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2672094700453505746655431 4008142050680258619983147)
              ·
                refine ⟨6012213076020387929974721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4008142050680258619983147 6012213076020387929974721)
                ·
                  refine ⟨4509159807015290947481041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6012213076020387929974721 4509159807015290947481041)
                  ·
                    refine ⟨3381869855261468210610781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4509159807015290947481041 3381869855261468210610781)
                    ·
                      refine ⟨1268201195723050578979043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3381869855261468210610781 1268201195723050578979043)
                      ·
                        rfl

theorem cell23_2469813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_2469813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469813 prefixEnd_2469813 := by exact prefixLift 2469813
  have htrace : WordTrace (prefixWord ++ tailWord_2469813) baseStart_2469813 baseEnd_2469813 := by
    simpa [prefixWord, tailWord_2469813, baseEnd_2469813] using wordTrace_append hprefix tailTrace_2469813
  have hstable : (prefixWord ++ tailWord_2469813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469813).length < 2 ^ (prefixWord ++ tailWord_2469813).sum := by decide
  have hdescent : baseEnd_2469813 < baseStart_2469813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469863 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 1, 5]
def baseStart_2469863 : Nat := 118140960795 + 2469863 * 2 ^ 59
def prefixEnd_2469863 : Nat := 4983230072969 + 3 ^ 40 * 2469863 * 2
def baseEnd_2469863 : Nat := 422742289918591794451271

theorem tailTrace_2469863 : CollatzResearch.WordTrace tailWord_2469863 prefixEnd_2469863 422742289918591794451271 := by
  unfold tailWord_2469863
  simp only [CollatzResearch.WordTrace]
  refine ⟨90083304251115644862782243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60055536167410429908521495 90083304251115644862782243)
  ·
    refine ⟨135124956376673467294173365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90083304251115644862782243 135124956376673467294173365)
    ·
      refine ⟨12667964660313137558828753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135124956376673467294173365 12667964660313137558828753)
      ·
        refine ⟨9500973495234853169121565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12667964660313137558828753 9500973495234853169121565)
        ·
          refine ⟨3562865060713069938420587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9500973495234853169121565 3562865060713069938420587)
          ·
            refine ⟨5344297591069604907630881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562865060713069938420587 5344297591069604907630881)
            ·
              refine ⟨4008223193302203680723161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5344297591069604907630881 4008223193302203680723161)
              ·
                refine ⟨3006167394976652760542371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4008223193302203680723161 3006167394976652760542371)
                ·
                  refine ⟨4509251092464979140813557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006167394976652760542371 4509251092464979140813557)
                  ·
                    refine ⟨422742289918591794451271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4509251092464979140813557 422742289918591794451271)
                    ·
                      rfl

theorem cell23_2469863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_2469863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469863 prefixEnd_2469863 := by exact prefixLift 2469863
  have htrace : WordTrace (prefixWord ++ tailWord_2469863) baseStart_2469863 baseEnd_2469863 := by
    simpa [prefixWord, tailWord_2469863, baseEnd_2469863] using wordTrace_append hprefix tailTrace_2469863
  have hstable : (prefixWord ++ tailWord_2469863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469863).length < 2 ^ (prefixWord ++ tailWord_2469863).sum := by decide
  have hdescent : baseEnd_2469863 < baseStart_2469863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469866 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_2469866 : Nat := 118140960795 + 2469866 * 2 ^ 59
def prefixEnd_2469866 : Nat := 4983230072969 + 3 ^ 40 * 2469866 * 2
def baseEnd_2469866 : Nat := 1268228410197738871616299

theorem tailTrace_2469866 : CollatzResearch.WordTrace tailWord_2469866 prefixEnd_2469866 1268228410197738871616299 := by
  unfold tailWord_2469866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22520853417526194093785363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60055609113403184250094301 22520853417526194093785363)
  ·
    refine ⟨33781280126289291140678045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22520853417526194093785363 33781280126289291140678045)
    ·
      refine ⟨12667980047358484177754267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33781280126289291140678045 12667980047358484177754267)
      ·
        refine ⟨19001970071037726266631401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12667980047358484177754267 19001970071037726266631401)
        ·
          refine ⟨14251477553278294699973551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19001970071037726266631401 14251477553278294699973551)
          ·
            refine ⟨21377216329917442049960327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14251477553278294699973551 21377216329917442049960327)
            ·
              refine ⟨32065824494876163074940491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21377216329917442049960327 32065824494876163074940491)
              ·
                refine ⟨48098736742314244612410737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32065824494876163074940491 48098736742314244612410737)
                ·
                  refine ⟨36074052556735683459308053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48098736742314244612410737 36074052556735683459308053)
                  ·
                    refine ⟨1690971213596985162155065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36074052556735683459308053 1690971213596985162155065)
                    ·
                      refine ⟨1268228410197738871616299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1690971213596985162155065 1268228410197738871616299)
                      ·
                        rfl

theorem cell23_2469866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_2469866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469866 prefixEnd_2469866 := by exact prefixLift 2469866
  have htrace : WordTrace (prefixWord ++ tailWord_2469866) baseStart_2469866 baseEnd_2469866 := by
    simpa [prefixWord, tailWord_2469866, baseEnd_2469866] using wordTrace_append hprefix tailTrace_2469866
  have hstable : (prefixWord ++ tailWord_2469866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469866).length < 2 ^ (prefixWord ++ tailWord_2469866).sum := by decide
  have hdescent : baseEnd_2469866 < baseStart_2469866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469943 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 1, 3, 2]
def baseStart_2469943 : Nat := 118140960795 + 2469943 * 2 ^ 59
def prefixEnd_2469943 : Nat := 4983230072969 + 3 ^ 40 * 2469943 * 2
def baseEnd_2469943 : Nat := 1268267948208135070353445

theorem tailTrace_2469943 : CollatzResearch.WordTrace tailWord_2469943 prefixEnd_2469943 1268267948208135070353445 := by
  unfold tailWord_2469943
  simp only [CollatzResearch.WordTrace]
  refine ⟨90086222090825818525694483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60057481393883879017129655 90086222090825818525694483)
  ·
    refine ⟨135129333136238727788541725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90086222090825818525694483 135129333136238727788541725)
    ·
      refine ⟨50673499926089522920703147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135129333136238727788541725 50673499926089522920703147)
      ·
        refine ⟨76010249889134284381054721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50673499926089522920703147 76010249889134284381054721)
        ·
          refine ⟨57007687416850713285791041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76010249889134284381054721 57007687416850713285791041)
          ·
            refine ⟨42755765562638034964343281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57007687416850713285791041 42755765562638034964343281)
            ·
              refine ⟨32066824171978526223257461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42755765562638034964343281 32066824171978526223257461)
              ·
                refine ⟨3006264766122986833430387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32066824171978526223257461 3006264766122986833430387)
                ·
                  refine ⟨4509397149184480250145581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006264766122986833430387 4509397149184480250145581)
                  ·
                    refine ⟨1691023930944180093804593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4509397149184480250145581 1691023930944180093804593)
                    ·
                      refine ⟨1268267948208135070353445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691023930944180093804593 1268267948208135070353445)
                      ·
                        rfl

theorem cell23_2469943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 3, 2].length) (baseStart_2469943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469943 prefixEnd_2469943 := by exact prefixLift 2469943
  have htrace : WordTrace (prefixWord ++ tailWord_2469943) baseStart_2469943 baseEnd_2469943 := by
    simpa [prefixWord, tailWord_2469943, baseEnd_2469943] using wordTrace_append hprefix tailTrace_2469943
  have hstable : (prefixWord ++ tailWord_2469943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469943).length < 2 ^ (prefixWord ++ tailWord_2469943).sum := by decide
  have hdescent : baseEnd_2469943 < baseStart_2469943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469966 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_2469966 : Nat := 118140960795 + 2469966 * 2 ^ 59
def prefixEnd_2469966 : Nat := 4983230072969 + 3 ^ 40 * 2469966 * 2
def baseEnd_2469966 : Nat := 422759919421062826788613

theorem tailTrace_2469966 : CollatzResearch.WordTrace tailWord_2469966 prefixEnd_2469966 422759919421062826788613 := by
  unfold tailWord_2469966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11260882621217811681722719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60058040646494995635854501 11260882621217811681722719)
  ·
    refine ⟨16891323931826717522584079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11260882621217811681722719 16891323931826717522584079)
    ·
      refine ⟨25336985897740076283876119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16891323931826717522584079 25336985897740076283876119)
      ·
        refine ⟨38005478846610114425814179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25336985897740076283876119 38005478846610114425814179)
        ·
          refine ⟨57008218269915171638721269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38005478846610114425814179 57008218269915171638721269)
          ·
            refine ⟨5344520462804547341130119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57008218269915171638721269 5344520462804547341130119)
            ·
              refine ⟨8016780694206821011695179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5344520462804547341130119 8016780694206821011695179)
              ·
                refine ⟨12025171041310231517542769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8016780694206821011695179 12025171041310231517542769)
                ·
                  refine ⟨9018878280982673638157077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12025171041310231517542769 9018878280982673638157077)
                  ·
                    refine ⟨422759919421062826788613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9018878280982673638157077 422759919421062826788613)
                    ·
                      rfl

theorem cell23_2469966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_2469966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469966 prefixEnd_2469966 := by exact prefixLift 2469966
  have htrace : WordTrace (prefixWord ++ tailWord_2469966) baseStart_2469966 baseEnd_2469966 := by
    simpa [prefixWord, tailWord_2469966, baseEnd_2469966] using wordTrace_append hprefix tailTrace_2469966
  have hstable : (prefixWord ++ tailWord_2469966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469966).length < 2 ^ (prefixWord ++ tailWord_2469966).sum := by decide
  have hdescent : baseEnd_2469966 < baseStart_2469966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469973 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 1, 4, 2]
def baseStart_2469973 : Nat := 118140960795 + 2469973 * 2 ^ 59
def prefixEnd_2469973 : Nat := 4983230072969 + 3 ^ 40 * 2469973 * 2
def baseEnd_2469973 : Nat := 1268283352627769952978307

theorem tailTrace_2469973 : CollatzResearch.WordTrace tailWord_2469973 prefixEnd_2469973 1268283352627769952978307 := by
  unfold tailWord_2469973
  simp only [CollatzResearch.WordTrace]
  refine ⟨90087316280717133649286573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60058210853811422432857715 90087316280717133649286573)
  ·
    refine ⟨33782743605268925118482465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90087316280717133649286573 33782743605268925118482465)
    ·
      refine ⟨25337057703951693838861849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33782743605268925118482465 25337057703951693838861849)
      ·
        refine ⟨19002793277963770379146387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25337057703951693838861849 19002793277963770379146387)
        ·
          refine ⟨28504189916945655568719581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19002793277963770379146387 28504189916945655568719581)
          ·
            refine ⟨10689071218854620838269843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28504189916945655568719581 10689071218854620838269843)
            ·
              refine ⟨16033606828281931257404765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10689071218854620838269843 16033606828281931257404765)
              ·
                refine ⟨6012602560605724221526787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16033606828281931257404765 6012602560605724221526787)
                ·
                  refine ⟨9018903840908586332290181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6012602560605724221526787 9018903840908586332290181)
                  ·
                    refine ⟨1691044470170359937304409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9018903840908586332290181 1691044470170359937304409)
                    ·
                      refine ⟨1268283352627769952978307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691044470170359937304409 1268283352627769952978307)
                      ·
                        rfl

theorem cell23_2469973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_2469973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469973 prefixEnd_2469973 := by exact prefixLift 2469973
  have htrace : WordTrace (prefixWord ++ tailWord_2469973) baseStart_2469973 baseEnd_2469973 := by
    simpa [prefixWord, tailWord_2469973, baseEnd_2469973] using wordTrace_append hprefix tailTrace_2469973
  have hstable : (prefixWord ++ tailWord_2469973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469973).length < 2 ^ (prefixWord ++ tailWord_2469973).sum := by decide
  have hdescent : baseEnd_2469973 < baseStart_2469973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469994 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_2469994 : Nat := 118140960795 + 2469994 * 2 ^ 59
def prefixEnd_2469994 : Nat := 4983230072969 + 3 ^ 40 * 2469994 * 2
def baseEnd_2469994 : Nat := 1268294135721514370815711

theorem tailTrace_2469994 : CollatzResearch.WordTrace tailWord_2469994 prefixEnd_2469994 1268294135721514370815711 := by
  unfold tailWord_2469994
  simp only [CollatzResearch.WordTrace]
  refine ⟨22522020553410263558950259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60058721475760702823867357 22522020553410263558950259)
  ·
    refine ⟨33783030830115395338425389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22522020553410263558950259 33783030830115395338425389)
    ·
      refine ⟨12668636561293273251909521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33783030830115395338425389 12668636561293273251909521)
      ·
        refine ⟨9501477420969954938932141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12668636561293273251909521 9501477420969954938932141)
        ·
          refine ⟨3563054032863733102099553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9501477420969954938932141 3563054032863733102099553)
          ·
            refine ⟨2672290524647799826574665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3563054032863733102099553 2672290524647799826574665)
            ·
              refine ⟨2004217893485849869930999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672290524647799826574665 2004217893485849869930999)
              ·
                refine ⟨3006326840228774804896499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004217893485849869930999 3006326840228774804896499)
                ·
                  refine ⟨4509490260343162207344749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006326840228774804896499 4509490260343162207344749)
                  ·
                    refine ⟨1691058847628685827754281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4509490260343162207344749 1691058847628685827754281)
                    ·
                      refine ⟨1268294135721514370815711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691058847628685827754281 1268294135721514370815711)
                      ·
                        rfl

theorem cell23_2469994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_2469994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469994 prefixEnd_2469994 := by exact prefixLift 2469994
  have htrace : WordTrace (prefixWord ++ tailWord_2469994) baseStart_2469994 baseEnd_2469994 := by
    simpa [prefixWord, tailWord_2469994, baseEnd_2469994] using wordTrace_append hprefix tailTrace_2469994
  have hstable : (prefixWord ++ tailWord_2469994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469994).length < 2 ^ (prefixWord ++ tailWord_2469994).sum := by decide
  have hdescent : baseEnd_2469994 < baseStart_2469994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470007 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 2, 2, 2]
def baseStart_2470007 : Nat := 118140960795 + 2470007 * 2 ^ 59
def prefixEnd_2470007 : Nat := 4983230072969 + 3 ^ 40 * 2470007 * 2
def baseEnd_2470007 : Nat := 1268300810970022819953151

theorem tailTrace_2470007 : CollatzResearch.WordTrace tailWord_2470007 prefixEnd_2470007 1268300810970022819953151 := by
  unfold tailWord_2470007
  simp only [CollatzResearch.WordTrace]
  refine ⟨90088556362593957456024275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60059037575062638304016183 90088556362593957456024275)
  ·
    refine ⟨135132834543890936184036413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90088556362593957456024275 135132834543890936184036413)
    ·
      refine ⟨50674812953959101069013655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135132834543890936184036413 50674812953959101069013655)
      ·
        refine ⟨76012219430938651603520483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50674812953959101069013655 76012219430938651603520483)
        ·
          refine ⟨114018329146407977405280725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76012219430938651603520483 114018329146407977405280725)
          ·
            refine ⟨2672304589368936970436267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 114018329146407977405280725 2672304589368936970436267)
            ·
              refine ⟨4008456884053405455654401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2672304589368936970436267 4008456884053405455654401)
              ·
                refine ⟨3006342663040054091740801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4008456884053405455654401 3006342663040054091740801)
                ·
                  refine ⟨2254756997280040568805601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3006342663040054091740801 2254756997280040568805601)
                  ·
                    refine ⟨1691067747960030426604201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2254756997280040568805601 1691067747960030426604201)
                    ·
                      refine ⟨1268300810970022819953151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691067747960030426604201 1268300810970022819953151)
                      ·
                        rfl

theorem cell23_2470007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 2, 2].length) (baseStart_2470007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470007 prefixEnd_2470007 := by exact prefixLift 2470007
  have htrace : WordTrace (prefixWord ++ tailWord_2470007) baseStart_2470007 baseEnd_2470007 := by
    simpa [prefixWord, tailWord_2470007, baseEnd_2470007] using wordTrace_append hprefix tailTrace_2470007
  have hstable : (prefixWord ++ tailWord_2470007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470007).length < 2 ^ (prefixWord ++ tailWord_2470007).sum := by decide
  have hdescent : baseEnd_2470007 < baseStart_2470007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470013 : List Nat := [1, 4, 1, 1, 3, 2, 2, 4, 5]
def baseStart_2470013 : Nat := 118140960795 + 2470013 * 2 ^ 59
def prefixEnd_2470013 : Nat := 4983230072969 + 3 ^ 40 * 2470013 * 2
def baseEnd_2470013 : Nat := 140922654650438866275347

theorem tailTrace_2470013 : CollatzResearch.WordTrace tailWord_2470013 prefixEnd_2470013 140922654650438866275347 := by
  unfold tailWord_2470013
  simp only [CollatzResearch.WordTrace]
  refine ⟨90088775200572220480742693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60059183467048146987161795 90088775200572220480742693)
  ·
    refine ⟨16891645350107291340139255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90088775200572220480742693 16891645350107291340139255)
    ·
      refine ⟨25337468025160937010208883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16891645350107291340139255 25337468025160937010208883)
      ·
        refine ⟨38006202037741405515313325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25337468025160937010208883 38006202037741405515313325)
        ·
          refine ⟨14252325764153027068242497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38006202037741405515313325 14252325764153027068242497)
          ·
            refine ⟨10689244323114770301181873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14252325764153027068242497 10689244323114770301181873)
            ·
              refine ⟨8016933242336077725886405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10689244323114770301181873 8016933242336077725886405)
              ·
                refine ⟨1503174982938014573603701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8016933242336077725886405 1503174982938014573603701)
                ·
                  refine ⟨140922654650438866275347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1503174982938014573603701 140922654650438866275347)
                  ·
                    rfl

theorem cell23_2470013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_2470013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470013 prefixEnd_2470013 := by exact prefixLift 2470013
  have htrace : WordTrace (prefixWord ++ tailWord_2470013) baseStart_2470013 baseEnd_2470013 := by
    simpa [prefixWord, tailWord_2470013, baseEnd_2470013] using wordTrace_append hprefix tailTrace_2470013
  have hstable : (prefixWord ++ tailWord_2470013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470013).length < 2 ^ (prefixWord ++ tailWord_2470013).sum := by decide
  have hdescent : baseEnd_2470013 < baseStart_2470013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470024 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 2, 2, 2]
def baseStart_2470024 : Nat := 118140960795 + 2470024 * 2 ^ 59
def prefixEnd_2470024 : Nat := 4983230072969 + 3 ^ 40 * 2470024 * 2
def baseEnd_2470024 : Nat := 1268309540141149253440573

theorem tailTrace_2470024 : CollatzResearch.WordTrace tailWord_2470024 prefixEnd_2470024 1268309540141149253440573 := by
  unfold tailWord_2470024
  simp only [CollatzResearch.WordTrace]
  refine ⟨45044588201766184679696563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60059450935688246239595417 45044588201766184679696563)
  ·
    refine ⟨67566882302649277019544845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45044588201766184679696563 67566882302649277019544845)
    ·
      refine ⟨25337580863493478882329317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67566882302649277019544845 25337580863493478882329317)
      ·
        refine ⟨4750796411905027290436747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25337580863493478882329317 4750796411905027290436747)
        ·
          refine ⟨7126194617857540935655121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4750796411905027290436747 7126194617857540935655121)
          ·
            refine ⟨5344645963393155701741341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7126194617857540935655121 5344645963393155701741341)
            ·
              refine ⟨2004242236272433388153003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5344645963393155701741341 2004242236272433388153003)
              ·
                refine ⟨3006363354408650082229505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004242236272433388153003 3006363354408650082229505)
                ·
                  refine ⟨2254772515806487561672129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3006363354408650082229505 2254772515806487561672129)
                  ·
                    refine ⟨1691079386854865671254097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2254772515806487561672129 1691079386854865671254097)
                    ·
                      refine ⟨1268309540141149253440573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691079386854865671254097 1268309540141149253440573)
                      ·
                        rfl

theorem cell23_2470024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_2470024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470024 prefixEnd_2470024 := by exact prefixLift 2470024
  have htrace : WordTrace (prefixWord ++ tailWord_2470024) baseStart_2470024 baseEnd_2470024 := by
    simpa [prefixWord, tailWord_2470024, baseEnd_2470024] using wordTrace_append hprefix tailTrace_2470024
  have hstable : (prefixWord ++ tailWord_2470024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470024).length < 2 ^ (prefixWord ++ tailWord_2470024).sum := by decide
  have hdescent : baseEnd_2470024 < baseStart_2470024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470026 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_2470026 : Nat := 118140960795 + 2470026 * 2 ^ 59
def prefixEnd_2470026 : Nat := 4983230072969 + 3 ^ 40 * 2470026 * 2
def baseEnd_2470026 : Nat := 422770189034152748538521

theorem tailTrace_2470026 : CollatzResearch.WordTrace tailWord_2470026 prefixEnd_2470026 422770189034152748538521 := by
  unfold tailWord_2470026
  simp only [CollatzResearch.WordTrace]
  refine ⟨22522312337381280925241483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60059499566350082467310621 22522312337381280925241483)
  ·
    refine ⟨33783468506071921387862225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22522312337381280925241483 33783468506071921387862225)
    ·
      refine ⟨25337601379553941040896669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33783468506071921387862225 25337601379553941040896669)
      ·
        refine ⟨9501600517332727890336251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25337601379553941040896669 9501600517332727890336251)
        ·
          refine ⟨14252400775999091835504377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9501600517332727890336251 14252400775999091835504377)
          ·
            refine ⟨10689300581999318876628283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14252400775999091835504377 10689300581999318876628283)
            ·
              refine ⟨16033950872998978314942425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10689300581999318876628283 16033950872998978314942425)
              ·
                refine ⟨12025463154749233736206819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16033950872998978314942425 12025463154749233736206819)
                ·
                  refine ⟨18038194732123850604310229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12025463154749233736206819 18038194732123850604310229)
                  ·
                    refine ⟨422770189034152748538521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18038194732123850604310229 422770189034152748538521)
                    ·
                      rfl

theorem cell23_2470026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_2470026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470026 prefixEnd_2470026 := by exact prefixLift 2470026
  have htrace : WordTrace (prefixWord ++ tailWord_2470026) baseStart_2470026 baseEnd_2470026 := by
    simpa [prefixWord, tailWord_2470026, baseEnd_2470026] using wordTrace_append hprefix tailTrace_2470026
  have hstable : (prefixWord ++ tailWord_2470026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470026).length < 2 ^ (prefixWord ++ tailWord_2470026).sum := by decide
  have hdescent : baseEnd_2470026 < baseStart_2470026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470153 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 4]
def baseStart_2470153 : Nat := 118140960795 + 2470153 * 2 ^ 59
def prefixEnd_2470153 : Nat := 4983230072969 + 3 ^ 40 * 2470153 * 2
def baseEnd_2470153 : Nat := 1268375779145579248727479

theorem tailTrace_2470153 : CollatzResearch.WordTrace tailWord_2470153 prefixEnd_2470153 1268375779145579248727479 := by
  unfold tailWord_2470153
  simp only [CollatzResearch.WordTrace]
  refine ⟨90093881420065024390839113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60062587613376682927226075 90093881420065024390839113)
  ·
    refine ⟨67570411065048768293129335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90093881420065024390839113 67570411065048768293129335)
    ·
      refine ⟨101355616597573152439694003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67570411065048768293129335 101355616597573152439694003)
      ·
        refine ⟨152033424896359728659541005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101355616597573152439694003 152033424896359728659541005)
        ·
          refine ⟨57012534336134898247327877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152033424896359728659541005 57012534336134898247327877)
          ·
            refine ⟨10689850188025293421373977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57012534336134898247327877 10689850188025293421373977)
            ·
              refine ⟨8017387641018970066030483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10689850188025293421373977 8017387641018970066030483)
              ·
                refine ⟨12026081461528455099045725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8017387641018970066030483 12026081461528455099045725)
                ·
                  refine ⟨4509780548073170662142147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12026081461528455099045725 4509780548073170662142147)
                  ·
                    refine ⟨6764670822109755993213221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4509780548073170662142147 6764670822109755993213221)
                    ·
                      refine ⟨1268375779145579248727479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6764670822109755993213221 1268375779145579248727479)
                      ·
                        rfl

theorem cell23_2470153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_2470153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470153 prefixEnd_2470153 := by exact prefixLift 2470153
  have htrace : WordTrace (prefixWord ++ tailWord_2470153) baseStart_2470153 baseEnd_2470153 := by
    simpa [prefixWord, tailWord_2470153, baseEnd_2470153] using wordTrace_append hprefix tailTrace_2470153
  have hstable : (prefixWord ++ tailWord_2470153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470153).length < 2 ^ (prefixWord ++ tailWord_2470153).sum := by decide
  have hdescent : baseEnd_2470153 < baseStart_2470153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470167 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 1, 5]
def baseStart_2470167 : Nat := 118140960795 + 2470167 * 2 ^ 59
def prefixEnd_2470167 : Nat := 4983230072969 + 3 ^ 40 * 2470167 * 2
def baseEnd_2470167 : Nat := 422794322624914064650805

theorem tailTrace_2470167 : CollatzResearch.WordTrace tailWord_2470167 prefixEnd_2470167 422794322624914064650805 := by
  unfold tailWord_2470167
  simp only [CollatzResearch.WordTrace]
  refine ⟨90094392042014304781848755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60062928028009536521232503 90094392042014304781848755)
  ·
    refine ⟨135141588063021457172773133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90094392042014304781848755 135141588063021457172773133)
    ·
      refine ⟨50678095523633046439789925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135141588063021457172773133 50678095523633046439789925)
      ·
        refine ⟨9502142910681196207460611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50678095523633046439789925 9502142910681196207460611)
        ·
          refine ⟨14253214366021794311190917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9502142910681196207460611 14253214366021794311190917)
          ·
            refine ⟨2672477693629086433348297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14253214366021794311190917 2672477693629086433348297)
            ·
              refine ⟨2004358270221814825011223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672477693629086433348297 2004358270221814825011223)
              ·
                refine ⟨3006537405332722237516835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004358270221814825011223 3006537405332722237516835)
                ·
                  refine ⟨4509806107999083356275253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006537405332722237516835 4509806107999083356275253)
                  ·
                    refine ⟨422794322624914064650805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4509806107999083356275253 422794322624914064650805)
                    ·
                      rfl

theorem cell23_2470167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_2470167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470167 prefixEnd_2470167 := by exact prefixLift 2470167
  have htrace : WordTrace (prefixWord ++ tailWord_2470167) baseStart_2470167 baseEnd_2470167 := by
    simpa [prefixWord, tailWord_2470167, baseEnd_2470167] using wordTrace_append hprefix tailTrace_2470167
  have hstable : (prefixWord ++ tailWord_2470167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470167).length < 2 ^ (prefixWord ++ tailWord_2470167).sum := by decide
  have hdescent : baseEnd_2470167 < baseStart_2470167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470180 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_2470180 : Nat := 118140960795 + 2470180 * 2 ^ 59
def prefixEnd_2470180 : Nat := 4983230072969 + 3 ^ 40 * 2470180 * 2
def baseEnd_2470180 : Nat := 422796547707750214363285

theorem tailTrace_2470180 : CollatzResearch.WordTrace tailWord_2470180 prefixEnd_2470180 422796547707750214363285 := by
  unfold tailWord_2470180
  simp only [CollatzResearch.WordTrace]
  refine ⟨45047433095483604001035997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60063244127311472001381329 45047433095483604001035997)
  ·
    refine ⟨16892787410806351500388499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45047433095483604001035997 16892787410806351500388499)
    ·
      refine ⟨25339181116209527250582749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16892787410806351500388499 25339181116209527250582749)
      ·
        refine ⟨9502192918578572718968531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25339181116209527250582749 9502192918578572718968531)
        ·
          refine ⟨14253289377867859078452797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9502192918578572718968531 14253289377867859078452797)
          ·
            refine ⟨5344983516700447154419799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14253289377867859078452797 5344983516700447154419799)
            ·
              refine ⟨8017475275050670731629699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5344983516700447154419799 8017475275050670731629699)
              ·
                refine ⟨12026212912576006097444549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8017475275050670731629699 12026212912576006097444549)
                ·
                  refine ⟨2254914921108001143270853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12026212912576006097444549 2254914921108001143270853)
                  ·
                    refine ⟨422796547707750214363285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2254914921108001143270853 422796547707750214363285)
                    ·
                      rfl

theorem cell23_2470180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_2470180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470180 prefixEnd_2470180 := by exact prefixLift 2470180
  have htrace : WordTrace (prefixWord ++ tailWord_2470180) baseStart_2470180 baseEnd_2470180 := by
    simpa [prefixWord, tailWord_2470180, baseEnd_2470180] using wordTrace_append hprefix tailTrace_2470180
  have hstable : (prefixWord ++ tailWord_2470180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470180).length < 2 ^ (prefixWord ++ tailWord_2470180).sum := by decide
  have hdescent : baseEnd_2470180 < baseStart_2470180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470197 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2470197 : Nat := 118140960795 + 2470197 * 2 ^ 59
def prefixEnd_2470197 : Nat := 4983230072969 + 3 ^ 40 * 2470197 * 2
def baseEnd_2470197 : Nat := 422799457431459025525759

theorem tailTrace_2470197 : CollatzResearch.WordTrace tailWord_2470197 prefixEnd_2470197 422799457431459025525759 := by
  unfold tailWord_2470197
  simp only [CollatzResearch.WordTrace]
  refine ⟨90095486231905619905440845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60063657487937079936960563 90095486231905619905440845)
  ·
    refine ⟨33785807336964607464540317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90095486231905619905440845 33785807336964607464540317)
    ·
      refine ⟨12669677751361727799202619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33785807336964607464540317 12669677751361727799202619)
      ·
        refine ⟨19004516627042591698803929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12669677751361727799202619 19004516627042591698803929)
        ·
          refine ⟨14253387470281943774102947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19004516627042591698803929 14253387470281943774102947)
          ·
            refine ⟨21380081205422915661154421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14253387470281943774102947 21380081205422915661154421)
            ·
              refine ⟨2004382613008398343233227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21380081205422915661154421 2004382613008398343233227)
              ·
                refine ⟨3006573919512597514849841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004382613008398343233227 3006573919512597514849841)
                ·
                  refine ⟨2254930439634448136137381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3006573919512597514849841 2254930439634448136137381)
                  ·
                    refine ⟨422799457431459025525759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2254930439634448136137381 422799457431459025525759)
                    ·
                      rfl

theorem cell23_2470197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2470197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470197 prefixEnd_2470197 := by exact prefixLift 2470197
  have htrace : WordTrace (prefixWord ++ tailWord_2470197) baseStart_2470197 baseEnd_2470197 := by
    simpa [prefixWord, tailWord_2470197, baseEnd_2470197] using wordTrace_append hprefix tailTrace_2470197
  have hstable : (prefixWord ++ tailWord_2470197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470197).length < 2 ^ (prefixWord ++ tailWord_2470197).sum := by decide
  have hdescent : baseEnd_2470197 < baseStart_2470197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470220 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2470220 : Nat := 118140960795 + 2470220 * 2 ^ 59
def prefixEnd_2470220 : Nat := 4983230072969 + 3 ^ 40 * 2470220 * 2
def baseEnd_2470220 : Nat := 1268410182349430486589671

theorem tailTrace_2470220 : CollatzResearch.WordTrace tailWord_2470220 prefixEnd_2470220 1268410182349430486589671 := by
  unfold tailWord_2470220
  simp only [CollatzResearch.WordTrace]
  refine ⟨45048162555411147416764057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60064216740548196555685409 45048162555411147416764057)
  ·
    refine ⟨33786121916558360562573043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45048162555411147416764057 33786121916558360562573043)
    ·
      refine ⟨50679182874837540843859565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33786121916558360562573043 50679182874837540843859565)
      ·
        refine ⟨19004693578064077816447337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50679182874837540843859565 19004693578064077816447337)
        ·
          refine ⟨14253520183548058362335503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19004693578064077816447337 14253520183548058362335503)
          ·
            refine ⟨21380280275322087543503255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14253520183548058362335503 21380280275322087543503255)
            ·
              refine ⟨32070420412983131315254883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21380280275322087543503255 32070420412983131315254883)
              ·
                refine ⟨48105630619474696972882325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32070420412983131315254883 48105630619474696972882325)
                ·
                  refine ⟨2254951435287876420603859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48105630619474696972882325 2254951435287876420603859)
                  ·
                    refine ⟨3382427152931814630905789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2254951435287876420603859 3382427152931814630905789)
                    ·
                      refine ⟨1268410182349430486589671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3382427152931814630905789 1268410182349430486589671)
                      ·
                        rfl

theorem cell23_2470220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2470220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470220 prefixEnd_2470220 := by exact prefixLift 2470220
  have htrace : WordTrace (prefixWord ++ tailWord_2470220) baseStart_2470220 baseEnd_2470220 := by
    simpa [prefixWord, tailWord_2470220, baseEnd_2470220] using wordTrace_append hprefix tailTrace_2470220
  have hstable : (prefixWord ++ tailWord_2470220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470220).length < 2 ^ (prefixWord ++ tailWord_2470220).sum := by decide
  have hdescent : baseEnd_2470220 < baseStart_2470220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470243 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 4]
def baseStart_2470243 : Nat := 118140960795 + 2470243 * 2 ^ 59
def prefixEnd_2470243 : Nat := 4983230072969 + 3 ^ 40 * 2470243 * 2
def baseEnd_2470243 : Nat := 1268421992404483896602065

theorem tailTrace_2470243 : CollatzResearch.WordTrace tailWord_2470243 prefixEnd_2470243 1268421992404483896602065 := by
  unfold tailWord_2470243
  simp only [CollatzResearch.WordTrace]
  refine ⟨90097163989738969761615383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60064775993159313174410255 90097163989738969761615383)
  ·
    refine ⟨135145745984608454642423075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90097163989738969761615383 135145745984608454642423075)
    ·
      refine ⟨202718618976912681963634613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135145745984608454642423075 202718618976912681963634613)
      ·
        refine ⟨19004870529085563934090745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202718618976912681963634613 19004870529085563934090745)
        ·
          refine ⟨14253652896814172950568059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19004870529085563934090745 14253652896814172950568059)
          ·
            refine ⟨21380479345221259425852089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14253652896814172950568059 21380479345221259425852089)
            ·
              refine ⟨16035359508915944569389067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21380479345221259425852089 16035359508915944569389067)
              ·
                refine ⟨24053039263373916854083601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16035359508915944569389067 24053039263373916854083601)
                ·
                  refine ⟨18039779447530437640562701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24053039263373916854083601 18039779447530437640562701)
                  ·
                    refine ⟨6764917292823914115211013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18039779447530437640562701 6764917292823914115211013)
                    ·
                      refine ⟨1268421992404483896602065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6764917292823914115211013 1268421992404483896602065)
                      ·
                        rfl

theorem cell23_2470243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_2470243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470243 prefixEnd_2470243 := by exact prefixLift 2470243
  have htrace : WordTrace (prefixWord ++ tailWord_2470243) baseStart_2470243 baseEnd_2470243 := by
    simpa [prefixWord, tailWord_2470243, baseEnd_2470243] using wordTrace_append hprefix tailTrace_2470243
  have hstable : (prefixWord ++ tailWord_2470243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470243).length < 2 ^ (prefixWord ++ tailWord_2470243).sum := by decide
  have hdescent : baseEnd_2470243 < baseStart_2470243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470253 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_2470253 : Nat := 118140960795 + 2470253 * 2 ^ 59
def prefixEnd_2470253 : Nat := 4983230072969 + 3 ^ 40 * 2470253 * 2
def baseEnd_2470253 : Nat := 422809042403676285825673

theorem tailTrace_2470253 : CollatzResearch.WordTrace tailWord_2470253 prefixEnd_2470253 422809042403676285825673 := by
  unfold tailWord_2470253
  simp only [CollatzResearch.WordTrace]
  refine ⟨90097528719702741469479413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60065019146468494312986275 90097528719702741469479413)
  ·
    refine ⟨8446643317472132012763695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90097528719702741469479413 8446643317472132012763695)
    ·
      refine ⟨12669964976208198019145543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8446643317472132012763695 12669964976208198019145543)
      ·
        refine ⟨19004947464312297028718315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12669964976208198019145543 19004947464312297028718315)
        ·
          refine ⟨28507421196468445543077473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19004947464312297028718315 28507421196468445543077473)
          ·
            refine ⟨21380565897351334157308105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28507421196468445543077473 21380565897351334157308105)
            ·
              refine ⟨16035424423013500617981079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21380565897351334157308105 16035424423013500617981079)
              ·
                refine ⟨24053136634520250926971619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16035424423013500617981079 24053136634520250926971619)
                ·
                  refine ⟨36079704951780376390457429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24053136634520250926971619 36079704951780376390457429)
                  ·
                    refine ⟨422809042403676285825673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36079704951780376390457429 422809042403676285825673)
                    ·
                      rfl

theorem cell23_2470253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2470253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470253 prefixEnd_2470253 := by exact prefixLift 2470253
  have htrace : WordTrace (prefixWord ++ tailWord_2470253) baseStart_2470253 baseEnd_2470253 := by
    simpa [prefixWord, tailWord_2470253, baseEnd_2470253] using wordTrace_append hprefix tailTrace_2470253
  have hstable : (prefixWord ++ tailWord_2470253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470253).length < 2 ^ (prefixWord ++ tailWord_2470253).sum := by decide
  have hdescent : baseEnd_2470253 < baseStart_2470253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470263 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 3]
def baseStart_2470263 : Nat := 118140960795 + 2470263 * 2 ^ 59
def prefixEnd_2470263 : Nat := 4983230072969 + 3 ^ 40 * 2470263 * 2
def baseEnd_2470263 : Nat := 1268432262017573818351973

theorem tailTrace_2470263 : CollatzResearch.WordTrace tailWord_2470263 prefixEnd_2470263 1268432262017573818351973 := by
  unfold tailWord_2470263
  simp only [CollatzResearch.WordTrace]
  refine ⟨90097893449666513177343443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60065262299777675451562295 90097893449666513177343443)
  ·
    refine ⟨135146840174499769766015165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90097893449666513177343443 135146840174499769766015165)
    ·
      refine ⟨50680065065437413662255687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135146840174499769766015165 50680065065437413662255687)
      ·
        refine ⟨76020097598156120493383531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50680065065437413662255687 76020097598156120493383531)
        ·
          refine ⟨114030146397234180740075297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76020097598156120493383531 114030146397234180740075297)
          ·
            refine ⟨85522609797925635555056473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114030146397234180740075297 85522609797925635555056473)
            ·
              refine ⟨64141957348444226666292355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85522609797925635555056473 64141957348444226666292355)
              ·
                refine ⟨96212936022666339999438533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64141957348444226666292355 96212936022666339999438533)
                ·
                  refine ⟨18039925504249938749894725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96212936022666339999438533 18039925504249938749894725)
                  ·
                    refine ⟨3382486032046863515605261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18039925504249938749894725 3382486032046863515605261)
                    ·
                      refine ⟨1268432262017573818351973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3382486032046863515605261 1268432262017573818351973)
                      ·
                        rfl

theorem cell23_2470263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_2470263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470263 prefixEnd_2470263 := by exact prefixLift 2470263
  have htrace : WordTrace (prefixWord ++ tailWord_2470263) baseStart_2470263 baseEnd_2470263 := by
    simpa [prefixWord, tailWord_2470263, baseEnd_2470263] using wordTrace_append hprefix tailTrace_2470263
  have hstable : (prefixWord ++ tailWord_2470263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470263).length < 2 ^ (prefixWord ++ tailWord_2470263).sum := by decide
  have hdescent : baseEnd_2470263 < baseStart_2470263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470313 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 4, 5]
def baseStart_2470313 : Nat := 118140960795 + 2470313 * 2 ^ 59
def prefixEnd_2470313 : Nat := 4983230072969 + 3 ^ 40 * 2470313 * 2
def baseEnd_2470313 : Nat := 422819312016766207575581

theorem tailTrace_2470313 : CollatzResearch.WordTrace tailWord_2470313 prefixEnd_2470313 422819312016766207575581 := by
  unfold tailWord_2470313
  simp only [CollatzResearch.WordTrace]
  refine ⟨90099717099485371716663593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60066478066323581144442395 90099717099485371716663593)
  ·
    refine ⟨67574787824614028787497695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90099717099485371716663593 67574787824614028787497695)
    ·
      refine ⟨101362181736921043181246543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67574787824614028787497695 101362181736921043181246543)
      ·
        refine ⟨152043272605381564771869815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101362181736921043181246543 152043272605381564771869815)
        ·
          refine ⟨228064908908072347157804723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152043272605381564771869815 228064908908072347157804723)
          ·
            refine ⟨342097363362108520736707085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228064908908072347157804723 342097363362108520736707085)
            ·
              refine ⟨128286511260790695276265157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 342097363362108520736707085 128286511260790695276265157)
              ·
                refine ⟨24053720861398255364299717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128286511260790695276265157 24053720861398255364299717)
                ·
                  refine ⟨4510072661512172880806197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24053720861398255364299717 4510072661512172880806197)
                  ·
                    refine ⟨422819312016766207575581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4510072661512172880806197 422819312016766207575581)
                    ·
                      rfl

theorem cell23_2470313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_2470313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470313 prefixEnd_2470313 := by exact prefixLift 2470313
  have htrace : WordTrace (prefixWord ++ tailWord_2470313) baseStart_2470313 baseEnd_2470313 := by
    simpa [prefixWord, tailWord_2470313, baseEnd_2470313] using wordTrace_append hprefix tailTrace_2470313
  have hstable : (prefixWord ++ tailWord_2470313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470313).length < 2 ^ (prefixWord ++ tailWord_2470313).sum := by decide
  have hdescent : baseEnd_2470313 < baseStart_2470313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470317 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 7]
def baseStart_2470317 : Nat := 118140960795 + 2470317 * 2 ^ 59
def prefixEnd_2470317 : Nat := 4983230072969 + 3 ^ 40 * 2470317 * 2
def baseEnd_2470317 : Nat := 140939998885879623008525

theorem tailTrace_2470317 : CollatzResearch.WordTrace tailWord_2470317 prefixEnd_2470317 140939998885879623008525 := by
  unfold tailWord_2470317
  simp only [CollatzResearch.WordTrace]
  refine ⟨90099862991470880399809205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60066575327647253599872803 90099862991470880399809205)
  ·
    refine ⟨8446862155450395037482113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90099862991470880399809205 8446862155450395037482113)
    ·
      refine ⟨6335146616587796278111585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8446862155450395037482113 6335146616587796278111585)
      ·
        refine ⟨4751359962440847208583689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6335146616587796278111585 4751359962440847208583689)
        ·
          refine ⟨3563519971830635406437767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4751359962440847208583689 3563519971830635406437767)
          ·
            refine ⟨5345279957745953109656651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563519971830635406437767 5345279957745953109656651)
            ·
              refine ⟨8017919936618929664484977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5345279957745953109656651 8017919936618929664484977)
              ·
                refine ⟨6013439952464197248363733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8017919936618929664484977 6013439952464197248363733)
                ·
                  refine ⟨140939998885879623008525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6013439952464197248363733 140939998885879623008525)
                  ·
                    rfl

theorem cell23_2470317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_2470317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470317 prefixEnd_2470317 := by exact prefixLift 2470317
  have htrace : WordTrace (prefixWord ++ tailWord_2470317) baseStart_2470317 baseEnd_2470317 := by
    simpa [prefixWord, tailWord_2470317, baseEnd_2470317] using wordTrace_append hprefix tailTrace_2470317
  have hstable : (prefixWord ++ tailWord_2470317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470317).length < 2 ^ (prefixWord ++ tailWord_2470317).sum := by decide
  have hdescent : baseEnd_2470317 < baseStart_2470317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470350 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_2470350 : Nat := 118140960795 + 2470350 * 2 ^ 59
def prefixEnd_2470350 : Nat := 4983230072969 + 3 ^ 40 * 2470350 * 2
def baseEnd_2470350 : Nat := 1268476934834514977964073

theorem tailTrace_2470350 : CollatzResearch.WordTrace tailWord_2470350 prefixEnd_2470350 1268476934834514977964073 := by
  unfold tailWord_2470350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11262633325043915879470063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60067377733567551357173669 11262633325043915879470063)
  ·
    refine ⟨16893949987565873819205095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11262633325043915879470063 16893949987565873819205095)
    ·
      refine ⟨25340924981348810728807643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16893949987565873819205095 25340924981348810728807643)
      ·
        refine ⟨38011387472023216093211465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25340924981348810728807643 38011387472023216093211465)
        ·
          refine ⟨28508540604017412069908599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38011387472023216093211465 28508540604017412069908599)
          ·
            refine ⟨42762810906026118104862899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28508540604017412069908599 42762810906026118104862899)
            ·
              refine ⟨64144216359039177157294349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42762810906026118104862899 64144216359039177157294349)
              ·
                refine ⟨24054081134639691433985381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64144216359039177157294349 24054081134639691433985381)
                ·
                  refine ⟨4510140212744942143872259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24054081134639691433985381 4510140212744942143872259)
                  ·
                    refine ⟨6765210319117413215808389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4510140212744942143872259 6765210319117413215808389)
                    ·
                      refine ⟨1268476934834514977964073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6765210319117413215808389 1268476934834514977964073)
                      ·
                        rfl

theorem cell23_2470350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_2470350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470350 prefixEnd_2470350 := by exact prefixLift 2470350
  have htrace : WordTrace (prefixWord ++ tailWord_2470350) baseStart_2470350 baseEnd_2470350 := by
    simpa [prefixWord, tailWord_2470350, baseEnd_2470350] using wordTrace_append hprefix tailTrace_2470350
  have hstable : (prefixWord ++ tailWord_2470350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470350).length < 2 ^ (prefixWord ++ tailWord_2470350).sum := by decide
  have hdescent : baseEnd_2470350 < baseStart_2470350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470353 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_2470353 : Nat := 118140960795 + 2470353 * 2 ^ 59
def prefixEnd_2470353 : Nat := 4983230072969 + 3 ^ 40 * 2470353 * 2
def baseEnd_2470353 : Nat := 1268478475276478466226559

theorem tailTrace_2470353 : CollatzResearch.WordTrace tailWord_2470353 prefixEnd_2470353 1268478475276478466226559 := by
  unfold tailWord_2470353
  simp only [CollatzResearch.WordTrace]
  refine ⟨90101176019340458548119713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60067450679560305698746475 90101176019340458548119713)
  ·
    refine ⟨67575882014505343911089785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90101176019340458548119713 67575882014505343911089785)
    ·
      refine ⟨50681911510879007933317339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67575882014505343911089785 50681911510879007933317339)
      ·
        refine ⟨76022867266318511899976009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50681911510879007933317339 76022867266318511899976009)
        ·
          refine ⟨57017150449738883924982007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76022867266318511899976009 57017150449738883924982007)
          ·
            refine ⟨85525725674608325887473011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57017150449738883924982007 85525725674608325887473011)
            ·
              refine ⟨128288588511912488831209517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85525725674608325887473011 128288588511912488831209517)
              ·
                refine ⟨48108220691967183311703569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128288588511912488831209517 48108220691967183311703569)
                ·
                  refine ⟨36081165518975387483777677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48108220691967183311703569 36081165518975387483777677)
                  ·
                    refine ⟨13530437069615770306416629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36081165518975387483777677 13530437069615770306416629)
                    ·
                      refine ⟨1268478475276478466226559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13530437069615770306416629 1268478475276478466226559)
                      ·
                        rfl

theorem cell23_2470353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_2470353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470353 prefixEnd_2470353 := by exact prefixLift 2470353
  have htrace : WordTrace (prefixWord ++ tailWord_2470353) baseStart_2470353 baseEnd_2470353 := by
    simpa [prefixWord, tailWord_2470353, baseEnd_2470353] using wordTrace_append hprefix tailTrace_2470353
  have hstable : (prefixWord ++ tailWord_2470353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470353).length < 2 ^ (prefixWord ++ tailWord_2470353).sum := by decide
  have hdescent : baseEnd_2470353 < baseStart_2470353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470367 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 2, 4, 2]
def baseStart_2470367 : Nat := 118140960795 + 2470367 * 2 ^ 59
def prefixEnd_2470367 : Nat := 4983230072969 + 3 ^ 40 * 2470367 * 2
def baseEnd_2470367 : Nat := 1268485664005641411451495

theorem tailTrace_2470367 : CollatzResearch.WordTrace tailWord_2470367 prefixEnd_2470367 1268485664005641411451495 := by
  unfold tailWord_2470367
  simp only [CollatzResearch.WordTrace]
  refine ⟨90101686641289738939129355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60067791094193159292752903 90101686641289738939129355)
  ·
    refine ⟨135152529961934608408694033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90101686641289738939129355 135152529961934608408694033)
    ·
      refine ⟨101364397471450956306520525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135152529961934608408694033 101364397471450956306520525)
      ·
        refine ⟨38011649051794108614945197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101364397471450956306520525 38011649051794108614945197)
        ·
          refine ⟨14254368394422790730604449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38011649051794108614945197 14254368394422790730604449)
          ·
            refine ⟨10690776295817093047953337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14254368394422790730604449 10690776295817093047953337)
            ·
              refine ⟨8018082221862819785965003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10690776295817093047953337 8018082221862819785965003)
              ·
                refine ⟨12027123332794229678947505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8018082221862819785965003 12027123332794229678947505)
                ·
                  refine ⟨9020342499595672259210629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12027123332794229678947505 9020342499595672259210629)
                  ·
                    refine ⟨1691314218674188548601993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9020342499595672259210629 1691314218674188548601993)
                    ·
                      refine ⟨1268485664005641411451495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691314218674188548601993 1268485664005641411451495)
                      ·
                        rfl

theorem cell23_2470367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_2470367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470367 prefixEnd_2470367 := by exact prefixLift 2470367
  have htrace : WordTrace (prefixWord ++ tailWord_2470367) baseStart_2470367 baseEnd_2470367 := by
    simpa [prefixWord, tailWord_2470367, baseEnd_2470367] using wordTrace_append hprefix tailTrace_2470367
  have hstable : (prefixWord ++ tailWord_2470367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470367).length < 2 ^ (prefixWord ++ tailWord_2470367).sum := by decide
  have hdescent : baseEnd_2470367 < baseStart_2470367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470390 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2470390 : Nat := 118140960795 + 2470390 * 2 ^ 59
def prefixEnd_2470390 : Nat := 4983230072969 + 3 ^ 40 * 2470390 * 2
def baseEnd_2470390 : Nat := 140944163784521646829321

theorem tailTrace_2470390 : CollatzResearch.WordTrace tailWord_2470390 prefixEnd_2470390 140944163784521646829321 := by
  unfold tailWord_2470390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5631407845012900866701039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60068350346804275911477749 5631407845012900866701039)
  ·
    refine ⟨8447111767519351300051559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5631407845012900866701039 8447111767519351300051559)
    ·
      refine ⟨12670667651279026950077339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8447111767519351300051559 12670667651279026950077339)
      ·
        refine ⟨19006001476918540425116009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12670667651279026950077339 19006001476918540425116009)
        ·
          refine ⟨14254501107688905318837007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19006001476918540425116009 14254501107688905318837007)
          ·
            refine ⟨21381751661533357978255511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14254501107688905318837007 21381751661533357978255511)
            ·
              refine ⟨32072627492300036967383267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21381751661533357978255511 32072627492300036967383267)
              ·
                refine ⟨48108941238450055451074901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32072627492300036967383267 48108941238450055451074901)
                ·
                  refine ⟨140944163784521646829321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 48108941238450055451074901 140944163784521646829321)
                  ·
                    rfl

theorem cell23_2470390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2470390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470390 prefixEnd_2470390 := by exact prefixLift 2470390
  have htrace : WordTrace (prefixWord ++ tailWord_2470390) baseStart_2470390 baseEnd_2470390 := by
    simpa [prefixWord, tailWord_2470390, baseEnd_2470390] using wordTrace_append hprefix tailTrace_2470390
  have hstable : (prefixWord ++ tailWord_2470390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470390).length < 2 ^ (prefixWord ++ tailWord_2470390).sum := by decide
  have hdescent : baseEnd_2470390 < baseStart_2470390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470404 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2470404 : Nat := 118140960795 + 2470404 * 2 ^ 59
def prefixEnd_2470404 : Nat := 4983230072969 + 3 ^ 40 * 2470404 * 2
def baseEnd_2470404 : Nat := 1268504662789857766688825

theorem tailTrace_2470404 : CollatzResearch.WordTrace tailWord_2470404 prefixEnd_2470404 1268504662789857766688825 := by
  unfold tailWord_2470404
  simp only [CollatzResearch.WordTrace]
  refine ⟨45051518071077847129113133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60068690761437129505484177 45051518071077847129113133)
  ·
    refine ⟨16894319276654192673417425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45051518071077847129113133 16894319276654192673417425)
    ·
      refine ⟨12670739457490644505063069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16894319276654192673417425 12670739457490644505063069)
      ·
        refine ⟨4751527296558991689398651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12670739457490644505063069 4751527296558991689398651)
        ·
          refine ⟨7127290944838487534097977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4751527296558991689398651 7127290944838487534097977)
          ·
            refine ⟨5345468208628865650573483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7127290944838487534097977 5345468208628865650573483)
            ·
              refine ⟨8018202312943298475860225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5345468208628865650573483 8018202312943298475860225)
              ·
                refine ⟨6013651734707473856895169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8018202312943298475860225 6013651734707473856895169)
                ·
                  refine ⟨4510238801030605392671377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6013651734707473856895169 4510238801030605392671377)
                  ·
                    refine ⟨3382679100772954044503533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4510238801030605392671377 3382679100772954044503533)
                    ·
                      refine ⟨1268504662789857766688825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3382679100772954044503533 1268504662789857766688825)
                      ·
                        rfl

theorem cell23_2470404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2470404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470404 prefixEnd_2470404 := by exact prefixLift 2470404
  have htrace : WordTrace (prefixWord ++ tailWord_2470404) baseStart_2470404 baseEnd_2470404 := by
    simpa [prefixWord, tailWord_2470404, baseEnd_2470404] using wordTrace_append hprefix tailTrace_2470404
  have hstable : (prefixWord ++ tailWord_2470404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470404).length < 2 ^ (prefixWord ++ tailWord_2470404).sum := by decide
  have hdescent : baseEnd_2470404 < baseStart_2470404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470411 : List Nat := [1, 1, 1, 1, 7, 2, 3, 2, 1, 4]
def baseStart_2470411 : Nat := 118140960795 + 2470411 * 2 ^ 59
def prefixEnd_2470411 : Nat := 4983230072969 + 3 ^ 40 * 2470411 * 2
def baseEnd_2470411 : Nat := 422836085718146413100431

theorem tailTrace_2470411 : CollatzResearch.WordTrace tailWord_2470411 prefixEnd_2470411 422836085718146413100431 := by
  unfold tailWord_2470411
  simp only [CollatzResearch.WordTrace]
  refine ⟨90103291453130334453731087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60068860968753556302487391 90103291453130334453731087)
  ·
    refine ⟨135154937179695501680596631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90103291453130334453731087 135154937179695501680596631)
    ·
      refine ⟨202732405769543252520894947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135154937179695501680596631 202732405769543252520894947)
      ·
        refine ⟨304098608654314878781342421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202732405769543252520894947 304098608654314878781342421)
        ·
          refine ⟨7127311140335504971437713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 304098608654314878781342421 7127311140335504971437713)
          ·
            refine ⟨5345483355251628728578285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7127311140335504971437713 5345483355251628728578285)
            ·
              refine ⟨2004556258219360773216857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5345483355251628728578285 2004556258219360773216857)
              ·
                refine ⟨1503417193664520579912643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2004556258219360773216857 1503417193664520579912643)
                ·
                  refine ⟨2255125790496780869868965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1503417193664520579912643 2255125790496780869868965)
                  ·
                    refine ⟨422836085718146413100431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2255125790496780869868965 422836085718146413100431)
                    ·
                      rfl

theorem cell23_2470411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 1, 4].length) (baseStart_2470411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470411 prefixEnd_2470411 := by exact prefixLift 2470411
  have htrace : WordTrace (prefixWord ++ tailWord_2470411) baseStart_2470411 baseEnd_2470411 := by
    simpa [prefixWord, tailWord_2470411, baseEnd_2470411] using wordTrace_append hprefix tailTrace_2470411
  have hstable : (prefixWord ++ tailWord_2470411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470411).length < 2 ^ (prefixWord ++ tailWord_2470411).sum := by decide
  have hdescent : baseEnd_2470411 < baseStart_2470411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470417 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 3, 1, 3]
def baseStart_2470417 : Nat := 118140960795 + 2470417 * 2 ^ 59
def prefixEnd_2470417 : Nat := 4983230072969 + 3 ^ 40 * 2470417 * 2
def baseEnd_2470417 : Nat := 1268511338038366215826265

theorem tailTrace_2470417 : CollatzResearch.WordTrace tailWord_2470417 prefixEnd_2470417 1268511338038366215826265 := by
  unfold tailWord_2470417
  simp only [CollatzResearch.WordTrace]
  refine ⟨90103510291108597478449505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60069006860739064985633003 90103510291108597478449505)
  ·
    refine ⟨67577632718331448108837129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90103510291108597478449505 67577632718331448108837129)
    ·
      refine ⟨50683224538748586081627847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67577632718331448108837129 50683224538748586081627847)
      ·
        refine ⟨76024836808122879122441771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50683224538748586081627847 76024836808122879122441771)
        ·
          refine ⟨114037255212184318683662657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76024836808122879122441771 114037255212184318683662657)
          ·
            refine ⟨85527941409138239012746993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114037255212184318683662657 85527941409138239012746993)
            ·
              refine ⟨64145956056853679259560245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85527941409138239012746993 64145956056853679259560245)
              ·
                refine ⟨6013683380330032430583773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64145956056853679259560245 6013683380330032430583773)
                ·
                  refine ⟨2255131267623762161468915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6013683380330032430583773 2255131267623762161468915)
                  ·
                    refine ⟨3382696901435643242203373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2255131267623762161468915 3382696901435643242203373)
                    ·
                      refine ⟨1268511338038366215826265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3382696901435643242203373 1268511338038366215826265)
                      ·
                        rfl

theorem cell23_2470417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_2470417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470417 prefixEnd_2470417 := by exact prefixLift 2470417
  have htrace : WordTrace (prefixWord ++ tailWord_2470417) baseStart_2470417 baseEnd_2470417 := by
    simpa [prefixWord, tailWord_2470417, baseEnd_2470417] using wordTrace_append hprefix tailTrace_2470417
  have hstable : (prefixWord ++ tailWord_2470417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470417).length < 2 ^ (prefixWord ++ tailWord_2470417).sum := by decide
  have hdescent : baseEnd_2470417 < baseStart_2470417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470424 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 6]
def baseStart_2470424 : Nat := 118140960795 + 2470424 * 2 ^ 59
def prefixEnd_2470424 : Nat := 4983230072969 + 3 ^ 40 * 2470424 * 2
def baseEnd_2470424 : Nat := 140946103600327520937637

theorem tailTrace_2470424 : CollatzResearch.WordTrace tailWord_2470424 prefixEnd_2470424 140946103600327520937637 := by
  unfold tailWord_2470424
  simp only [CollatzResearch.WordTrace]
  refine ⟨45051882801041618836977163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60069177068055491782636217 45051882801041618836977163)
  ·
    refine ⟨67577824201562428255465745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45051882801041618836977163 67577824201562428255465745)
    ·
      refine ⟨50683368151171821191599309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67577824201562428255465745 50683368151171821191599309)
      ·
        refine ⟨19006263056689432946849741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50683368151171821191599309 19006263056689432946849741)
        ·
          refine ⟨7127348646258537355068653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19006263056689432946849741 7127348646258537355068653)
          ·
            refine ⟨2672755742346951508150745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7127348646258537355068653 2672755742346951508150745)
            ·
              refine ⟨2004566806760213631113059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672755742346951508150745 2004566806760213631113059)
              ·
                refine ⟨3006850210140320446669589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004566806760213631113059 3006850210140320446669589)
                ·
                  refine ⟨140946103600327520937637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3006850210140320446669589 140946103600327520937637)
                  ·
                    rfl

theorem cell23_2470424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 6].length) (baseStart_2470424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470424 prefixEnd_2470424 := by exact prefixLift 2470424
  have htrace : WordTrace (prefixWord ++ tailWord_2470424) baseStart_2470424 baseEnd_2470424 := by
    simpa [prefixWord, tailWord_2470424, baseEnd_2470424] using wordTrace_append hprefix tailTrace_2470424
  have hstable : (prefixWord ++ tailWord_2470424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470424).length < 2 ^ (prefixWord ++ tailWord_2470424).sum := by decide
  have hdescent : baseEnd_2470424 < baseStart_2470424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470437 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 1, 5]
def baseStart_2470437 : Nat := 118140960795 + 2470437 * 2 ^ 59
def prefixEnd_2470437 : Nat := 4983230072969 + 3 ^ 40 * 2470437 * 2
def baseEnd_2470437 : Nat := 422840535883818712525391

theorem tailTrace_2470437 : CollatzResearch.WordTrace tailWord_2470437 prefixEnd_2470437 422840535883818712525391 := by
  unfold tailWord_2470437
  simp only [CollatzResearch.WordTrace]
  refine ⟨90104239751036140894177565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60069493167357427262785043 90104239751036140894177565)
  ·
    refine ⟨33789089906638552835316587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90104239751036140894177565 33789089906638552835316587)
    ·
      refine ⟨50683634859957829252974881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33789089906638552835316587 50683634859957829252974881)
      ·
        refine ⟨38012726144968371939731161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50683634859957829252974881 38012726144968371939731161)
        ·
          refine ⟨28509544608726278954798371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38012726144968371939731161 28509544608726278954798371)
          ·
            refine ⟨42764316913089418432197557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28509544608726278954798371 42764316913089418432197557)
            ·
              refine ⟨4009154710602132978018521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42764316913089418432197557 4009154710602132978018521)
              ·
                refine ⟨3006866032951599733513891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4009154710602132978018521 3006866032951599733513891)
                ·
                  refine ⟨4510299049427399600270837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006866032951599733513891 4510299049427399600270837)
                  ·
                    refine ⟨422840535883818712525391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4510299049427399600270837 422840535883818712525391)
                    ·
                      rfl

theorem cell23_2470437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_2470437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470437 prefixEnd_2470437 := by exact prefixLift 2470437
  have htrace : WordTrace (prefixWord ++ tailWord_2470437) baseStart_2470437 baseEnd_2470437 := by
    simpa [prefixWord, tailWord_2470437, baseEnd_2470437] using wordTrace_append hprefix tailTrace_2470437
  have hstable : (prefixWord ++ tailWord_2470437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470437).length < 2 ^ (prefixWord ++ tailWord_2470437).sum := by decide
  have hdescent : baseEnd_2470437 < baseStart_2470437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470450 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_2470450 : Nat := 118140960795 + 2470450 * 2 ^ 59
def prefixEnd_2470450 : Nat := 4983230072969 + 3 ^ 40 * 2470450 * 2
def baseEnd_2470450 : Nat := 422842760966654862237871

theorem tailTrace_2470450 : CollatzResearch.WordTrace tailWord_2470450 prefixEnd_2470450 422842760966654862237871 := by
  unfold tailWord_2470450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22526178474997261028600201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60069809266659362742933869 22526178474997261028600201)
  ·
    refine ⟨16894633856247945771450151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22526178474997261028600201 16894633856247945771450151)
    ·
      refine ⟨25341950784371918657175227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16894633856247945771450151 25341950784371918657175227)
      ·
        refine ⟨38012926176557877985762841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25341950784371918657175227 38012926176557877985762841)
        ·
          refine ⟨28509694632418408489322131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38012926176557877985762841 28509694632418408489322131)
          ·
            refine ⟨42764541948627612733983197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28509694632418408489322131 42764541948627612733983197)
            ·
              refine ⟨16036703230735354775243699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42764541948627612733983197 16036703230735354775243699)
              ·
                refine ⟨24055054846103032162865549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16036703230735354775243699 24055054846103032162865549)
                ·
                  refine ⟨9020645567288637061074581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24055054846103032162865549 9020645567288637061074581)
                  ·
                    refine ⟨422842760966654862237871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9020645567288637061074581 422842760966654862237871)
                    ·
                      rfl

theorem cell23_2470450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_2470450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470450 prefixEnd_2470450 := by exact prefixLift 2470450
  have htrace : WordTrace (prefixWord ++ tailWord_2470450) baseStart_2470450 baseEnd_2470450 := by
    simpa [prefixWord, tailWord_2470450, baseEnd_2470450] using wordTrace_append hprefix tailTrace_2470450
  have hstable : (prefixWord ++ tailWord_2470450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470450).length < 2 ^ (prefixWord ++ tailWord_2470450).sum := by decide
  have hdescent : baseEnd_2470450 < baseStart_2470450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470462 : List Nat := [4, 2, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2470462 : Nat := 118140960795 + 2470462 * 2 ^ 59
def prefixEnd_2470462 : Nat := 4983230072969 + 3 ^ 40 * 2470462 * 2
def baseEnd_2470462 : Nat := 422844814889272846587853

theorem tailTrace_2470462 : CollatzResearch.WordTrace tailWord_2470462 prefixEnd_2470462 422844814889272846587853 := by
  unfold tailWord_2470462
  simp only [CollatzResearch.WordTrace]
  refine ⟨11263143946993196270479705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60070101050630380109225093 11263143946993196270479705)
  ·
    refine ⟨8447357960244897202859779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11263143946993196270479705 8447357960244897202859779)
    ·
      refine ⟨12671036940367345804289669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8447357960244897202859779 12671036940367345804289669)
      ·
        refine ⟨2375819426318877338304313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12671036940367345804289669 2375819426318877338304313)
        ·
          refine ⟨1781864569739158003728235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2375819426318877338304313 1781864569739158003728235)
          ·
            refine ⟨2672796854608737005592353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781864569739158003728235 2672796854608737005592353)
            ·
              refine ⟨2004597640956552754194265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672796854608737005592353 2004597640956552754194265)
              ·
                refine ⟨1503448230717414565645699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2004597640956552754194265 1503448230717414565645699)
                ·
                  refine ⟨2255172346076121848468549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1503448230717414565645699 2255172346076121848468549)
                  ·
                    refine ⟨422844814889272846587853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2255172346076121848468549 422844814889272846587853)
                    ·
                      rfl

theorem cell23_2470462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2470462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470462 prefixEnd_2470462 := by exact prefixLift 2470462
  have htrace : WordTrace (prefixWord ++ tailWord_2470462) baseStart_2470462 baseEnd_2470462 := by
    simpa [prefixWord, tailWord_2470462, baseEnd_2470462] using wordTrace_append hprefix tailTrace_2470462
  have hstable : (prefixWord ++ tailWord_2470462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470462).length < 2 ^ (prefixWord ++ tailWord_2470462).sum := by decide
  have hdescent : baseEnd_2470462 < baseStart_2470462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470484 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_2470484 : Nat := 118140960795 + 2470484 * 2 ^ 59
def prefixEnd_2470484 : Nat := 4983230072969 + 3 ^ 40 * 2470484 * 2
def baseEnd_2470484 : Nat := 422848580414072484562819

theorem tailTrace_2470484 : CollatzResearch.WordTrace tailWord_2470484 prefixEnd_2470484 422848580414072484562819 := by
  unfold tailWord_2470484
  simp only [CollatzResearch.WordTrace]
  refine ⟨45052976990932933960569253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60070635987910578614092337 45052976990932933960569253)
  ·
    refine ⟨8447433185799925117606735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45052976990932933960569253 8447433185799925117606735)
    ·
      refine ⟨12671149778699887676410103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8447433185799925117606735 12671149778699887676410103)
      ·
        refine ⟨19006724668049831514615155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12671149778699887676410103 19006724668049831514615155)
        ·
          refine ⟨28510087002074747271922733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19006724668049831514615155 28510087002074747271922733)
          ·
            refine ⟨10691282625778030226971025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28510087002074747271922733 10691282625778030226971025)
            ·
              refine ⟨8018461969333522670228269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10691282625778030226971025 8018461969333522670228269)
              ·
                refine ⟨3006923238500071001335601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8018461969333522670228269 3006923238500071001335601)
                ·
                  refine ⟨2255192428875053251001701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3006923238500071001335601 2255192428875053251001701)
                  ·
                    refine ⟨422848580414072484562819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2255192428875053251001701 422848580414072484562819)
                    ·
                      rfl

theorem cell23_2470484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_2470484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470484 prefixEnd_2470484 := by exact prefixLift 2470484
  have htrace : WordTrace (prefixWord ++ tailWord_2470484) baseStart_2470484 baseEnd_2470484 := by
    simpa [prefixWord, tailWord_2470484, baseEnd_2470484] using wordTrace_append hprefix tailTrace_2470484
  have hstable : (prefixWord ++ tailWord_2470484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470484).length < 2 ^ (prefixWord ++ tailWord_2470484).sum := by decide
  have hdescent : baseEnd_2470484 < baseStart_2470484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470487 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 4]
def baseStart_2470487 : Nat := 118140960795 + 2470487 * 2 ^ 59
def prefixEnd_2470487 : Nat := 4983230072969 + 3 ^ 40 * 2470487 * 2
def baseEnd_2470487 : Nat := 1268547281684180941950943

theorem tailTrace_2470487 : CollatzResearch.WordTrace tailWord_2470487 prefixEnd_2470487 1268547281684180941950943 := by
  unfold tailWord_2470487
  simp only [CollatzResearch.WordTrace]
  refine ⟨90106063400854999433497715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60070708933903332955665143 90106063400854999433497715)
  ·
    refine ⟨135159095101282499150246573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90106063400854999433497715 135159095101282499150246573)
    ·
      refine ⟨50684660662980937181342465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135159095101282499150246573 50684660662980937181342465)
      ·
        refine ⟨38013495497235702886006849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50684660662980937181342465 38013495497235702886006849)
        ·
          refine ⟨28510121622926777164505137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38013495497235702886006849 28510121622926777164505137)
          ·
            refine ⟨21382591217195082873378853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28510121622926777164505137 21382591217195082873378853)
            ·
              refine ⟨4009235853224078038758535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21382591217195082873378853 4009235853224078038758535)
              ·
                refine ⟨6013853779836117058137803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4009235853224078038758535 6013853779836117058137803)
                ·
                  refine ⟨9020780669754175587206705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6013853779836117058137803 9020780669754175587206705)
                  ·
                    refine ⟨6765585502315631690405029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9020780669754175587206705 6765585502315631690405029)
                    ·
                      refine ⟨1268547281684180941950943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6765585502315631690405029 1268547281684180941950943)
                      ·
                        rfl

theorem cell23_2470487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_2470487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470487 prefixEnd_2470487 := by exact prefixLift 2470487
  have htrace : WordTrace (prefixWord ++ tailWord_2470487) baseStart_2470487 baseEnd_2470487 := by
    simpa [prefixWord, tailWord_2470487, baseEnd_2470487] using wordTrace_append hprefix tailTrace_2470487
  have hstable : (prefixWord ++ tailWord_2470487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470487).length < 2 ^ (prefixWord ++ tailWord_2470487).sum := by decide
  have hdescent : baseEnd_2470487 < baseStart_2470487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470497 : List Nat := [1, 2, 3, 1, 1, 5, 3, 7]
def baseStart_2470497 : Nat := 118140960795 + 2470497 * 2 ^ 59
def prefixEnd_2470497 : Nat := 4983230072969 + 3 ^ 40 * 2470497 * 2
def baseEnd_2470497 : Nat := 46983422832989848252811

theorem tailTrace_2470497 : CollatzResearch.WordTrace tailWord_2470497 prefixEnd_2470497 46983422832989848252811 := by
  unfold tailWord_2470497
  simp only [CollatzResearch.WordTrace]
  refine ⟨90106428130818771141361745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60070952087212514094241163 90106428130818771141361745)
  ·
    refine ⟨67579821098114078356021309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90106428130818771141361745 67579821098114078356021309)
    ·
      refine ⟨25342432911792779383507991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67579821098114078356021309 25342432911792779383507991)
      ·
        refine ⟨38013649367689169075261987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25342432911792779383507991 38013649367689169075261987)
        ·
          refine ⟨57020474051533753612892981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38013649367689169075261987 57020474051533753612892981)
          ·
            refine ⟨5345669442331289401208717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57020474051533753612892981 5345669442331289401208717)
            ·
              refine ⟨2004626040874233525453269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5345669442331289401208717 2004626040874233525453269)
              ·
                refine ⟨46983422832989848252811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2004626040874233525453269 46983422832989848252811)
                ·
                  rfl

theorem cell23_2470497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 7].length) (baseStart_2470497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470497 prefixEnd_2470497 := by exact prefixLift 2470497
  have htrace : WordTrace (prefixWord ++ tailWord_2470497) baseStart_2470497 baseEnd_2470497 := by
    simpa [prefixWord, tailWord_2470497, baseEnd_2470497] using wordTrace_append hprefix tailTrace_2470497
  have hstable : (prefixWord ++ tailWord_2470497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470497).length < 2 ^ (prefixWord ++ tailWord_2470497).sum := by decide
  have hdescent : baseEnd_2470497 < baseStart_2470497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470518 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_2470518 : Nat := 118140960795 + 2470518 * 2 ^ 59
def prefixEnd_2470518 : Nat := 4983230072969 + 3 ^ 40 * 2470518 * 2
def baseEnd_2470518 : Nat := 422854399861490106887767

theorem tailTrace_2470518 : CollatzResearch.WordTrace tailWord_2470518 prefixEnd_2470518 422854399861490106887767 := by
  unfold tailWord_2470518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5631699628983918232992263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60071462709161794485250805 5631699628983918232992263)
  ·
    refine ⟨8447549443475877349488395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5631699628983918232992263 8447549443475877349488395)
    ·
      refine ⟨12671324165213816024232593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8447549443475877349488395 12671324165213816024232593)
      ·
        refine ⟨9503493123910362018174445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12671324165213816024232593 9503493123910362018174445)
        ·
          refine ⟨3563809921466385756815417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9503493123910362018174445 3563809921466385756815417)
          ·
            refine ⟨2672857441099789317611563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3563809921466385756815417 2672857441099789317611563)
            ·
              refine ⟨4009286161649683976417345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2672857441099789317611563 4009286161649683976417345)
              ·
                refine ⟨3006964621237262982313009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4009286161649683976417345 3006964621237262982313009)
                ·
                  refine ⟨2255223465927947236734757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3006964621237262982313009 2255223465927947236734757)
                  ·
                    refine ⟨422854399861490106887767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2255223465927947236734757 422854399861490106887767)
                    ·
                      rfl

theorem cell23_2470518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_2470518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470518 prefixEnd_2470518 := by exact prefixLift 2470518
  have htrace : WordTrace (prefixWord ++ tailWord_2470518) baseStart_2470518 baseEnd_2470518 := by
    simpa [prefixWord, tailWord_2470518, baseEnd_2470518] using wordTrace_append hprefix tailTrace_2470518
  have hstable : (prefixWord ++ tailWord_2470518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470518).length < 2 ^ (prefixWord ++ tailWord_2470518).sum := by decide
  have hdescent : baseEnd_2470518 < baseStart_2470518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470520 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_2470520 : Nat := 118140960795 + 2470520 * 2 ^ 59
def prefixEnd_2470520 : Nat := 4983230072969 + 3 ^ 40 * 2470520 * 2
def baseEnd_2470520 : Nat := 1268564226545779312838291

theorem tailTrace_2470520 : CollatzResearch.WordTrace tailWord_2470520 prefixEnd_2470520 1268564226545779312838291 := by
  unfold tailWord_2470520
  simp only [CollatzResearch.WordTrace]
  refine ⟨45053633504867723034724507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60071511339823630712966009 45053633504867723034724507)
  ·
    refine ⟨67580450257301584552086761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45053633504867723034724507 67580450257301584552086761)
    ·
      refine ⟨50685337692976188414065071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67580450257301584552086761 50685337692976188414065071)
      ·
        refine ⟨76028006539464282621097607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50685337692976188414065071 76028006539464282621097607)
        ·
          refine ⟨114042009809196423931646411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76028006539464282621097607 114042009809196423931646411)
          ·
            refine ⟨171063014713794635897469617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114042009809196423931646411 171063014713794635897469617)
            ·
              refine ⟨128297261035345976923102213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171063014713794635897469617 128297261035345976923102213)
              ·
                refine ⟨24055736444127370673081665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128297261035345976923102213 24055736444127370673081665)
                ·
                  refine ⟨18041802333095528004811249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24055736444127370673081665 18041802333095528004811249)
                  ·
                    refine ⟨13531351749821646003608437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18041802333095528004811249 13531351749821646003608437)
                    ·
                      refine ⟨1268564226545779312838291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13531351749821646003608437 1268564226545779312838291)
                      ·
                        rfl

theorem cell23_2470520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_2470520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470520 prefixEnd_2470520 := by exact prefixLift 2470520
  have htrace : WordTrace (prefixWord ++ tailWord_2470520) baseStart_2470520 baseEnd_2470520 := by
    simpa [prefixWord, tailWord_2470520, baseEnd_2470520] using wordTrace_append hprefix tailTrace_2470520
  have hstable : (prefixWord ++ tailWord_2470520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470520).length < 2 ^ (prefixWord ++ tailWord_2470520).sum := by decide
  have hdescent : baseEnd_2470520 < baseStart_2470520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470540 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_2470540 : Nat := 118140960795 + 2470540 * 2 ^ 59
def prefixEnd_2470540 : Nat := 4983230072969 + 3 ^ 40 * 2470540 * 2
def baseEnd_2470540 : Nat := 422858165386289744862733

theorem tailTrace_2470540 : CollatzResearch.WordTrace tailWord_2470540 prefixEnd_2470540 422858165386289744862733 := by
  unfold tailWord_2470540
  simp only [CollatzResearch.WordTrace]
  refine ⟨45053998234831494742588537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60071997646441992990118049 45053998234831494742588537)
  ·
    refine ⟨33790498676123621056941403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45053998234831494742588537 33790498676123621056941403)
    ·
      refine ⟨50685748014185431585412105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33790498676123621056941403 50685748014185431585412105)
      ·
        refine ⟨38014311010639073689059079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50685748014185431585412105 38014311010639073689059079)
        ·
          refine ⟨57021466515958610533588619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38014311010639073689059079 57021466515958610533588619)
          ·
            refine ⟨85532199773937915800382929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57021466515958610533588619 85532199773937915800382929)
            ·
              refine ⟨64149149830453436850287197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85532199773937915800382929 64149149830453436850287197)
              ·
                refine ⟨24055931186420038818857699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64149149830453436850287197 24055931186420038818857699)
                ·
                  refine ⟨36083896779630058228286549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24055931186420038818857699 36083896779630058228286549)
                  ·
                    refine ⟨422858165386289744862733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36083896779630058228286549 422858165386289744862733)
                    ·
                      rfl

theorem cell23_2470540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_2470540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470540 prefixEnd_2470540 := by exact prefixLift 2470540
  have htrace : WordTrace (prefixWord ++ tailWord_2470540) baseStart_2470540 baseEnd_2470540 := by
    simpa [prefixWord, tailWord_2470540, baseEnd_2470540] using wordTrace_append hprefix tailTrace_2470540
  have hstable : (prefixWord ++ tailWord_2470540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470540).length < 2 ^ (prefixWord ++ tailWord_2470540).sum := by decide
  have hdescent : baseEnd_2470540 < baseStart_2470540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470551 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 1, 3, 2]
def baseStart_2470551 : Nat := 118140960795 + 2470551 * 2 ^ 59
def prefixEnd_2470551 : Nat := 4983230072969 + 3 ^ 40 * 2470551 * 2
def baseEnd_2470551 : Nat := 1268580144446068691550649

theorem tailTrace_2470551 : CollatzResearch.WordTrace tailWord_2470551 prefixEnd_2470551 1268580144446068691550649 := by
  unfold tailWord_2470551
  simp only [CollatzResearch.WordTrace]
  refine ⟨90108397672623138363827507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60072265115082092242551671 90108397672623138363827507)
  ·
    refine ⟨135162596508934707545741261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90108397672623138363827507 135162596508934707545741261)
    ·
      refine ⟨50685973690850515329652973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135162596508934707545741261 50685973690850515329652973)
      ·
        refine ⟨19007240134068943248619865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50685973690850515329652973 19007240134068943248619865)
        ·
          refine ⟨14255430100551707436464899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19007240134068943248619865 14255430100551707436464899)
          ·
            refine ⟨21383145150827561154697349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14255430100551707436464899 21383145150827561154697349)
            ·
              refine ⟨4009339715780167716505753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21383145150827561154697349 4009339715780167716505753)
              ·
                refine ⟨3007004786835125787379315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4009339715780167716505753 3007004786835125787379315)
                ·
                  refine ⟨4510507180252688681068973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3007004786835125787379315 4510507180252688681068973)
                  ·
                    refine ⟨1691440192594758255400865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4510507180252688681068973 1691440192594758255400865)
                    ·
                      refine ⟨1268580144446068691550649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691440192594758255400865 1268580144446068691550649)
                      ·
                        rfl

theorem cell23_2470551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_2470551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470551 prefixEnd_2470551 := by exact prefixLift 2470551
  have htrace : WordTrace (prefixWord ++ tailWord_2470551) baseStart_2470551 baseEnd_2470551 := by
    simpa [prefixWord, tailWord_2470551, baseEnd_2470551] using wordTrace_append hprefix tailTrace_2470551
  have hstable : (prefixWord ++ tailWord_2470551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470551).length < 2 ^ (prefixWord ++ tailWord_2470551).sum := by decide
  have hdescent : baseEnd_2470551 < baseStart_2470551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470564 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 3, 4, 2]
def baseStart_2470564 : Nat := 118140960795 + 2470564 * 2 ^ 59
def prefixEnd_2470564 : Nat := 4983230072969 + 3 ^ 40 * 2470564 * 2
def baseEnd_2470564 : Nat := 1268586819694577140688089

theorem tailTrace_2470564 : CollatzResearch.WordTrace tailWord_2470564 prefixEnd_2470564 1268586819694577140688089 := by
  unfold tailWord_2470564
  simp only [CollatzResearch.WordTrace]
  refine ⟨45054435910788020792025373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60072581214384027722700497 45054435910788020792025373)
  ·
    refine ⟨16895413466545507797009515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45054435910788020792025373 16895413466545507797009515)
    ·
      refine ⟨25343120199818261695514273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16895413466545507797009515 25343120199818261695514273)
      ·
        refine ⟨19007340149863696271635705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25343120199818261695514273 19007340149863696271635705)
        ·
          refine ⟨14255505112397772203726779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19007340149863696271635705 14255505112397772203726779)
          ·
            refine ⟨21383257668596658305590169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14255505112397772203726779 21383257668596658305590169)
            ·
              refine ⟨16037443251447493729192627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21383257668596658305590169 16037443251447493729192627)
              ·
                refine ⟨24056164877171240593788941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16037443251447493729192627 24056164877171240593788941)
                ·
                  refine ⟨9021061828939215222670853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24056164877171240593788941 9021061828939215222670853)
                  ·
                    refine ⟨1691449092926102854250785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9021061828939215222670853 1691449092926102854250785)
                    ·
                      refine ⟨1268586819694577140688089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1691449092926102854250785 1268586819694577140688089)
                      ·
                        rfl

theorem cell23_2470564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_2470564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2470564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2470564 prefixEnd_2470564 := by exact prefixLift 2470564
  have htrace : WordTrace (prefixWord ++ tailWord_2470564) baseStart_2470564 baseEnd_2470564 := by
    simpa [prefixWord, tailWord_2470564, baseEnd_2470564] using wordTrace_append hprefix tailTrace_2470564
  have hstable : (prefixWord ++ tailWord_2470564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470564).length < 2 ^ (prefixWord ++ tailWord_2470564).sum := by decide
  have hdescent : baseEnd_2470564 < baseStart_2470564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
