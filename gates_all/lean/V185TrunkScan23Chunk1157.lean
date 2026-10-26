import V185TrunkScan23Chunk1156

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6853988 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_6853988 : Nat := 118140960795 + 6853988 * 2 ^ 59
def prefixEnd_6853988 : Nat := 4983230072969 + 3 ^ 40 * 6853988 * 2
def baseEnd_6853988 : Nat := 3519390244148434974129089

theorem tailTrace_6853988 : CollatzResearch.WordTrace tailWord_6853988 prefixEnd_6853988 3519390244148434974129089 := by
  unfold tailWord_6853988
  simp only [CollatzResearch.WordTrace]
  refine ⟨124992739746589759400917309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166656986328786345867889745 124992739746589759400917309)
  ·
    refine ⟨46872277404971159775343991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124992739746589759400917309 46872277404971159775343991)
    ·
      refine ⟨70308416107456739663015987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46872277404971159775343991 70308416107456739663015987)
      ·
        refine ⟨105462624161185109494523981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70308416107456739663015987 105462624161185109494523981)
        ·
          refine ⟨39548484060444416060446493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105462624161185109494523981 39548484060444416060446493)
          ·
            refine ⟨14830681522666656022667435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39548484060444416060446493 14830681522666656022667435)
            ·
              refine ⟨22246022283999984034001153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14830681522666656022667435 22246022283999984034001153)
              ·
                refine ⟨16684516712999988025500865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22246022283999984034001153 16684516712999988025500865)
                ·
                  refine ⟨12513387534749991019125649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16684516712999988025500865 12513387534749991019125649)
                  ·
                    refine ⟨9385040651062493264344237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12513387534749991019125649 9385040651062493264344237)
                    ·
                      refine ⟨3519390244148434974129089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9385040651062493264344237 3519390244148434974129089)
                      ·
                        rfl

theorem cell23_6853988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_6853988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853988 prefixEnd_6853988 := by exact prefixLift 6853988
  have htrace : WordTrace (prefixWord ++ tailWord_6853988) baseStart_6853988 baseEnd_6853988 := by
    simpa [prefixWord, tailWord_6853988, baseEnd_6853988] using wordTrace_append hprefix tailTrace_6853988
  have hstable : (prefixWord ++ tailWord_6853988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853988).length < 2 ^ (prefixWord ++ tailWord_6853988).sum := by decide
  have hdescent : baseEnd_6853988 < baseStart_6853988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854045 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_6854045 : Nat := 118140960795 + 6854045 * 2 ^ 59
def prefixEnd_6854045 : Nat := 4983230072969 + 3 ^ 40 * 6854045 * 2
def baseEnd_6854045 : Nat := 3519419512545741251116327

theorem tailTrace_6854045 : CollatzResearch.WordTrace tailWord_6854045 prefixEnd_6854045 3519419512545741251116327 := by
  unfold tailWord_6854045
  simp only [CollatzResearch.WordTrace]
  refine ⟨249987558453973017536659589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166658372302648678357773059 249987558453973017536659589)
  ·
    refine ⟨46872667210119940788123673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249987558453973017536659589 46872667210119940788123673)
    ·
      refine ⟨35154500407589955591092755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46872667210119940788123673 35154500407589955591092755)
      ·
        refine ⟨52731750611384933386639133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35154500407589955591092755 52731750611384933386639133)
        ·
          refine ⟨19774406479269350019989675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52731750611384933386639133 19774406479269350019989675)
          ·
            refine ⟨29661609718904025029984513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19774406479269350019989675 29661609718904025029984513)
            ·
              refine ⟨22246207289178018772488385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29661609718904025029984513 22246207289178018772488385)
              ·
                refine ⟨16684655466883514079366289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22246207289178018772488385 16684655466883514079366289)
                ·
                  refine ⟨12513491600162635559524717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16684655466883514079366289 12513491600162635559524717)
                  ·
                    refine ⟨4692559350060988334821769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12513491600162635559524717 4692559350060988334821769)
                    ·
                      refine ⟨3519419512545741251116327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4692559350060988334821769 3519419512545741251116327)
                      ·
                        rfl

theorem cell23_6854045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_6854045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854045 prefixEnd_6854045 := by exact prefixLift 6854045
  have htrace : WordTrace (prefixWord ++ tailWord_6854045) baseStart_6854045 baseEnd_6854045 := by
    simpa [prefixWord, tailWord_6854045, baseEnd_6854045] using wordTrace_append hprefix tailTrace_6854045
  have hstable : (prefixWord ++ tailWord_6854045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854045).length < 2 ^ (prefixWord ++ tailWord_6854045).sum := by decide
  have hdescent : baseEnd_6854045 < baseStart_6854045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854046 : List Nat := [4, 3, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_6854046 : Nat := 118140960795 + 6854046 * 2 ^ 59
def prefixEnd_6854046 : Nat := 4983230072969 + 3 ^ 40 * 6854046 * 2
def baseEnd_6854046 : Nat := 1173140008675465249067941

theorem tailTrace_6854046 : CollatzResearch.WordTrace tailWord_6854046 prefixEnd_6854046 1173140008675465249067941 := by
  unfold tailWord_6854046
  simp only [CollatzResearch.WordTrace]
  refine ⟨31248449365871174338430749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166658396617979596471630661 31248449365871174338430749)
  ·
    refine ⟨11718168512201690376911531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31248449365871174338430749 11718168512201690376911531)
    ·
      refine ⟨17577252768302535565367297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11718168512201690376911531 17577252768302535565367297)
      ·
        refine ⟨13182939576226901674025473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17577252768302535565367297 13182939576226901674025473)
        ·
          refine ⟨9887204682170176255519105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13182939576226901674025473 9887204682170176255519105)
          ·
            refine ⟨7415403511627632191639329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9887204682170176255519105 7415403511627632191639329)
            ·
              refine ⟨5561552633720724143729497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415403511627632191639329 5561552633720724143729497)
              ·
                refine ⟨4171164475290543107797123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5561552633720724143729497 4171164475290543107797123)
                ·
                  refine ⟨6256746712935814661695685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4171164475290543107797123 6256746712935814661695685)
                  ·
                    refine ⟨1173140008675465249067941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6256746712935814661695685 1173140008675465249067941)
                    ·
                      rfl

theorem cell23_6854046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_6854046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854046 prefixEnd_6854046 := by exact prefixLift 6854046
  have htrace : WordTrace (prefixWord ++ tailWord_6854046) baseStart_6854046 baseEnd_6854046 := by
    simpa [prefixWord, tailWord_6854046, baseEnd_6854046] using wordTrace_append hprefix tailTrace_6854046
  have hstable : (prefixWord ++ tailWord_6854046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854046).length < 2 ^ (prefixWord ++ tailWord_6854046).sum := by decide
  have hdescent : baseEnd_6854046 < baseStart_6854046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854064 : List Nat := [2, 1, 1, 1, 2, 1, 1, 14]
def baseStart_6854064 : Nat := 118140960795 + 6854064 * 2 ^ 59
def prefixEnd_6854064 : Nat := 4983230072969 + 3 ^ 40 * 6854064 * 2
def baseEnd_6854064 : Nat := 130349232173265802843657

theorem tailTrace_6854064 : CollatzResearch.WordTrace tailWord_6854064 prefixEnd_6854064 130349232173265802843657 := by
  unfold tailWord_6854064
  simp only [CollatzResearch.WordTrace]
  refine ⟨124994125720452091890800623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166658834293936122521067497 124994125720452091890800623)
  ·
    refine ⟨187491188580678137836200935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124994125720452091890800623 187491188580678137836200935)
    ·
      refine ⟨281236782871017206754301403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187491188580678137836200935 281236782871017206754301403)
      ·
        refine ⟨421855174306525810131452105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281236782871017206754301403 421855174306525810131452105)
        ·
          refine ⟨316391380729894357598589079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421855174306525810131452105 316391380729894357598589079)
          ·
            refine ⟨474587071094841536397883619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316391380729894357598589079 474587071094841536397883619)
            ·
              refine ⟨711880606642262304596825429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474587071094841536397883619 711880606642262304596825429)
              ·
                refine ⟨130349232173265802843657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 711880606642262304596825429 130349232173265802843657)
                ·
                  rfl

theorem cell23_6854064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 14].length) (baseStart_6854064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854064 prefixEnd_6854064 := by exact prefixLift 6854064
  have htrace : WordTrace (prefixWord ++ tailWord_6854064) baseStart_6854064 baseEnd_6854064 := by
    simpa [prefixWord, tailWord_6854064, baseEnd_6854064] using wordTrace_append hprefix tailTrace_6854064
  have hstable : (prefixWord ++ tailWord_6854064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854064).length < 2 ^ (prefixWord ++ tailWord_6854064).sum := by decide
  have hdescent : baseEnd_6854064 < baseStart_6854064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854092 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 1, 1, 4]
def baseStart_6854092 : Nat := 118140960795 + 6854092 * 2 ^ 59
def prefixEnd_6854092 : Nat := 4983230072969 + 3 ^ 40 * 6854092 * 2
def baseEnd_6854092 : Nat := 3519443646136502567228611

theorem tailTrace_6854092 : CollatzResearch.WordTrace tailWord_6854092 prefixEnd_6854092 3519443646136502567228611 := by
  unfold tailWord_6854092
  simp only [CollatzResearch.WordTrace]
  refine ⟨124994636342401372281810265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166659515123201829709080353 124994636342401372281810265)
  ·
    refine ⟨93745977256801029211357699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124994636342401372281810265 93745977256801029211357699)
    ·
      refine ⟨140618965885201543817036549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93745977256801029211357699 140618965885201543817036549)
      ·
        refine ⟨26366056103475289465694353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140618965885201543817036549 26366056103475289465694353)
        ·
          refine ⟨19774542077606467099270765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26366056103475289465694353 19774542077606467099270765)
          ·
            refine ⟨7415453279102425162226537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19774542077606467099270765 7415453279102425162226537)
            ·
              refine ⟨5561589959326818871669903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415453279102425162226537 5561589959326818871669903)
              ·
                refine ⟨8342384938990228307504855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5561589959326818871669903 8342384938990228307504855)
                ·
                  refine ⟨12513577408485342461257283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8342384938990228307504855 12513577408485342461257283)
                  ·
                    refine ⟨18770366112728013691885925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12513577408485342461257283 18770366112728013691885925)
                    ·
                      refine ⟨3519443646136502567228611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18770366112728013691885925 3519443646136502567228611)
                      ·
                        rfl

theorem cell23_6854092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_6854092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854092 prefixEnd_6854092 := by exact prefixLift 6854092
  have htrace : WordTrace (prefixWord ++ tailWord_6854092) baseStart_6854092 baseEnd_6854092 := by
    simpa [prefixWord, tailWord_6854092, baseEnd_6854092] using wordTrace_append hprefix tailTrace_6854092
  have hstable : (prefixWord ++ tailWord_6854092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854092).length < 2 ^ (prefixWord ++ tailWord_6854092).sum := by decide
  have hdescent : baseEnd_6854092 < baseStart_6854092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854095 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 1, 2, 3]
def baseStart_6854095 : Nat := 118140960795 + 6854095 * 2 ^ 59
def prefixEnd_6854095 : Nat := 4983230072969 + 3 ^ 40 * 6854095 * 2
def baseEnd_6854095 : Nat := 3519445186578466055491097

theorem tailTrace_6854095 : CollatzResearch.WordTrace tailWord_6854095 prefixEnd_6854095 3519445186578466055491097 := by
  unfold tailWord_6854095
  simp only [CollatzResearch.WordTrace]
  refine ⟨249989382103791876075979739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166659588069194584050653159 249989382103791876075979739)
  ·
    refine ⟨374984073155687814113969609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249989382103791876075979739 374984073155687814113969609)
    ·
      refine ⟨281238054866765860585477207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374984073155687814113969609 281238054866765860585477207)
      ·
        refine ⟨421857082300148790878215811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281238054866765860585477207 421857082300148790878215811)
        ·
          refine ⟨632785623450223186317323717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421857082300148790878215811 632785623450223186317323717)
          ·
            refine ⟨118647304396916847434498197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 632785623450223186317323717 118647304396916847434498197)
            ·
              refine ⟨5561592393605477223492103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118647304396916847434498197 5561592393605477223492103)
              ·
                refine ⟨8342388590408215835238155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5561592393605477223492103 8342388590408215835238155)
                ·
                  refine ⟨12513582885612323752857233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8342388590408215835238155 12513582885612323752857233)
                  ·
                    refine ⟨9385187164209242814642925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12513582885612323752857233 9385187164209242814642925)
                    ·
                      refine ⟨3519445186578466055491097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9385187164209242814642925 3519445186578466055491097)
                      ·
                        rfl

theorem cell23_6854095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 2, 3].length) (baseStart_6854095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854095 prefixEnd_6854095 := by exact prefixLift 6854095
  have htrace : WordTrace (prefixWord ++ tailWord_6854095) baseStart_6854095 baseEnd_6854095 := by
    simpa [prefixWord, tailWord_6854095, baseEnd_6854095] using wordTrace_append hprefix tailTrace_6854095
  have hstable : (prefixWord ++ tailWord_6854095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854095).length < 2 ^ (prefixWord ++ tailWord_6854095).sum := by decide
  have hdescent : baseEnd_6854095 < baseStart_6854095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854102 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_6854102 : Nat := 118140960795 + 6854102 * 2 ^ 59
def prefixEnd_6854102 : Nat := 4983230072969 + 3 ^ 40 * 6854102 * 2
def baseEnd_6854102 : Nat := 1173149593647682509367855

theorem tailTrace_6854102 : CollatzResearch.WordTrace tailWord_6854102 prefixEnd_6854102 1173149593647682509367855 := by
  unfold tailWord_6854102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15624352338422907266967785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166659758276511010847656373 15624352338422907266967785)
  ·
    refine ⟨11718264253817180450225839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15624352338422907266967785 11718264253817180450225839)
    ·
      refine ⟨17577396380725770675338759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11718264253817180450225839 17577396380725770675338759)
      ·
        refine ⟨26366094571088656013008139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17577396380725770675338759 26366094571088656013008139)
        ·
          refine ⟨39549141856632984019512209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26366094571088656013008139 39549141856632984019512209)
          ·
            refine ⟨29661856392474738014634157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39549141856632984019512209 29661856392474738014634157)
            ·
              refine ⟨11123196147178026755487809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29661856392474738014634157 11123196147178026755487809)
              ·
                refine ⟨8342397110383520066615857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11123196147178026755487809 8342397110383520066615857)
                ·
                  refine ⟨6256797832787640049961893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8342397110383520066615857 6256797832787640049961893)
                  ·
                    refine ⟨1173149593647682509367855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6256797832787640049961893 1173149593647682509367855)
                    ·
                      rfl

theorem cell23_6854102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_6854102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854102 prefixEnd_6854102 := by exact prefixLift 6854102
  have htrace : WordTrace (prefixWord ++ tailWord_6854102) baseStart_6854102 baseEnd_6854102 := by
    simpa [prefixWord, tailWord_6854102, baseEnd_6854102] using wordTrace_append hprefix tailTrace_6854102
  have hstable : (prefixWord ++ tailWord_6854102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854102).length < 2 ^ (prefixWord ++ tailWord_6854102).sum := by decide
  have hdescent : baseEnd_6854102 < baseStart_6854102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854109 : List Nat := [1, 4, 3, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_6854109 : Nat := 118140960795 + 6854109 * 2 ^ 59
def prefixEnd_6854109 : Nat := 4983230072969 + 3 ^ 40 * 6854109 * 2
def baseEnd_6854109 : Nat := 3519452375307629000716033

theorem tailTrace_6854109 : CollatzResearch.WordTrace tailWord_6854109 prefixEnd_6854109 3519452375307629000716033 := by
  unfold tailWord_6854109
  simp only [CollatzResearch.WordTrace]
  refine ⟨249989892725741156466989381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166659928483827437644659587 249989892725741156466989381)
  ·
    refine ⟨46873104886076466837560509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249989892725741156466989381 46873104886076466837560509)
    ·
      refine ⟨17577414332278675064085191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46873104886076466837560509 17577414332278675064085191)
      ·
        refine ⟨26366121498418012596127787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17577414332278675064085191 26366121498418012596127787)
        ·
          refine ⟨39549182247627018894191681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26366121498418012596127787 39549182247627018894191681)
          ·
            refine ⟨29661886685720264170643761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39549182247627018894191681 29661886685720264170643761)
            ·
              refine ⟨22246415014290198127982821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29661886685720264170643761 22246415014290198127982821)
              ·
                refine ⟨4171202815179412148996779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22246415014290198127982821 4171202815179412148996779)
                ·
                  refine ⟨6256804222769118223495169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4171202815179412148996779 6256804222769118223495169)
                  ·
                    refine ⟨4692603167076838667621377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6256804222769118223495169 4692603167076838667621377)
                    ·
                      refine ⟨3519452375307629000716033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4692603167076838667621377 3519452375307629000716033)
                      ·
                        rfl

theorem cell23_6854109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_6854109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854109 prefixEnd_6854109 := by exact prefixLift 6854109
  have htrace : WordTrace (prefixWord ++ tailWord_6854109) baseStart_6854109 baseEnd_6854109 := by
    simpa [prefixWord, tailWord_6854109, baseEnd_6854109] using wordTrace_append hprefix tailTrace_6854109
  have hstable : (prefixWord ++ tailWord_6854109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854109).length < 2 ^ (prefixWord ++ tailWord_6854109).sum := by decide
  have hdescent : baseEnd_6854109 < baseStart_6854109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854122 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_6854122 : Nat := 118140960795 + 6854122 * 2 ^ 59
def prefixEnd_6854122 : Nat := 4983230072969 + 3 ^ 40 * 6854122 * 2
def baseEnd_6854122 : Nat := 3519459050556137449853473

theorem tailTrace_6854122 : CollatzResearch.WordTrace tailWord_6854122 prefixEnd_6854122 3519459050556137449853473 := by
  unfold tailWord_6854122
  simp only [CollatzResearch.WordTrace]
  refine ⟨62497591718673514921803155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166660244583129373124808413 62497591718673514921803155)
  ·
    refine ⟨93746387578010272382704733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62497591718673514921803155 93746387578010272382704733)
    ·
      refine ⟨35154895341753852143514275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93746387578010272382704733 35154895341753852143514275)
      ·
        refine ⟨52732343012630778215271413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35154895341753852143514275 52732343012630778215271413)
        ·
          refine ⟨4943657157434135457681695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52732343012630778215271413 4943657157434135457681695)
          ·
            refine ⟨7415485736151203186522543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943657157434135457681695 7415485736151203186522543)
            ·
              refine ⟨11123228604226804779783815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7415485736151203186522543 11123228604226804779783815)
              ·
                refine ⟨16684842906340207169675723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11123228604226804779783815 16684842906340207169675723)
                ·
                  refine ⟨25027264359510310754513585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16684842906340207169675723 25027264359510310754513585)
                  ·
                    refine ⟨18770448269632733065885189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25027264359510310754513585 18770448269632733065885189)
                    ·
                      refine ⟨3519459050556137449853473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18770448269632733065885189 3519459050556137449853473)
                      ·
                        rfl

theorem cell23_6854122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_6854122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854122 prefixEnd_6854122 := by exact prefixLift 6854122
  have htrace : WordTrace (prefixWord ++ tailWord_6854122) baseStart_6854122 baseEnd_6854122 := by
    simpa [prefixWord, tailWord_6854122, baseEnd_6854122] using wordTrace_append hprefix tailTrace_6854122
  have hstable : (prefixWord ++ tailWord_6854122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854122).length < 2 ^ (prefixWord ++ tailWord_6854122).sum := by decide
  have hdescent : baseEnd_6854122 < baseStart_6854122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854178 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_6854178 : Nat := 118140960795 + 6854178 * 2 ^ 59
def prefixEnd_6854178 : Nat := 4983230072969 + 3 ^ 40 * 6854178 * 2
def baseEnd_6854178 : Nat := 3519487805472789230753215

theorem tailTrace_6854178 : CollatzResearch.WordTrace tailWord_6854178 prefixEnd_6854178 3519487805472789230753215 := by
  unfold tailWord_6854178
  simp only [CollatzResearch.WordTrace]
  refine ⟨62498102340622795312812797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166661606241660787500834125 62498102340622795312812797)
  ·
    refine ⟨23436788377733548242304799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62498102340622795312812797 23436788377733548242304799)
    ·
      refine ⟨35155182566600322363457199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23436788377733548242304799 35155182566600322363457199)
      ·
        refine ⟨52732773849900483545185799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35155182566600322363457199 52732773849900483545185799)
        ·
          refine ⟨79099160774850725317778699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52732773849900483545185799 79099160774850725317778699)
          ·
            refine ⟨118648741162276087976668049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79099160774850725317778699 118648741162276087976668049)
            ·
              refine ⟨88986555871707065982501037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118648741162276087976668049 88986555871707065982501037)
              ·
                refine ⟨33369958451890149743437889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88986555871707065982501037 33369958451890149743437889)
                ·
                  refine ⟨25027468838917612307578417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33369958451890149743437889 25027468838917612307578417)
                  ·
                    refine ⟨18770601629188209230683813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25027468838917612307578417 18770601629188209230683813)
                    ·
                      refine ⟨3519487805472789230753215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18770601629188209230683813 3519487805472789230753215)
                      ·
                        rfl

theorem cell23_6854178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_6854178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854178 prefixEnd_6854178 := by exact prefixLift 6854178
  have htrace : WordTrace (prefixWord ++ tailWord_6854178) baseStart_6854178 baseEnd_6854178 := by
    simpa [prefixWord, tailWord_6854178, baseEnd_6854178] using wordTrace_append hprefix tailTrace_6854178
  have hstable : (prefixWord ++ tailWord_6854178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854178).length < 2 ^ (prefixWord ++ tailWord_6854178).sum := by decide
  have hdescent : baseEnd_6854178 < baseStart_6854178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854218 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_6854218 : Nat := 118140960795 + 6854218 * 2 ^ 59
def prefixEnd_6854218 : Nat := 4983230072969 + 3 ^ 40 * 6854218 * 2
def baseEnd_6854218 : Nat := 1173169448232989691417677

theorem tailTrace_6854218 : CollatzResearch.WordTrace tailWord_6854218 prefixEnd_6854218 1173169448232989691417677 := by
  unfold tailWord_6854218
  simp only [CollatzResearch.WordTrace]
  refine ⟨62498467070586567020676827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166662578854897512055138205 62498467070586567020676827)
  ·
    refine ⟨93747700605879850531015241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62498467070586567020676827 93747700605879850531015241)
    ·
      refine ⟨70310775454409887898261431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93747700605879850531015241 70310775454409887898261431)
      ·
        refine ⟨105466163181614831847392147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70310775454409887898261431 105466163181614831847392147)
        ·
          refine ⟨158199244772422247771088221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105466163181614831847392147 158199244772422247771088221)
          ·
            refine ⟨59324716789658342914158083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158199244772422247771088221 59324716789658342914158083)
            ·
              refine ⟨88987075184487514371237125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59324716789658342914158083 88987075184487514371237125)
              ·
                refine ⟨16685076597091408944606961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88987075184487514371237125 16685076597091408944606961)
                ·
                  refine ⟨12513807447818556708455221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16685076597091408944606961 12513807447818556708455221)
                  ·
                    refine ⟨1173169448232989691417677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12513807447818556708455221 1173169448232989691417677)
                    ·
                      rfl

theorem cell23_6854218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_6854218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854218 prefixEnd_6854218 := by exact prefixLift 6854218
  have htrace : WordTrace (prefixWord ++ tailWord_6854218) baseStart_6854218 baseEnd_6854218 := by
    simpa [prefixWord, tailWord_6854218, baseEnd_6854218] using wordTrace_append hprefix tailTrace_6854218
  have hstable : (prefixWord ++ tailWord_6854218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854218).length < 2 ^ (prefixWord ++ tailWord_6854218).sum := by decide
  have hdescent : baseEnd_6854218 < baseStart_6854218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854228 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_6854228 : Nat := 118140960795 + 6854228 * 2 ^ 59
def prefixEnd_6854228 : Nat := 4983230072969 + 3 ^ 40 * 6854228 * 2
def baseEnd_6854228 : Nat := 3519513479505514035127985

theorem tailTrace_6854228 : CollatzResearch.WordTrace tailWord_6854228 prefixEnd_6854228 3519513479505514035127985 := by
  unfold tailWord_6854228
  simp only [CollatzResearch.WordTrace]
  refine ⟨124997116506155019895285669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166662822008206693193714225 124997116506155019895285669)
  ·
    refine ⟨23436959344904066230366063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124997116506155019895285669 23436959344904066230366063)
    ·
      refine ⟨35155439017356099345549095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23436959344904066230366063 35155439017356099345549095)
      ·
        refine ⟨52733158526034149018323643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35155439017356099345549095 52733158526034149018323643)
        ·
          refine ⟨79099737789051223527485465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52733158526034149018323643 79099737789051223527485465)
          ·
            refine ⟨59324803341788417645614099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79099737789051223527485465 59324803341788417645614099)
            ·
              refine ⟨88987205012682626468421149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59324803341788417645614099 88987205012682626468421149)
              ·
                refine ⟨33370201879755984925657931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88987205012682626468421149 33370201879755984925657931)
                ·
                  refine ⟨50055302819633977388486897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33370201879755984925657931 50055302819633977388486897)
                  ·
                    refine ⟨37541477114725483041365173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50055302819633977388486897 37541477114725483041365173)
                    ·
                      refine ⟨3519513479505514035127985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37541477114725483041365173 3519513479505514035127985)
                      ·
                        rfl

theorem cell23_6854228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_6854228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854228 prefixEnd_6854228 := by exact prefixLift 6854228
  have htrace : WordTrace (prefixWord ++ tailWord_6854228) baseStart_6854228 baseEnd_6854228 := by
    simpa [prefixWord, tailWord_6854228, baseEnd_6854228] using wordTrace_append hprefix tailTrace_6854228
  have hstable : (prefixWord ++ tailWord_6854228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854228).length < 2 ^ (prefixWord ++ tailWord_6854228).sum := by decide
  have hdescent : baseEnd_6854228 < baseStart_6854228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854282 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 3, 4]
def baseStart_6854282 : Nat := 118140960795 + 6854282 * 2 ^ 59
def prefixEnd_6854282 : Nat := 4983230072969 + 3 ^ 40 * 6854282 * 2
def baseEnd_6854282 : Nat := 1173180402486952274617579

theorem tailTrace_6854282 : CollatzResearch.WordTrace tailWord_6854282 prefixEnd_6854282 1173180402486952274617579 := by
  unfold tailWord_6854282
  simp only [CollatzResearch.WordTrace]
  refine ⟨62499050638528601753259275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166664135036076271342024733 62499050638528601753259275)
  ·
    refine ⟨93748575957792902629888913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62499050638528601753259275 93748575957792902629888913)
    ·
      refine ⟨70311431968344676972416685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93748575957792902629888913 70311431968344676972416685)
      ·
        refine ⟨26366786988129253864656257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70311431968344676972416685 26366786988129253864656257)
        ·
          refine ⟨19775090241096940398492193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26366786988129253864656257 19775090241096940398492193)
          ·
            refine ⟨14831317680822705298869145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19775090241096940398492193 14831317680822705298869145)
            ·
              refine ⟨11123488260617028974151859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14831317680822705298869145 11123488260617028974151859)
              ·
                refine ⟨16685232390925543461227789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11123488260617028974151859 16685232390925543461227789)
                ·
                  refine ⟨6256962146597078797960421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16685232390925543461227789 6256962146597078797960421)
                  ·
                    refine ⟨1173180402486952274617579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6256962146597078797960421 1173180402486952274617579)
                    ·
                      rfl

theorem cell23_6854282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_6854282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854282 prefixEnd_6854282 := by exact prefixLift 6854282
  have htrace : WordTrace (prefixWord ++ tailWord_6854282) baseStart_6854282 baseEnd_6854282 := by
    simpa [prefixWord, tailWord_6854282, baseEnd_6854282] using wordTrace_append hprefix tailTrace_6854282
  have hstable : (prefixWord ++ tailWord_6854282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854282).length < 2 ^ (prefixWord ++ tailWord_6854282).sum := by decide
  have hdescent : baseEnd_6854282 < baseStart_6854282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854332 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 4, 3, 2]
def baseStart_6854332 : Nat := 118140960795 + 6854332 * 2 ^ 59
def prefixEnd_6854332 : Nat := 4983230072969 + 3 ^ 40 * 6854332 * 2
def baseEnd_6854332 : Nat := 3519566881493581628227507

theorem tailTrace_6854332 : CollatzResearch.WordTrace tailWord_6854332 prefixEnd_6854332 3519566881493581628227507 := by
  unfold tailWord_6854332
  simp only [CollatzResearch.WordTrace]
  refine ⟨124999013101966632776178625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166665350802622177034904833 124999013101966632776178625)
  ·
    refine ⟨93749259826474974582133969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124999013101966632776178625 93749259826474974582133969)
    ·
      refine ⟨70311944869856230936600477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93749259826474974582133969 70311944869856230936600477)
      ·
        refine ⟨26366979326196086601225179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70311944869856230936600477 26366979326196086601225179)
        ·
          refine ⟨39550468989294129901837769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26366979326196086601225179 39550468989294129901837769)
          ·
            refine ⟨29662851741970597426378327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39550468989294129901837769 29662851741970597426378327)
            ·
              refine ⟨44494277612955896139567491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29662851741970597426378327 44494277612955896139567491)
              ·
                refine ⟨66741416419433844209351237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44494277612955896139567491 66741416419433844209351237)
                ·
                  refine ⟨12514015578643845789253357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66741416419433844209351237 12514015578643845789253357)
                  ·
                    refine ⟨4692755841991442170970009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12514015578643845789253357 4692755841991442170970009)
                    ·
                      refine ⟨3519566881493581628227507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4692755841991442170970009 3519566881493581628227507)
                      ·
                        rfl

theorem cell23_6854332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_6854332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854332 prefixEnd_6854332 := by exact prefixLift 6854332
  have htrace : WordTrace (prefixWord ++ tailWord_6854332) baseStart_6854332 baseEnd_6854332 := by
    simpa [prefixWord, tailWord_6854332, baseEnd_6854332] using wordTrace_append hprefix tailTrace_6854332
  have hstable : (prefixWord ++ tailWord_6854332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854332).length < 2 ^ (prefixWord ++ tailWord_6854332).sum := by decide
  have hdescent : baseEnd_6854332 < baseStart_6854332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854362 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4]
def baseStart_6854362 : Nat := 118140960795 + 6854362 * 2 ^ 59
def prefixEnd_6854362 : Nat := 4983230072969 + 3 ^ 40 * 6854362 * 2
def baseEnd_6854362 : Nat := 3519582285913216510852369

theorem tailTrace_6854362 : CollatzResearch.WordTrace tailWord_6854362 prefixEnd_6854362 3519582285913216510852369 := by
  unfold tailWord_6854362
  simp only [CollatzResearch.WordTrace]
  refine ⟨62499780098456145168987335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166666080262549720450632893 62499780098456145168987335)
  ·
    refine ⟨93749670147684217753481003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62499780098456145168987335 93749670147684217753481003)
    ·
      refine ⟨140624505221526326630221505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93749670147684217753481003 140624505221526326630221505)
      ·
        refine ⟨105468378916144744972666129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140624505221526326630221505 105468378916144744972666129)
        ·
          refine ⟨79101284187108558729499597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105468378916144744972666129 79101284187108558729499597)
          ·
            refine ⟨29662981570165709523562349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79101284187108558729499597 29662981570165709523562349)
            ·
              refine ⟨11123618088812141071335881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29662981570165709523562349 11123618088812141071335881)
              ·
                refine ⟨8342713566609105803501911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11123618088812141071335881 8342713566609105803501911)
                ·
                  refine ⟨12514070349913658705252867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8342713566609105803501911 12514070349913658705252867)
                  ·
                    refine ⟨18771105524870488057879301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12514070349913658705252867 18771105524870488057879301)
                    ·
                      refine ⟨3519582285913216510852369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18771105524870488057879301 3519582285913216510852369)
                      ·
                        rfl

theorem cell23_6854362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_6854362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854362 prefixEnd_6854362 := by exact prefixLift 6854362
  have htrace : WordTrace (prefixWord ++ tailWord_6854362) baseStart_6854362 baseEnd_6854362 := by
    simpa [prefixWord, tailWord_6854362, baseEnd_6854362] using wordTrace_append hprefix tailTrace_6854362
  have hstable : (prefixWord ++ tailWord_6854362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854362).length < 2 ^ (prefixWord ++ tailWord_6854362).sum := by decide
  have hdescent : baseEnd_6854362 < baseStart_6854362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854368 : List Nat := [2, 1, 1, 3, 1, 2, 4, 9]
def baseStart_6854368 : Nat := 118140960795 + 6854368 * 2 ^ 59
def prefixEnd_6854368 : Nat := 4983230072969 + 3 ^ 40 * 6854368 * 2
def baseEnd_6854368 : Nat := 130355013585079388421383

theorem tailTrace_6854368 : CollatzResearch.WordTrace tailWord_6854368 prefixEnd_6854368 130355013585079388421383 := by
  unfold tailWord_6854368
  simp only [CollatzResearch.WordTrace]
  refine ⟨124999669615901421850333879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166666226154535229133778505 124999669615901421850333879)
  ·
    refine ⟨187499504423852132775500819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124999669615901421850333879 187499504423852132775500819)
    ·
      refine ⟨281249256635778199163251229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187499504423852132775500819 281249256635778199163251229)
      ·
        refine ⟨105468471238416824686219211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281249256635778199163251229 105468471238416824686219211)
        ·
          refine ⟨158202706857625237029328817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105468471238416824686219211 158202706857625237029328817)
          ·
            refine ⟨118652030143218927771996613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158202706857625237029328817 118652030143218927771996613)
            ·
              refine ⟨22247255651853548957249365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118652030143218927771996613 22247255651853548957249365)
              ·
                refine ⟨130355013585079388421383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22247255651853548957249365 130355013585079388421383)
                ·
                  rfl

theorem cell23_6854368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 9].length) (baseStart_6854368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854368 prefixEnd_6854368 := by exact prefixLift 6854368
  have htrace : WordTrace (prefixWord ++ tailWord_6854368) baseStart_6854368 baseEnd_6854368 := by
    simpa [prefixWord, tailWord_6854368, baseEnd_6854368] using wordTrace_append hprefix tailTrace_6854368
  have hstable : (prefixWord ++ tailWord_6854368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854368).length < 2 ^ (prefixWord ++ tailWord_6854368).sum := by decide
  have hdescent : baseEnd_6854368 < baseStart_6854368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854396 : List Nat := [2, 2, 2, 1, 3, 1, 3, 4, 1, 2, 2]
def baseStart_6854396 : Nat := 118140960795 + 6854396 * 2 ^ 59
def prefixEnd_6854396 : Nat := 4983230072969 + 3 ^ 40 * 6854396 * 2
def baseEnd_6854396 : Nat := 3519599744255469377827213

theorem tailTrace_6854396 : CollatzResearch.WordTrace tailWord_6854396 prefixEnd_6854396 3519599744255469377827213 := by
  unfold tailWord_6854396
  simp only [CollatzResearch.WordTrace]
  refine ⟨125000180237850702241343521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166666906983800936321791361 125000180237850702241343521)
  ·
    refine ⟨93750135178388026681007641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125000180237850702241343521 93750135178388026681007641)
    ·
      refine ⟨70312601383791020010755731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93750135178388026681007641 70312601383791020010755731)
      ·
        refine ⟨105468902075686530016133597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70312601383791020010755731 105468902075686530016133597)
        ·
          refine ⟨39550838278382448756050099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105468902075686530016133597 39550838278382448756050099)
          ·
            refine ⟨59326257417573673134075149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39550838278382448756050099 59326257417573673134075149)
            ·
              refine ⟨22247346531590127425278181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59326257417573673134075149 22247346531590127425278181)
              ·
                refine ⟨4171377474673148892239659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22247346531590127425278181 4171377474673148892239659)
                ·
                  refine ⟨6257066212009723338359489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4171377474673148892239659 6257066212009723338359489)
                  ·
                    refine ⟨4692799659007292503769617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6257066212009723338359489 4692799659007292503769617)
                    ·
                      refine ⟨3519599744255469377827213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4692799659007292503769617 3519599744255469377827213)
                      ·
                        rfl

theorem cell23_6854396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_6854396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854396 prefixEnd_6854396 := by exact prefixLift 6854396
  have htrace : WordTrace (prefixWord ++ tailWord_6854396) baseStart_6854396 baseEnd_6854396 := by
    simpa [prefixWord, tailWord_6854396, baseEnd_6854396] using wordTrace_append hprefix tailTrace_6854396
  have hstable : (prefixWord ++ tailWord_6854396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854396).length < 2 ^ (prefixWord ++ tailWord_6854396).sum := by decide
  have hdescent : baseEnd_6854396 < baseStart_6854396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854430 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6854430 : Nat := 118140960795 + 6854430 * 2 ^ 59
def prefixEnd_6854430 : Nat := 4983230072969 + 3 ^ 40 * 6854430 * 2
def baseEnd_6854430 : Nat := 3519617202597722244802057

theorem tailTrace_6854430 : CollatzResearch.WordTrace tailWord_6854430 prefixEnd_6854430 3519617202597722244802057 := by
  unfold tailWord_6854430
  simp only [CollatzResearch.WordTrace]
  refine ⟨31250200069697278536178093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166667733705052152192949829 31250200069697278536178093)
  ·
    refine ⟨11718825026136479451066785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31250200069697278536178093 11718825026136479451066785)
    ·
      refine ⟨8789118769602359588300089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11718825026136479451066785 8789118769602359588300089)
      ·
        refine ⟨6591839077201769691225067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8789118769602359588300089 6591839077201769691225067)
        ·
          refine ⟨9887758615802654536837601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6591839077201769691225067 9887758615802654536837601)
          ·
            refine ⟨7415818961851990902628201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9887758615802654536837601 7415818961851990902628201)
            ·
              refine ⟨5561864221388993176971151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415818961851990902628201 5561864221388993176971151)
              ·
                refine ⟨8342796332083489765456727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5561864221388993176971151 8342796332083489765456727)
                ·
                  refine ⟨12514194498125234648185091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8342796332083489765456727 12514194498125234648185091)
                  ·
                    refine ⟨18771291747187851972277637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12514194498125234648185091 18771291747187851972277637)
                    ·
                      refine ⟨3519617202597722244802057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18771291747187851972277637 3519617202597722244802057)
                      ·
                        rfl

theorem cell23_6854430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6854430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854430 prefixEnd_6854430 := by exact prefixLift 6854430
  have htrace : WordTrace (prefixWord ++ tailWord_6854430) baseStart_6854430 baseEnd_6854430 := by
    simpa [prefixWord, tailWord_6854430, baseEnd_6854430] using wordTrace_append hprefix tailTrace_6854430
  have hstable : (prefixWord ++ tailWord_6854430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854430).length < 2 ^ (prefixWord ++ tailWord_6854430).sum := by decide
  have hdescent : baseEnd_6854430 < baseStart_6854430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854446 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_6854446 : Nat := 118140960795 + 6854446 * 2 ^ 59
def prefixEnd_6854446 : Nat := 4983230072969 + 3 ^ 40 * 6854446 * 2
def baseEnd_6854446 : Nat := 3519625418288194182201983

theorem tailTrace_6854446 : CollatzResearch.WordTrace tailWord_6854446 prefixEnd_6854446 3519625418288194182201983 := by
  unfold tailWord_6854446
  simp only [CollatzResearch.WordTrace]
  refine ⟨31250273015690032877750899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166668122750346842014671461 31250273015690032877750899)
  ·
    refine ⟨46875409523535049316626349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31250273015690032877750899 46875409523535049316626349)
    ·
      refine ⟨17578278571325643493734881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46875409523535049316626349 17578278571325643493734881)
      ·
        refine ⟨13183708928494232620301161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17578278571325643493734881 13183708928494232620301161)
        ·
          refine ⟨9887781696370674465225871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13183708928494232620301161 9887781696370674465225871)
          ·
            refine ⟨14831672544556011697838807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9887781696370674465225871 14831672544556011697838807)
            ·
              refine ⟨22247508816834017546758211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14831672544556011697838807 22247508816834017546758211)
              ·
                refine ⟨33371263225251026320137317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22247508816834017546758211 33371263225251026320137317)
                ·
                  refine ⟨6257111854734567435025747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33371263225251026320137317 6257111854734567435025747)
                  ·
                    refine ⟨9385667782101851152538621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6257111854734567435025747 9385667782101851152538621)
                    ·
                      refine ⟨3519625418288194182201983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9385667782101851152538621 3519625418288194182201983)
                      ·
                        rfl

theorem cell23_6854446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_6854446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854446 prefixEnd_6854446 := by exact prefixLift 6854446
  have htrace : WordTrace (prefixWord ++ tailWord_6854446) baseStart_6854446 baseEnd_6854446 := by
    simpa [prefixWord, tailWord_6854446, baseEnd_6854446] using wordTrace_append hprefix tailTrace_6854446
  have hstable : (prefixWord ++ tailWord_6854446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854446).length < 2 ^ (prefixWord ++ tailWord_6854446).sum := by decide
  have hdescent : baseEnd_6854446 < baseStart_6854446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854455 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 3]
def baseStart_6854455 : Nat := 118140960795 + 6854455 * 2 ^ 59
def prefixEnd_6854455 : Nat := 4983230072969 + 3 ^ 40 * 6854455 * 2
def baseEnd_6854455 : Nat := 3519630039614084646989441

theorem tailTrace_6854455 : CollatzResearch.WordTrace tailWord_6854455 prefixEnd_6854455 3519630039614084646989441 := by
  unfold tailWord_6854455
  simp only [CollatzResearch.WordTrace]
  refine ⟨250002512382487657559084819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166668341588325105039389879 250002512382487657559084819)
  ·
    refine ⟨375003768573731486338627229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250002512382487657559084819 375003768573731486338627229)
    ·
      refine ⟨140626413215149307376985211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375003768573731486338627229 140626413215149307376985211)
      ·
        refine ⟨210939619822723961065477817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140626413215149307376985211 210939619822723961065477817)
        ·
          refine ⟨158204714867042970799108363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210939619822723961065477817 158204714867042970799108363)
          ·
            refine ⟨237307072300564456198662545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158204714867042970799108363 237307072300564456198662545)
            ·
              refine ⟨177980304225423342148996909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237307072300564456198662545 177980304225423342148996909)
              ·
                refine ⟨66742614084533753305873841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177980304225423342148996909 66742614084533753305873841)
                ·
                  refine ⟨50056960563400314979405381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66742614084533753305873841 50056960563400314979405381)
                  ·
                    refine ⟨9385680105637559058638509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50056960563400314979405381 9385680105637559058638509)
                    ·
                      refine ⟨3519630039614084646989441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9385680105637559058638509 3519630039614084646989441)
                      ·
                        rfl

theorem cell23_6854455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_6854455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854455 prefixEnd_6854455 := by exact prefixLift 6854455
  have htrace : WordTrace (prefixWord ++ tailWord_6854455) baseStart_6854455 baseEnd_6854455 := by
    simpa [prefixWord, tailWord_6854455, baseEnd_6854455] using wordTrace_append hprefix tailTrace_6854455
  have hstable : (prefixWord ++ tailWord_6854455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854455).length < 2 ^ (prefixWord ++ tailWord_6854455).sum := by decide
  have hdescent : baseEnd_6854455 < baseStart_6854455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854462 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_6854462 : Nat := 118140960795 + 6854462 * 2 ^ 59
def prefixEnd_6854462 : Nat := 4983230072969 + 3 ^ 40 * 6854462 * 2
def baseEnd_6854462 : Nat := 1173211211326222039867303

theorem tailTrace_6854462 : CollatzResearch.WordTrace tailWord_6854462 prefixEnd_6854462 1173211211326222039867303 := by
  unfold tailWord_6854462
  simp only [CollatzResearch.WordTrace]
  refine ⟨31250345961682787219323705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166668511795641531836393093 31250345961682787219323705)
  ·
    refine ⟨23437759471262090414492779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31250345961682787219323705 23437759471262090414492779)
    ·
      refine ⟨35156639206893135621739169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23437759471262090414492779 35156639206893135621739169)
      ·
        refine ⟨26367479405169851716304377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35156639206893135621739169 26367479405169851716304377)
        ·
          refine ⟨19775609553877388787228283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26367479405169851716304377 19775609553877388787228283)
          ·
            refine ⟨29663414330816083180842425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19775609553877388787228283 29663414330816083180842425)
            ·
              refine ⟨22247560748112062385631819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29663414330816083180842425 22247560748112062385631819)
              ·
                refine ⟨33371341122168093578447729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22247560748112062385631819 33371341122168093578447729)
                ·
                  refine ⟨25028505841626070183835797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33371341122168093578447729 25028505841626070183835797)
                  ·
                    refine ⟨1173211211326222039867303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25028505841626070183835797 1173211211326222039867303)
                    ·
                      rfl

theorem cell23_6854462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_6854462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854462 prefixEnd_6854462 := by exact prefixLift 6854462
  have htrace : WordTrace (prefixWord ++ tailWord_6854462) baseStart_6854462 baseEnd_6854462 := by
    simpa [prefixWord, tailWord_6854462, baseEnd_6854462] using wordTrace_append hprefix tailTrace_6854462
  have hstable : (prefixWord ++ tailWord_6854462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854462).length < 2 ^ (prefixWord ++ tailWord_6854462).sum := by decide
  have hdescent : baseEnd_6854462 < baseStart_6854462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854512 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 2, 5, 2]
def baseStart_6854512 : Nat := 118140960795 + 6854512 * 2 ^ 59
def prefixEnd_6854512 : Nat := 4983230072969 + 3 ^ 40 * 6854512 * 2
def baseEnd_6854512 : Nat := 3519659308011390923976679

theorem tailTrace_6854512 : CollatzResearch.WordTrace tailWord_6854512 prefixEnd_6854512 3519659308011390923976679 := by
  unfold tailWord_6854512
  simp only [CollatzResearch.WordTrace]
  refine ⟨125002295671640578146954895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166669727562187437529273193 125002295671640578146954895)
  ·
    refine ⟨187503443507460867220432343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125002295671640578146954895 187503443507460867220432343)
    ·
      refine ⟨281255165261191300830648515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187503443507460867220432343 281255165261191300830648515)
      ·
        refine ⟨421882747891786951245972773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281255165261191300830648515 421882747891786951245972773)
        ·
          refine ⟨79103015229710053358619895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421882747891786951245972773 79103015229710053358619895)
          ·
            refine ⟨118654522844565080037929843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79103015229710053358619895 118654522844565080037929843)
            ·
              refine ⟨177981784266847620056894765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118654522844565080037929843 177981784266847620056894765)
              ·
                refine ⟨66743169100067857521335537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177981784266847620056894765 66743169100067857521335537)
                ·
                  refine ⟨50057376825050893141001653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66743169100067857521335537 50057376825050893141001653)
                  ·
                    refine ⟨4692879077348521231968905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50057376825050893141001653 4692879077348521231968905)
                    ·
                      refine ⟨3519659308011390923976679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4692879077348521231968905 3519659308011390923976679)
                      ·
                        rfl

theorem cell23_6854512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 5, 2].length) (baseStart_6854512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854512 prefixEnd_6854512 := by exact prefixLift 6854512
  have htrace : WordTrace (prefixWord ++ tailWord_6854512) baseStart_6854512 baseEnd_6854512 := by
    simpa [prefixWord, tailWord_6854512, baseEnd_6854512] using wordTrace_append hprefix tailTrace_6854512
  have hstable : (prefixWord ++ tailWord_6854512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854512).length < 2 ^ (prefixWord ++ tailWord_6854512).sum := by decide
  have hdescent : baseEnd_6854512 < baseStart_6854512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854565 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 8]
def baseStart_6854565 : Nat := 118140960795 + 6854565 * 2 ^ 59
def prefixEnd_6854565 : Nat := 4983230072969 + 3 ^ 40 * 6854565 * 2
def baseEnd_6854565 : Nat := 391076280276231024068215

theorem tailTrace_6854565 : CollatzResearch.WordTrace tailWord_6854565 prefixEnd_6854565 391076280276231024068215 := by
  unfold tailWord_6854565
  simp only [CollatzResearch.WordTrace]
  refine ⟨250006524412089146345589149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166671016274726097563726099 250006524412089146345589149)
  ·
    refine ⟨93752446654533429879595931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250006524412089146345589149 93752446654533429879595931)
    ·
      refine ⟨140628669981800144819393897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93752446654533429879595931 140628669981800144819393897)
      ·
        refine ⟨105471502486350108614545423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140628669981800144819393897 105471502486350108614545423)
        ·
          refine ⟨158207253729525162921818135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105471502486350108614545423 158207253729525162921818135)
          ·
            refine ⟨237310880594287744382727203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158207253729525162921818135 237310880594287744382727203)
            ·
              refine ⟨355966320891431616574090805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237310880594287744382727203 355966320891431616574090805)
              ·
                refine ⟨33371842583571714053821013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 355966320891431616574090805 33371842583571714053821013)
                ·
                  refine ⟨391076280276231024068215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33371842583571714053821013 391076280276231024068215)
                  ·
                    rfl

theorem cell23_6854565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_6854565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854565 prefixEnd_6854565 := by exact prefixLift 6854565
  have htrace : WordTrace (prefixWord ++ tailWord_6854565) baseStart_6854565 baseEnd_6854565 := by
    simpa [prefixWord, tailWord_6854565, baseEnd_6854565] using wordTrace_append hprefix tailTrace_6854565
  have hstable : (prefixWord ++ tailWord_6854565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854565).length < 2 ^ (prefixWord ++ tailWord_6854565).sum := by decide
  have hdescent : baseEnd_6854565 < baseStart_6854565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854620 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6854620 : Nat := 118140960795 + 6854620 * 2 ^ 59
def prefixEnd_6854620 : Nat := 4983230072969 + 3 ^ 40 * 6854620 * 2
def baseEnd_6854620 : Nat := 1173238254640692167142061

theorem tailTrace_6854620 : CollatzResearch.WordTrace tailWord_6854620 prefixEnd_6854620 1173238254640692167142061 := by
  unfold tailWord_6854620
  simp only [CollatzResearch.WordTrace]
  refine ⟨125004265213444945369420657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166672353617926593825894209 125004265213444945369420657)
  ·
    refine ⟨93753198910083709027065493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125004265213444945369420657 93753198910083709027065493)
    ·
      refine ⟨4394681198910173860643695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93753198910083709027065493 4394681198910173860643695)
      ·
        refine ⟨6592021798365260790965543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394681198910173860643695 6592021798365260790965543)
        ·
          refine ⟨9888032697547891186448315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6592021798365260790965543 9888032697547891186448315)
          ·
            refine ⟨14832049046321836779672473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9888032697547891186448315 14832049046321836779672473)
            ·
              refine ⟨11124036784741377584754355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14832049046321836779672473 11124036784741377584754355)
              ·
                refine ⟨16686055177112066377131533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11124036784741377584754355 16686055177112066377131533)
                ·
                  refine ⟨6257270691417024891424325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16686055177112066377131533 6257270691417024891424325)
                  ·
                    refine ⟨1173238254640692167142061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6257270691417024891424325 1173238254640692167142061)
                    ·
                      rfl

theorem cell23_6854620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6854620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854620 prefixEnd_6854620 := by exact prefixLift 6854620
  have htrace : WordTrace (prefixWord ++ tailWord_6854620) baseStart_6854620 baseEnd_6854620 := by
    simpa [prefixWord, tailWord_6854620, baseEnd_6854620] using wordTrace_append hprefix tailTrace_6854620
  have hstable : (prefixWord ++ tailWord_6854620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854620).length < 2 ^ (prefixWord ++ tailWord_6854620).sum := by decide
  have hdescent : baseEnd_6854620 < baseStart_6854620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854649 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 4]
def baseStart_6854649 : Nat := 118140960795 + 6854649 * 2 ^ 59
def prefixEnd_6854649 : Nat := 4983230072969 + 3 ^ 40 * 6854649 * 2
def baseEnd_6854649 : Nat := 3519729654861056887963549

theorem tailTrace_6854649 : CollatzResearch.WordTrace tailWord_6854649 prefixEnd_6854649 3519729654861056887963549 := by
  unfold tailWord_6854649
  simp only [CollatzResearch.WordTrace]
  refine ⟨250009588143784828691647001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166673058762523219127764667 250009588143784828691647001)
  ·
    refine ⟨187507191107838621518735251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250009588143784828691647001 187507191107838621518735251)
    ·
      refine ⟨281260786661757932278102877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187507191107838621518735251 281260786661757932278102877)
      ·
        refine ⟨105472794998159224604288579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281260786661757932278102877 105472794998159224604288579)
        ·
          refine ⟨158209192497238836906432869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105472794998159224604288579 158209192497238836906432869)
          ·
            refine ⟨29664223593232281919956163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158209192497238836906432869 29664223593232281919956163)
            ·
              refine ⟨44496335389848422879934245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29664223593232281919956163 44496335389848422879934245)
              ·
                refine ⟨8343062885596579289987671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44496335389848422879934245 8343062885596579289987671)
                ·
                  refine ⟨12514594328394868934981507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8343062885596579289987671 12514594328394868934981507)
                  ·
                    refine ⟨18771891492592303402472261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12514594328394868934981507 18771891492592303402472261)
                    ·
                      refine ⟨3519729654861056887963549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18771891492592303402472261 3519729654861056887963549)
                      ·
                        rfl

theorem cell23_6854649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_6854649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854649 prefixEnd_6854649 := by exact prefixLift 6854649
  have htrace : WordTrace (prefixWord ++ tailWord_6854649) baseStart_6854649 baseEnd_6854649 := by
    simpa [prefixWord, tailWord_6854649, baseEnd_6854649] using wordTrace_append hprefix tailTrace_6854649
  have hstable : (prefixWord ++ tailWord_6854649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854649).length < 2 ^ (prefixWord ++ tailWord_6854649).sum := by decide
  have hdescent : baseEnd_6854649 < baseStart_6854649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854652 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_6854652 : Nat := 118140960795 + 6854652 * 2 ^ 59
def prefixEnd_6854652 : Nat := 4983230072969 + 3 ^ 40 * 6854652 * 2
def baseEnd_6854652 : Nat := 3519731195303020376226035

theorem tailTrace_6854652 : CollatzResearch.WordTrace tailWord_6854652 prefixEnd_6854652 3519731195303020376226035 := by
  unfold tailWord_6854652
  simp only [CollatzResearch.WordTrace]
  refine ⟨125004848781386980102003105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166673131708515973469337473 125004848781386980102003105)
  ·
    refine ⟨93753636586040235076502329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125004848781386980102003105 93753636586040235076502329)
    ·
      refine ⟨70315227439530176307376747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93753636586040235076502329 70315227439530176307376747)
      ·
        refine ⟨105472841159295264461065121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70315227439530176307376747 105472841159295264461065121)
        ·
          refine ⟨79104630869471448345798841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105472841159295264461065121 79104630869471448345798841)
          ·
            refine ⟨59328473152103586259349131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79104630869471448345798841 59328473152103586259349131)
            ·
              refine ⟨88992709728155379389023697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59328473152103586259349131 88992709728155379389023697)
              ·
                refine ⟨66744532296116534541767773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88992709728155379389023697 66744532296116534541767773)
                ·
                  refine ⟨25029199611043700453162915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66744532296116534541767773 25029199611043700453162915)
                  ·
                    refine ⟨37543799416565550679744373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25029199611043700453162915 37543799416565550679744373)
                    ·
                      refine ⟨3519731195303020376226035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37543799416565550679744373 3519731195303020376226035)
                      ·
                        rfl

theorem cell23_6854652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_6854652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854652 prefixEnd_6854652 := by exact prefixLift 6854652
  have htrace : WordTrace (prefixWord ++ tailWord_6854652) baseStart_6854652 baseEnd_6854652 := by
    simpa [prefixWord, tailWord_6854652, baseEnd_6854652] using wordTrace_append hprefix tailTrace_6854652
  have hstable : (prefixWord ++ tailWord_6854652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854652).length < 2 ^ (prefixWord ++ tailWord_6854652).sum := by decide
  have hdescent : baseEnd_6854652 < baseStart_6854652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854689 : List Nat := [1, 2, 3, 2, 4, 1, 2, 8]
def baseStart_6854689 : Nat := 118140960795 + 6854689 * 2 ^ 59
def prefixEnd_6854689 : Nat := 4983230072969 + 3 ^ 40 * 6854689 * 2
def baseEnd_6854689 : Nat := 130361118299527286350495

theorem tailTrace_6854689 : CollatzResearch.WordTrace tailWord_6854689 prefixEnd_6854689 130361118299527286350495 := by
  unfold tailWord_6854689
  simp only [CollatzResearch.WordTrace]
  refine ⟨250011047063639915523103121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166674031375759943682068747 250011047063639915523103121)
  ·
    refine ⟨187508285297729936642327341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250011047063639915523103121 187508285297729936642327341)
    ·
      refine ⟨70315606986648726240872753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187508285297729936642327341 70315606986648726240872753)
      ·
        refine ⟨52736705239986544680654565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70315606986648726240872753 52736705239986544680654565)
        ·
          refine ⟨9888132232497477127622731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52736705239986544680654565 9888132232497477127622731)
          ·
            refine ⟨14832198348746215691434097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9888132232497477127622731 14832198348746215691434097)
            ·
              refine ⟨11124148761559661768575573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14832198348746215691434097 11124148761559661768575573)
              ·
                refine ⟨130361118299527286350495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11124148761559661768575573 130361118299527286350495)
                ·
                  rfl

theorem cell23_6854689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 8].length) (baseStart_6854689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854689 prefixEnd_6854689 := by exact prefixLift 6854689
  have htrace : WordTrace (prefixWord ++ tailWord_6854689) baseStart_6854689 baseEnd_6854689 := by
    simpa [prefixWord, tailWord_6854689, baseEnd_6854689] using wordTrace_append hprefix tailTrace_6854689
  have hstable : (prefixWord ++ tailWord_6854689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854689).length < 2 ^ (prefixWord ++ tailWord_6854689).sum := by decide
  have hdescent : baseEnd_6854689 < baseStart_6854689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854693 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 2, 4]
def baseStart_6854693 : Nat := 118140960795 + 6854693 * 2 ^ 59
def prefixEnd_6854693 : Nat := 4983230072969 + 3 ^ 40 * 6854693 * 2
def baseEnd_6854693 : Nat := 1173250749336618238604449

theorem tailTrace_6854693 : CollatzResearch.WordTrace tailWord_6854693 prefixEnd_6854693 1173250749336618238604449 := by
  unfold tailWord_6854693
  simp only [CollatzResearch.WordTrace]
  refine ⟨250011192955625424206248733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166674128637083616137499155 250011192955625424206248733)
  ·
    refine ⟨93754197358359534077343275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250011192955625424206248733 93754197358359534077343275)
    ·
      refine ⟨140631296037539301116014913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93754197358359534077343275 140631296037539301116014913)
      ·
        refine ⟨105473472028154475837011185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140631296037539301116014913 105473472028154475837011185)
        ·
          refine ⟨79105104021115856877758389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105473472028154475837011185 79105104021115856877758389)
          ·
            refine ⟨7416103501979611582289849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79105104021115856877758389 7416103501979611582289849)
            ·
              refine ⟨5562077626484708686717387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7416103501979611582289849 5562077626484708686717387)
              ·
                refine ⟨8343116439727063030076081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562077626484708686717387 8343116439727063030076081)
                ·
                  refine ⟨6257337329795297272557061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8343116439727063030076081 6257337329795297272557061)
                  ·
                    refine ⟨1173250749336618238604449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6257337329795297272557061 1173250749336618238604449)
                    ·
                      rfl

theorem cell23_6854693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_6854693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854693 prefixEnd_6854693 := by exact prefixLift 6854693
  have htrace : WordTrace (prefixWord ++ tailWord_6854693) baseStart_6854693 baseEnd_6854693 := by
    simpa [prefixWord, tailWord_6854693, baseEnd_6854693] using wordTrace_append hprefix tailTrace_6854693
  have hstable : (prefixWord ++ tailWord_6854693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854693).length < 2 ^ (prefixWord ++ tailWord_6854693).sum := by decide
  have hdescent : baseEnd_6854693 < baseStart_6854693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854699 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 6, 1, 3]
def baseStart_6854699 : Nat := 118140960795 + 6854699 * 2 ^ 59
def prefixEnd_6854699 : Nat := 4983230072969 + 3 ^ 40 * 6854699 * 2
def baseEnd_6854699 : Nat := 3519755328893781692338319

theorem tailTrace_6854699 : CollatzResearch.WordTrace tailWord_6854699 prefixEnd_6854699 3519755328893781692338319 := by
  unfold tailWord_6854699
  simp only [CollatzResearch.WordTrace]
  refine ⟨250011411793603687230967151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166674274529069124820644767 250011411793603687230967151)
  ·
    refine ⟨375017117690405530846450727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250011411793603687230967151 375017117690405530846450727)
    ·
      refine ⟨562525676535608296269676091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375017117690405530846450727 562525676535608296269676091)
      ·
        refine ⟨843788514803412444404514137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562525676535608296269676091 843788514803412444404514137)
        ·
          refine ⟨632841386102559333303385603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843788514803412444404514137 632841386102559333303385603)
          ·
            refine ⟨949262079153838999955078405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632841386102559333303385603 949262079153838999955078405)
            ·
              refine ⟨177986639841344812491577201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 949262079153838999955078405 177986639841344812491577201)
              ·
                refine ⟨133489979881008609368682901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177986639841344812491577201 133489979881008609368682901)
                ·
                  refine ⟨6257342806922278564157011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133489979881008609368682901 6257342806922278564157011)
                  ·
                    refine ⟨9386014210383417846235517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6257342806922278564157011 9386014210383417846235517)
                    ·
                      refine ⟨3519755328893781692338319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9386014210383417846235517 3519755328893781692338319)
                      ·
                        rfl

theorem cell23_6854699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 1, 3].length) (baseStart_6854699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854699 prefixEnd_6854699 := by exact prefixLift 6854699
  have htrace : WordTrace (prefixWord ++ tailWord_6854699) baseStart_6854699 baseEnd_6854699 := by
    simpa [prefixWord, tailWord_6854699, baseEnd_6854699] using wordTrace_append hprefix tailTrace_6854699
  have hstable : (prefixWord ++ tailWord_6854699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854699).length < 2 ^ (prefixWord ++ tailWord_6854699).sum := by decide
  have hdescent : baseEnd_6854699 < baseStart_6854699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854756 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 1, 4, 2]
def baseStart_6854756 : Nat := 118140960795 + 6854756 * 2 ^ 59
def prefixEnd_6854756 : Nat := 4983230072969 + 3 ^ 40 * 6854756 * 2
def baseEnd_6854756 : Nat := 3519784597291087969325557

theorem tailTrace_6854756 : CollatzResearch.WordTrace tailWord_6854756 prefixEnd_6854756 3519784597291087969325557 := by
  unfold tailWord_6854756
  simp only [CollatzResearch.WordTrace]
  refine ⟨125006745377198592982896061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166675660502931457310528081 125006745377198592982896061)
  ·
    refine ⟨46877529516449472368586023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125006745377198592982896061 46877529516449472368586023)
    ·
      refine ⟨70316294274674208552879035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46877529516449472368586023 70316294274674208552879035)
      ·
        refine ⟨105474441412011312829318553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70316294274674208552879035 105474441412011312829318553)
        ·
          refine ⟨79105831059008484621988915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105474441412011312829318553 79105831059008484621988915)
          ·
            refine ⟨118658746588512726932983373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79105831059008484621988915 118658746588512726932983373)
            ·
              refine ⟨44497029970692272599868765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118658746588512726932983373 44497029970692272599868765)
              ·
                refine ⟨16686386239009602224950787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44497029970692272599868765 16686386239009602224950787)
                ·
                  refine ⟨25029579358514403337426181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16686386239009602224950787 25029579358514403337426181)
                  ·
                    refine ⟨4693046129721450625767409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25029579358514403337426181 4693046129721450625767409)
                    ·
                      refine ⟨3519784597291087969325557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4693046129721450625767409 3519784597291087969325557)
                      ·
                        rfl

theorem cell23_6854756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_6854756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854756 prefixEnd_6854756 := by exact prefixLift 6854756
  have htrace : WordTrace (prefixWord ++ tailWord_6854756) baseStart_6854756 baseEnd_6854756 := by
    simpa [prefixWord, tailWord_6854756, baseEnd_6854756] using wordTrace_append hprefix tailTrace_6854756
  have hstable : (prefixWord ++ tailWord_6854756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854756).length < 2 ^ (prefixWord ++ tailWord_6854756).sum := by decide
  have hdescent : baseEnd_6854756 < baseStart_6854756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854759 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_6854759 : Nat := 118140960795 + 6854759 * 2 ^ 59
def prefixEnd_6854759 : Nat := 4983230072969 + 3 ^ 40 * 6854759 * 2
def baseEnd_6854759 : Nat := 3519786137733051457588043

theorem tailTrace_6854759 : CollatzResearch.WordTrace tailWord_6854759 prefixEnd_6854759 3519786137733051457588043 := by
  unfold tailWord_6854759
  simp only [CollatzResearch.WordTrace]
  refine ⟨250013600173386317478151331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166675733448924211652100887 250013600173386317478151331)
  ·
    refine ⟨375020400260079476217226997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250013600173386317478151331 375020400260079476217226997)
    ·
      refine ⟨35158162524382450895365031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 375020400260079476217226997 35158162524382450895365031)
      ·
        refine ⟨52737243786573676343047547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35158162524382450895365031 52737243786573676343047547)
        ·
          refine ⟨79105865679860514514571321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52737243786573676343047547 79105865679860514514571321)
          ·
            refine ⟨59329399259895385885928491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79105865679860514514571321 59329399259895385885928491)
            ·
              refine ⟨88994098889843078828892737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59329399259895385885928491 88994098889843078828892737)
              ·
                refine ⟨66745574167382309121669553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88994098889843078828892737 66745574167382309121669553)
                ·
                  refine ⟨50059180625536731841252165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66745574167382309121669553 50059180625536731841252165)
                  ·
                    refine ⟨9386096367288137220234781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50059180625536731841252165 9386096367288137220234781)
                    ·
                      refine ⟨3519786137733051457588043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9386096367288137220234781 3519786137733051457588043)
                      ·
                        rfl

theorem cell23_6854759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_6854759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854759 prefixEnd_6854759 := by exact prefixLift 6854759
  have htrace : WordTrace (prefixWord ++ tailWord_6854759) baseStart_6854759 baseEnd_6854759 := by
    simpa [prefixWord, tailWord_6854759, baseEnd_6854759] using wordTrace_append hprefix tailTrace_6854759
  have hstable : (prefixWord ++ tailWord_6854759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854759).length < 2 ^ (prefixWord ++ tailWord_6854759).sum := by decide
  have hdescent : baseEnd_6854759 < baseStart_6854759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854807 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 2, 2, 2]
def baseStart_6854807 : Nat := 118140960795 + 6854807 * 2 ^ 59
def prefixEnd_6854807 : Nat := 4983230072969 + 3 ^ 40 * 6854807 * 2
def baseEnd_6854807 : Nat := 3519810784804467269787823

theorem tailTrace_6854807 : CollatzResearch.WordTrace tailWord_6854807 prefixEnd_6854807 3519810784804467269787823 := by
  unfold tailWord_6854807
  simp only [CollatzResearch.WordTrace]
  refine ⟨250015350877212421675898675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166676900584808281117265783 250015350877212421675898675)
  ·
    refine ⟨375023026315818632513848013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250015350877212421675898675 375023026315818632513848013)
    ·
      refine ⟨140633634868431987192693005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375023026315818632513848013 140633634868431987192693005)
      ·
        refine ⟨52737613075661995197259877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140633634868431987192693005 52737613075661995197259877)
        ·
          refine ⟨9888302451686624099486227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52737613075661995197259877 9888302451686624099486227)
          ·
            refine ⟨14832453677529936149229341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9888302451686624099486227 14832453677529936149229341)
            ·
              refine ⟨5562170129073726055961003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14832453677529936149229341 5562170129073726055961003)
              ·
                refine ⟨8343255193610589083941505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562170129073726055961003 8343255193610589083941505)
                ·
                  refine ⟨6257441395207941812956129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8343255193610589083941505 6257441395207941812956129)
                  ·
                    refine ⟨4693081046405956359717097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6257441395207941812956129 4693081046405956359717097)
                    ·
                      refine ⟨3519810784804467269787823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4693081046405956359717097 3519810784804467269787823)
                      ·
                        rfl

theorem cell23_6854807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_6854807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854807 prefixEnd_6854807 := by exact prefixLift 6854807
  have htrace : WordTrace (prefixWord ++ tailWord_6854807) baseStart_6854807 baseEnd_6854807 := by
    simpa [prefixWord, tailWord_6854807, baseEnd_6854807] using wordTrace_append hprefix tailTrace_6854807
  have hstable : (prefixWord ++ tailWord_6854807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854807).length < 2 ^ (prefixWord ++ tailWord_6854807).sum := by decide
  have hdescent : baseEnd_6854807 < baseStart_6854807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854909 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_6854909 : Nat := 118140960795 + 6854909 * 2 ^ 59
def prefixEnd_6854909 : Nat := 4983230072969 + 3 ^ 40 * 6854909 * 2
def baseEnd_6854909 : Nat := 3519863159831225870712353

theorem tailTrace_6854909 : CollatzResearch.WordTrace tailWord_6854909 prefixEnd_6854909 3519863159831225870712353 := by
  unfold tailWord_6854909
  simp only [CollatzResearch.WordTrace]
  refine ⟨250019071122842893096111781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166679380748561928730741187 250019071122842893096111781)
  ·
    refine ⟨46878575835533042455520959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250019071122842893096111781 46878575835533042455520959)
    ·
      refine ⟨70317863753299563683281439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46878575835533042455520959 70317863753299563683281439)
      ·
        refine ⟨105476795629949345524922159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70317863753299563683281439 105476795629949345524922159)
        ·
          refine ⟨158215193444924018287383239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105476795629949345524922159 158215193444924018287383239)
          ·
            refine ⟨237322790167386027431074859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158215193444924018287383239 237322790167386027431074859)
            ·
              refine ⟨355984185251079041146612289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237322790167386027431074859 355984185251079041146612289)
              ·
                refine ⟨266988138938309280859959217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355984185251079041146612289 266988138938309280859959217)
                ·
                  refine ⟨200241104203731960644969413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266988138938309280859959217 200241104203731960644969413)
                  ·
                    refine ⟨37545207038199742620931765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200241104203731960644969413 37545207038199742620931765)
                    ·
                      refine ⟨3519863159831225870712353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37545207038199742620931765 3519863159831225870712353)
                      ·
                        rfl

theorem cell23_6854909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_6854909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854909 prefixEnd_6854909 := by exact prefixLift 6854909
  have htrace : WordTrace (prefixWord ++ tailWord_6854909) baseStart_6854909 baseEnd_6854909 := by
    simpa [prefixWord, tailWord_6854909, baseEnd_6854909] using wordTrace_append hprefix tailTrace_6854909
  have hstable : (prefixWord ++ tailWord_6854909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854909).length < 2 ^ (prefixWord ++ tailWord_6854909).sum := by decide
  have hdescent : baseEnd_6854909 < baseStart_6854909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854913 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_6854913 : Nat := 118140960795 + 6854913 * 2 ^ 59
def prefixEnd_6854913 : Nat := 4983230072969 + 3 ^ 40 * 6854913 * 2
def baseEnd_6854913 : Nat := 3519865213753843855062335

theorem tailTrace_6854913 : CollatzResearch.WordTrace tailWord_6854913 prefixEnd_6854913 3519865213753843855062335 := by
  unfold tailWord_6854913
  simp only [CollatzResearch.WordTrace]
  refine ⟨250019217014828401779257393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166679478009885601186171595 250019217014828401779257393)
  ·
    refine ⟨187514412761121301334443045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250019217014828401779257393 187514412761121301334443045)
    ·
      refine ⟨35158952392710244000208071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187514412761121301334443045 35158952392710244000208071)
      ·
        refine ⟨52738428589065366000312107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35158952392710244000208071 52738428589065366000312107)
        ·
          refine ⟨79107642883598049000468161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52738428589065366000312107 79107642883598049000468161)
          ·
            refine ⟨59330732162698536750351121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79107642883598049000468161 59330732162698536750351121)
            ·
              refine ⟨44498049122023902562763341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59330732162698536750351121 44498049122023902562763341)
              ·
                refine ⟨16686768420758963461036253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44498049122023902562763341 16686768420758963461036253)
                ·
                  refine ⟨6257538157784611297888595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16686768420758963461036253 6257538157784611297888595)
                  ·
                    refine ⟨9386307236676916946832893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6257538157784611297888595 9386307236676916946832893)
                    ·
                      refine ⟨3519865213753843855062335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9386307236676916946832893 3519865213753843855062335)
                      ·
                        rfl

theorem cell23_6854913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_6854913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854913 prefixEnd_6854913 := by exact prefixLift 6854913
  have htrace : WordTrace (prefixWord ++ tailWord_6854913) baseStart_6854913 baseEnd_6854913 := by
    simpa [prefixWord, tailWord_6854913, baseEnd_6854913] using wordTrace_append hprefix tailTrace_6854913
  have hstable : (prefixWord ++ tailWord_6854913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854913).length < 2 ^ (prefixWord ++ tailWord_6854913).sum := by decide
  have hdescent : baseEnd_6854913 < baseStart_6854913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854936 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_6854936 : Nat := 118140960795 + 6854936 * 2 ^ 59
def prefixEnd_6854936 : Nat := 4983230072969 + 3 ^ 40 * 6854936 * 2
def baseEnd_6854936 : Nat := 3519877023808897265074729

theorem tailTrace_6854936 : CollatzResearch.WordTrace tailWord_6854936 prefixEnd_6854936 3519877023808897265074729 := by
  unfold tailWord_6854936
  simp only [CollatzResearch.WordTrace]
  refine ⟨125010027946872538353672331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166680037262496717804896441 125010027946872538353672331)
  ·
    refine ⟨187515041920308807530508497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125010027946872538353672331 187515041920308807530508497)
    ·
      refine ⟨140636281440231605647881373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187515041920308807530508497 140636281440231605647881373)
      ·
        refine ⟨52738605540086852117955515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140636281440231605647881373 52738605540086852117955515)
        ·
          refine ⟨79107908310130278176933273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52738605540086852117955515 79107908310130278176933273)
          ·
            refine ⟨59330931232597708632699955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79107908310130278176933273 59330931232597708632699955)
            ·
              refine ⟨88996396848896562949049933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59330931232597708632699955 88996396848896562949049933)
              ·
                refine ⟨33373648818336211105893725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88996396848896562949049933 33373648818336211105893725)
                ·
                  refine ⟨12515118306876079164710147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33373648818336211105893725 12515118306876079164710147)
                  ·
                    refine ⟨18772677460314118747065221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12515118306876079164710147 18772677460314118747065221)
                    ·
                      refine ⟨3519877023808897265074729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18772677460314118747065221 3519877023808897265074729)
                      ·
                        rfl

theorem cell23_6854936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_6854936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854936 prefixEnd_6854936 := by exact prefixLift 6854936
  have htrace : WordTrace (prefixWord ++ tailWord_6854936) baseStart_6854936 baseEnd_6854936 := by
    simpa [prefixWord, tailWord_6854936, baseEnd_6854936] using wordTrace_append hprefix tailTrace_6854936
  have hstable : (prefixWord ++ tailWord_6854936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854936).length < 2 ^ (prefixWord ++ tailWord_6854936).sum := by decide
  have hdescent : baseEnd_6854936 < baseStart_6854936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854970 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2]
def baseStart_6854970 : Nat := 118140960795 + 6854970 * 2 ^ 59
def prefixEnd_6854970 : Nat := 4983230072969 + 3 ^ 40 * 6854970 * 2
def baseEnd_6854970 : Nat := 3519894482151150132049573

theorem tailTrace_6854970 : CollatzResearch.WordTrace tailWord_6854970 prefixEnd_6854970 3519894482151150132049573 := by
  unfold tailWord_6854970
  simp only [CollatzResearch.WordTrace]
  refine ⟨62505323993905475128520591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166680863983747933676054909 62505323993905475128520591)
  ·
    refine ⟨93757985990858212692780887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62505323993905475128520591 93757985990858212692780887)
    ·
      refine ⟨140636978986287319039171331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93757985990858212692780887 140636978986287319039171331)
      ·
        refine ⟨210955468479430978558756997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140636978986287319039171331 210955468479430978558756997)
        ·
          refine ⟨39554150339893308479766937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210955468479430978558756997 39554150339893308479766937)
          ·
            refine ⟨29665612754919981359825203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39554150339893308479766937 29665612754919981359825203)
            ·
              refine ⟨44498419132379972039737805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29665612754919981359825203 44498419132379972039737805)
              ·
                refine ⟨16686907174642489514901677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44498419132379972039737805 16686907174642489514901677)
                ·
                  refine ⟨6257590190490933568088129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16686907174642489514901677 6257590190490933568088129)
                  ·
                    refine ⟨4693192642868200176066097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6257590190490933568088129 4693192642868200176066097)
                    ·
                      refine ⟨3519894482151150132049573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4693192642868200176066097 3519894482151150132049573)
                      ·
                        rfl

theorem cell23_6854970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2].length) (baseStart_6854970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854970 prefixEnd_6854970 := by exact prefixLift 6854970
  have htrace : WordTrace (prefixWord ++ tailWord_6854970) baseStart_6854970 baseEnd_6854970 := by
    simpa [prefixWord, tailWord_6854970, baseEnd_6854970] using wordTrace_append hprefix tailTrace_6854970
  have hstable : (prefixWord ++ tailWord_6854970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854970).length < 2 ^ (prefixWord ++ tailWord_6854970).sum := by decide
  have hdescent : baseEnd_6854970 < baseStart_6854970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6854993 : List Nat := [1, 2, 2, 1, 4, 4, 2, 7]
def baseStart_6854993 : Nat := 118140960795 + 6854993 * 2 ^ 59
def prefixEnd_6854993 : Nat := 4983230072969 + 3 ^ 40 * 6854993 * 2
def baseEnd_6854993 : Nat := 130366899711340871928221

theorem tailTrace_6854993 : CollatzResearch.WordTrace tailWord_6854993 prefixEnd_6854993 130366899711340871928221 := by
  unfold tailWord_6854993
  simp only [CollatzResearch.WordTrace]
  refine ⟨250022134854538575442169633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166681423236359050294779755 250022134854538575442169633)
  ·
    refine ⟨187516601140903931581627225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250022134854538575442169633 187516601140903931581627225)
    ·
      refine ⟨140637450855677948686220419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187516601140903931581627225 140637450855677948686220419)
      ·
        refine ⟨210956176283516923029330629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140637450855677948686220419 210956176283516923029330629)
        ·
          refine ⟨39554283053159423067999493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210956176283516923029330629 39554283053159423067999493)
          ·
            refine ⟨7416428072467391825249905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39554283053159423067999493 7416428072467391825249905)
            ·
              refine ⟨5562321054350543868937429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7416428072467391825249905 5562321054350543868937429)
              ·
                refine ⟨130366899711340871928221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5562321054350543868937429 130366899711340871928221)
                ·
                  rfl

theorem cell23_6854993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 7].length) (baseStart_6854993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6854993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6854993 prefixEnd_6854993 := by exact prefixLift 6854993
  have htrace : WordTrace (prefixWord ++ tailWord_6854993) baseStart_6854993 baseEnd_6854993 := by
    simpa [prefixWord, tailWord_6854993, baseEnd_6854993] using wordTrace_append hprefix tailTrace_6854993
  have hstable : (prefixWord ++ tailWord_6854993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6854993).length < 2 ^ (prefixWord ++ tailWord_6854993).sum := by decide
  have hdescent : baseEnd_6854993 < baseStart_6854993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6854993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855037 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 2, 1, 3]
def baseStart_6855037 : Nat := 118140960795 + 6855037 * 2 ^ 59
def prefixEnd_6855037 : Nat := 4983230072969 + 3 ^ 40 * 6855037 * 2
def baseEnd_6855037 : Nat := 3519928885355001369911765

theorem tailTrace_6855037 : CollatzResearch.WordTrace tailWord_6855037 prefixEnd_6855037 3519928885355001369911765 := by
  unfold tailWord_6855037
  simp only [CollatzResearch.WordTrace]
  refine ⟨250023739666379170956771365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166682493110919447304514243 250023739666379170956771365)
  ·
    refine ⟨46879451187446094554394631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250023739666379170956771365 46879451187446094554394631)
    ·
      refine ⟨70319176781169141831591947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46879451187446094554394631 70319176781169141831591947)
      ·
        refine ⟨105478765171753712747387921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70319176781169141831591947 105478765171753712747387921)
        ·
          refine ⟨79109073878815284560540941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105478765171753712747387921 79109073878815284560540941)
          ·
            refine ⟨29665902704555731710202853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79109073878815284560540941 29665902704555731710202853)
            ·
              refine ⟨5562356757104199695663035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29665902704555731710202853 5562356757104199695663035)
              ·
                refine ⟨8343535135656299543494553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562356757104199695663035 8343535135656299543494553)
                ·
                  refine ⟨6257651351742224657620915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8343535135656299543494553 6257651351742224657620915)
                  ·
                    refine ⟨9386477027613336986431373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6257651351742224657620915 9386477027613336986431373)
                    ·
                      refine ⟨3519928885355001369911765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9386477027613336986431373 3519928885355001369911765)
                      ·
                        rfl

theorem cell23_6855037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_6855037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855037 prefixEnd_6855037 := by exact prefixLift 6855037
  have htrace : WordTrace (prefixWord ++ tailWord_6855037) baseStart_6855037 baseEnd_6855037 := by
    simpa [prefixWord, tailWord_6855037, baseEnd_6855037] using wordTrace_append hprefix tailTrace_6855037
  have hstable : (prefixWord ++ tailWord_6855037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855037).length < 2 ^ (prefixWord ++ tailWord_6855037).sum := by decide
  have hdescent : baseEnd_6855037 < baseStart_6855037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855064 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 1, 3, 2]
def baseStart_6855064 : Nat := 118140960795 + 6855064 * 2 ^ 59
def prefixEnd_6855064 : Nat := 4983230072969 + 3 ^ 40 * 6855064 * 2
def baseEnd_6855064 : Nat := 3519942749332672764274141

theorem tailTrace_6855064 : CollatzResearch.WordTrace tailWord_6855064 prefixEnd_6855064 3519942749332672764274141 := by
  unfold tailWord_6855064
  simp only [CollatzResearch.WordTrace]
  refine ⟨125012362218640677284002123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166683149624854236378669497 125012362218640677284002123)
  ·
    refine ⟨187518543327961015926003185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125012362218640677284002123 187518543327961015926003185)
    ·
      refine ⟨140638907495970761944502389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187518543327961015926003185 140638907495970761944502389)
      ·
        refine ⟨13184897577747258932297099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140638907495970761944502389 13184897577747258932297099)
        ·
          refine ⟨19777346366620888398445649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13184897577747258932297099 19777346366620888398445649)
          ·
            refine ⟨14833009774965666298834237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19777346366620888398445649 14833009774965666298834237)
            ·
              refine ⟨5562378665612124862062839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14833009774965666298834237 5562378665612124862062839)
              ·
                refine ⟨8343567998418187293094259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562378665612124862062839 8343567998418187293094259)
                ·
                  refine ⟨12515351997627280939641389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8343567998418187293094259 12515351997627280939641389)
                  ·
                    refine ⟨4693256999110230352365521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12515351997627280939641389 4693256999110230352365521)
                    ·
                      refine ⟨3519942749332672764274141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4693256999110230352365521 3519942749332672764274141)
                      ·
                        rfl

theorem cell23_6855064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_6855064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855064 prefixEnd_6855064 := by exact prefixLift 6855064
  have htrace : WordTrace (prefixWord ++ tailWord_6855064) baseStart_6855064 baseEnd_6855064 := by
    simpa [prefixWord, tailWord_6855064, baseEnd_6855064] using wordTrace_append hprefix tailTrace_6855064
  have hstable : (prefixWord ++ tailWord_6855064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855064).length < 2 ^ (prefixWord ++ tailWord_6855064).sum := by decide
  have hdescent : baseEnd_6855064 < baseStart_6855064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855076 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_6855076 : Nat := 118140960795 + 6855076 * 2 ^ 59
def prefixEnd_6855076 : Nat := 4983230072969 + 3 ^ 40 * 6855076 * 2
def baseEnd_6855076 : Nat := 3519948911100526717324085

theorem tailTrace_6855076 : CollatzResearch.WordTrace tailWord_6855076 prefixEnd_6855076 3519948911100526717324085 := by
  unfold tailWord_6855076
  simp only [CollatzResearch.WordTrace]
  refine ⟨125012581056618940308720541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166683441408825253744960721 125012581056618940308720541)
  ·
    refine ⟨46879717896232102615770203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125012581056618940308720541 46879717896232102615770203)
    ·
      refine ⟨70319576844348153923655305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46879717896232102615770203 70319576844348153923655305)
      ·
        refine ⟨52739682633261115442741479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70319576844348153923655305 52739682633261115442741479)
        ·
          refine ⟨79109523949891673164112219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52739682633261115442741479 79109523949891673164112219)
          ·
            refine ⟨118664285924837509746168329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79109523949891673164112219 118664285924837509746168329)
            ·
              refine ⟨88998214443628132309626247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118664285924837509746168329 88998214443628132309626247)
              ·
                refine ⟨133497321665442198464439371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88998214443628132309626247 133497321665442198464439371)
                ·
                  refine ⟨200245982498163297696659057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133497321665442198464439371 200245982498163297696659057)
                  ·
                    refine ⟨150184486873622473272494293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200245982498163297696659057 150184486873622473272494293)
                    ·
                      refine ⟨3519948911100526717324085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150184486873622473272494293 3519948911100526717324085)
                      ·
                        rfl

theorem cell23_6855076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_6855076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855076 prefixEnd_6855076 := by exact prefixLift 6855076
  have htrace : WordTrace (prefixWord ++ tailWord_6855076) baseStart_6855076 baseEnd_6855076 := by
    simpa [prefixWord, tailWord_6855076, baseEnd_6855076] using wordTrace_append hprefix tailTrace_6855076
  have hstable : (prefixWord ++ tailWord_6855076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855076).length < 2 ^ (prefixWord ++ tailWord_6855076).sum := by decide
  have hdescent : baseEnd_6855076 < baseStart_6855076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855077 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 2, 2, 2]
def baseStart_6855077 : Nat := 118140960795 + 6855077 * 2 ^ 59
def prefixEnd_6855077 : Nat := 4983230072969 + 3 ^ 40 * 6855077 * 2
def baseEnd_6855077 : Nat := 3519949424581181213411581

theorem tailTrace_6855077 : CollatzResearch.WordTrace tailWord_6855077 prefixEnd_6855077 3519949424581181213411581 := by
  unfold tailWord_6855077
  simp only [CollatzResearch.WordTrace]
  refine ⟨250025198586234257788227485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166683465724156171858818323 250025198586234257788227485)
  ·
    refine ⟨93759449469837846670585307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250025198586234257788227485 93759449469837846670585307)
    ·
      refine ⟨140639174204756770005877961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93759449469837846670585307 140639174204756770005877961)
      ·
        refine ⟨105479380653567577504408471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140639174204756770005877961 105479380653567577504408471)
        ·
          refine ⟨158219070980351366256612707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105479380653567577504408471 158219070980351366256612707)
          ·
            refine ⟨237328606470527049384919061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158219070980351366256612707 237328606470527049384919061)
            ·
              refine ⟨11124778428305955439918081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237328606470527049384919061 11124778428305955439918081)
              ·
                refine ⟨8343583821229466579938561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11124778428305955439918081 8343583821229466579938561)
                ·
                  refine ⟨6257687865922099934953921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8343583821229466579938561 6257687865922099934953921)
                  ·
                    refine ⟨4693265899441574951215441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6257687865922099934953921 4693265899441574951215441)
                    ·
                      refine ⟨3519949424581181213411581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4693265899441574951215441 3519949424581181213411581)
                      ·
                        rfl

theorem cell23_6855077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_6855077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855077 prefixEnd_6855077 := by exact prefixLift 6855077
  have htrace : WordTrace (prefixWord ++ tailWord_6855077) baseStart_6855077 baseEnd_6855077 := by
    simpa [prefixWord, tailWord_6855077, baseEnd_6855077] using wordTrace_append hprefix tailTrace_6855077
  have hstable : (prefixWord ++ tailWord_6855077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855077).length < 2 ^ (prefixWord ++ tailWord_6855077).sum := by decide
  have hdescent : baseEnd_6855077 < baseStart_6855077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855080 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_6855080 : Nat := 118140960795 + 6855080 * 2 ^ 59
def prefixEnd_6855080 : Nat := 4983230072969 + 3 ^ 40 * 6855080 * 2
def baseEnd_6855080 : Nat := 3519950965023144701674067

theorem tailTrace_6855080 : CollatzResearch.WordTrace tailWord_6855080 prefixEnd_6855080 3519950965023144701674067 := by
  unfold tailWord_6855080
  simp only [CollatzResearch.WordTrace]
  refine ⟨125012654002611694650293347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166683538670148926200391129 125012654002611694650293347)
  ·
    refine ⟨187518981003917541975440021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125012654002611694650293347 187518981003917541975440021)
    ·
      refine ⟨8789952234558634780098751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 187518981003917541975440021 8789952234558634780098751)
      ·
        refine ⟨13184928351837952170148127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8789952234558634780098751 13184928351837952170148127)
        ·
          refine ⟨19777392527756928255222191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13184928351837952170148127 19777392527756928255222191)
          ·
            refine ⟨29666088791635392382833287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19777392527756928255222191 29666088791635392382833287)
            ·
              refine ⟨44499133187453088574249931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29666088791635392382833287 44499133187453088574249931)
              ·
                refine ⟨66748699781179632861374897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44499133187453088574249931 66748699781179632861374897)
                ·
                  refine ⟨50061524835884724646031173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66748699781179632861374897 50061524835884724646031173)
                  ·
                    refine ⟨9386535906728385871130845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50061524835884724646031173 9386535906728385871130845)
                    ·
                      refine ⟨3519950965023144701674067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9386535906728385871130845 3519950965023144701674067)
                      ·
                        rfl

theorem cell23_6855080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_6855080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855080 prefixEnd_6855080 := by exact prefixLift 6855080
  have htrace : WordTrace (prefixWord ++ tailWord_6855080) baseStart_6855080 baseEnd_6855080 := by
    simpa [prefixWord, tailWord_6855080, baseEnd_6855080] using wordTrace_append hprefix tailTrace_6855080
  have hstable : (prefixWord ++ tailWord_6855080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855080).length < 2 ^ (prefixWord ++ tailWord_6855080).sum := by decide
  have hdescent : baseEnd_6855080 < baseStart_6855080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855096 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 1, 7]
def baseStart_6855096 : Nat := 118140960795 + 6855096 * 2 ^ 59
def prefixEnd_6855096 : Nat := 4983230072969 + 3 ^ 40 * 6855096 * 2
def baseEnd_6855096 : Nat := 1173319726904538879691331

theorem tailTrace_6855096 : CollatzResearch.WordTrace tailWord_6855096 prefixEnd_6855096 1173319726904538879691331 := by
  unfold tailWord_6855096
  simp only [CollatzResearch.WordTrace]
  refine ⟨125012945786582712016584571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166683927715443616022112761 125012945786582712016584571)
  ·
    refine ⟨187519418679874068024876857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125012945786582712016584571 187519418679874068024876857)
    ·
      refine ⟨140639564009905551018657643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187519418679874068024876857 140639564009905551018657643)
      ·
        refine ⟨210959346014858326527986465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140639564009905551018657643 210959346014858326527986465)
        ·
          refine ⟨158219509511143744895989849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210959346014858326527986465 158219509511143744895989849)
          ·
            refine ⟨118664632133357808671992387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158219509511143744895989849 118664632133357808671992387)
            ·
              refine ⟨177996948200036713007988581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118664632133357808671992387 177996948200036713007988581)
              ·
                refine ⟨33374427787506883688997859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177996948200036713007988581 33374427787506883688997859)
                ·
                  refine ⟨50061641681260325533496789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33374427787506883688997859 50061641681260325533496789)
                  ·
                    refine ⟨1173319726904538879691331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50061641681260325533496789 1173319726904538879691331)
                    ·
                      rfl

theorem cell23_6855096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_6855096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855096 prefixEnd_6855096 := by exact prefixLift 6855096
  have htrace : WordTrace (prefixWord ++ tailWord_6855096) baseStart_6855096 baseEnd_6855096 := by
    simpa [prefixWord, tailWord_6855096, baseEnd_6855096] using wordTrace_append hprefix tailTrace_6855096
  have hstable : (prefixWord ++ tailWord_6855096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855096).length < 2 ^ (prefixWord ++ tailWord_6855096).sum := by decide
  have hdescent : baseEnd_6855096 < baseStart_6855096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855113 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 2, 5]
def baseStart_6855113 : Nat := 118140960795 + 6855113 * 2 ^ 59
def prefixEnd_6855113 : Nat := 4983230072969 + 3 ^ 40 * 6855113 * 2
def baseEnd_6855113 : Nat := 1173322636628247690853805

theorem tailTrace_6855113 : CollatzResearch.WordTrace tailWord_6855113 prefixEnd_6855113 1173322636628247690853805 := by
  unfold tailWord_6855113
  simp only [CollatzResearch.WordTrace]
  refine ⟨250026511614103835936537993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166684341076069223957691995 250026511614103835936537993)
  ·
    refine ⟨187519883710577876952403495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250026511614103835936537993 187519883710577876952403495)
    ·
      refine ⟨281279825565866815428605243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187519883710577876952403495 281279825565866815428605243)
      ·
        refine ⟨421919738348800223142907865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281279825565866815428605243 421919738348800223142907865)
        ·
          refine ⟨316439803761600167357180899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421919738348800223142907865 316439803761600167357180899)
          ·
            refine ⟨474659705642400251035771349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316439803761600167357180899 474659705642400251035771349)
            ·
              refine ⟨11124836850993755883650891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 474659705642400251035771349 11124836850993755883650891)
              ·
                refine ⟨16687255276490633825476337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11124836850993755883650891 16687255276490633825476337)
                ·
                  refine ⟨12515441457367975369107253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16687255276490633825476337 12515441457367975369107253)
                  ·
                    refine ⟨1173322636628247690853805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12515441457367975369107253 1173322636628247690853805)
                    ·
                      rfl

theorem cell23_6855113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 5].length) (baseStart_6855113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855113 prefixEnd_6855113 := by exact prefixLift 6855113
  have htrace : WordTrace (prefixWord ++ tailWord_6855113) baseStart_6855113 baseEnd_6855113 := by
    simpa [prefixWord, tailWord_6855113, baseEnd_6855113] using wordTrace_append hprefix tailTrace_6855113
  have hstable : (prefixWord ++ tailWord_6855113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855113).length < 2 ^ (prefixWord ++ tailWord_6855113).sum := by decide
  have hdescent : baseEnd_6855113 < baseStart_6855113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855153 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 3, 4, 3]
def baseStart_6855153 : Nat := 118140960795 + 6855153 * 2 ^ 59
def prefixEnd_6855153 : Nat := 4983230072969 + 3 ^ 40 * 6855153 * 2
def baseEnd_6855153 : Nat := 3519988449110922916061231

theorem tailTrace_6855153 : CollatzResearch.WordTrace tailWord_6855153 prefixEnd_6855153 3519988449110922916061231 := by
  unfold tailWord_6855153
  simp only [CollatzResearch.WordTrace]
  refine ⟨250027970533958922767994113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166685313689305948511996075 250027970533958922767994113)
  ·
    refine ⟨187520977900469192075995585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250027970533958922767994113 187520977900469192075995585)
    ·
      refine ⟨140640733425351894056996689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187520977900469192075995585 140640733425351894056996689)
      ·
        refine ⟨105480550069013920542747517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140640733425351894056996689 105480550069013920542747517)
        ·
          refine ⟨39555206275880220203530319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105480550069013920542747517 39555206275880220203530319)
          ·
            refine ⟨59332809413820330305295479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39555206275880220203530319 59332809413820330305295479)
            ·
              refine ⟨88999214120730495457943219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59332809413820330305295479 88999214120730495457943219)
              ·
                refine ⟨133498821181095743186914829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88999214120730495457943219 133498821181095743186914829)
                ·
                  refine ⟨50062057942910903695093061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133498821181095743186914829 50062057942910903695093061)
                  ·
                    refine ⟨9386635864295794442829949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50062057942910903695093061 9386635864295794442829949)
                    ·
                      refine ⟨3519988449110922916061231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9386635864295794442829949 3519988449110922916061231)
                      ·
                        rfl

theorem cell23_6855153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_6855153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855153 prefixEnd_6855153 := by exact prefixLift 6855153
  have htrace : WordTrace (prefixWord ++ tailWord_6855153) baseStart_6855153 baseEnd_6855153 := by
    simpa [prefixWord, tailWord_6855153, baseEnd_6855153] using wordTrace_append hprefix tailTrace_6855153
  have hstable : (prefixWord ++ tailWord_6855153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855153).length < 2 ^ (prefixWord ++ tailWord_6855153).sum := by decide
  have hdescent : baseEnd_6855153 < baseStart_6855153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855237 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 1, 5]
def baseStart_6855237 : Nat := 118140960795 + 6855237 * 2 ^ 59
def prefixEnd_6855237 : Nat := 4983230072969 + 3 ^ 40 * 6855237 * 2
def baseEnd_6855237 : Nat := 1173343860495300195803615

theorem tailTrace_6855237 : CollatzResearch.WordTrace tailWord_6855237 prefixEnd_6855237 1173343860495300195803615 := by
  unfold tailWord_6855237
  simp only [CollatzResearch.WordTrace]
  refine ⟨250031034265654605114051965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166687356177103070076034643 250031034265654605114051965)
  ·
    refine ⟨93761637849620476917769487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250031034265654605114051965 93761637849620476917769487)
    ·
      refine ⟨140642456774430715376654231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93761637849620476917769487 140642456774430715376654231)
      ·
        refine ⟨210963685161646073064981347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140642456774430715376654231 210963685161646073064981347)
        ·
          refine ⟨316445527742469109597472021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210963685161646073064981347 316445527742469109597472021)
          ·
            refine ⟨14833384112928239512381501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 316445527742469109597472021 14833384112928239512381501)
            ·
              refine ⟨5562519042348089817143063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14833384112928239512381501 5562519042348089817143063)
              ·
                refine ⟨8343778563522134725714595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562519042348089817143063 8343778563522134725714595)
                ·
                  refine ⟨12515667845283202088571893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8343778563522134725714595 12515667845283202088571893)
                  ·
                    refine ⟨1173343860495300195803615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12515667845283202088571893 1173343860495300195803615)
                    ·
                      rfl

theorem cell23_6855237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_6855237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855237 prefixEnd_6855237 := by exact prefixLift 6855237
  have htrace : WordTrace (prefixWord ++ tailWord_6855237) baseStart_6855237 baseEnd_6855237 := by
    simpa [prefixWord, tailWord_6855237, baseEnd_6855237] using wordTrace_append hprefix tailTrace_6855237
  have hstable : (prefixWord ++ tailWord_6855237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855237).length < 2 ^ (prefixWord ++ tailWord_6855237).sum := by decide
  have hdescent : baseEnd_6855237 < baseStart_6855237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855240 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_6855240 : Nat := 118140960795 + 6855240 * 2 ^ 59
def prefixEnd_6855240 : Nat := 4983230072969 + 3 ^ 40 * 6855240 * 2
def baseEnd_6855240 : Nat := 3520033121927864075673331

theorem tailTrace_6855240 : CollatzResearch.WordTrace tailWord_6855240 prefixEnd_6855240 3520033121927864075673331 := by
  unfold tailWord_6855240
  simp only [CollatzResearch.WordTrace]
  refine ⟨125015571842321868313205587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166687429123095824417607449 125015571842321868313205587)
  ·
    refine ⟨187523357763482802469808381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125015571842321868313205587 187523357763482802469808381)
    ·
      refine ⟨70321259161306050926178143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187523357763482802469808381 70321259161306050926178143)
      ·
        refine ⟨105481888741959076389267215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70321259161306050926178143 105481888741959076389267215)
        ·
          refine ⟨158222833112938614583900823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105481888741959076389267215 158222833112938614583900823)
          ·
            refine ⟨237334249669407921875851235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158222833112938614583900823 237334249669407921875851235)
            ·
              refine ⟨356001374504111882813776853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237334249669407921875851235 356001374504111882813776853)
              ·
                refine ⟨8343782214940122253447895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 356001374504111882813776853 8343782214940122253447895)
                ·
                  refine ⟨12515673322410183380171843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8343782214940122253447895 12515673322410183380171843)
                  ·
                    refine ⟨18773509983615275070257765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12515673322410183380171843 18773509983615275070257765)
                    ·
                      refine ⟨3520033121927864075673331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18773509983615275070257765 3520033121927864075673331)
                      ·
                        rfl

theorem cell23_6855240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_6855240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855240 prefixEnd_6855240 := by exact prefixLift 6855240
  have htrace : WordTrace (prefixWord ++ tailWord_6855240) baseStart_6855240 baseEnd_6855240 := by
    simpa [prefixWord, tailWord_6855240, baseEnd_6855240] using wordTrace_append hprefix tailTrace_6855240
  have hstable : (prefixWord ++ tailWord_6855240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855240).length < 2 ^ (prefixWord ++ tailWord_6855240).sum := by decide
  have hdescent : baseEnd_6855240 < baseStart_6855240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855253 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6855253 : Nat := 118140960795 + 6855253 * 2 ^ 59
def prefixEnd_6855253 : Nat := 4983230072969 + 3 ^ 40 * 6855253 * 2
def baseEnd_6855253 : Nat := 3520039797176372524810771

theorem tailTrace_6855253 : CollatzResearch.WordTrace tailWord_6855253 prefixEnd_6855253 3520039797176372524810771 := by
  unfold tailWord_6855253
  simp only [CollatzResearch.WordTrace]
  refine ⟨250031617833596639846634413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166687745222397759897756275 250031617833596639846634413)
  ·
    refine ⟨93761856687598739942487905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250031617833596639846634413 93761856687598739942487905)
    ·
      refine ⟨70321392515699054956865929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93761856687598739942487905 70321392515699054956865929)
      ·
        refine ⟨52741044386774291217649447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70321392515699054956865929 52741044386774291217649447)
        ·
          refine ⟨79111566580161436826474171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52741044386774291217649447 79111566580161436826474171)
          ·
            refine ⟨118667349870242155239711257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79111566580161436826474171 118667349870242155239711257)
            ·
              refine ⟨89000512402681616429783443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118667349870242155239711257 89000512402681616429783443)
              ·
                refine ⟨133500768604022424644675165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89000512402681616429783443 133500768604022424644675165)
                ·
                  refine ⟨50062788226508409241753187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133500768604022424644675165 50062788226508409241753187)
                  ·
                    refine ⟨75094182339762613862629781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50062788226508409241753187 75094182339762613862629781)
                    ·
                      refine ⟨3520039797176372524810771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75094182339762613862629781 3520039797176372524810771)
                      ·
                        rfl

theorem cell23_6855253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6855253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855253 prefixEnd_6855253 := by exact prefixLift 6855253
  have htrace : WordTrace (prefixWord ++ tailWord_6855253) baseStart_6855253 baseEnd_6855253 := by
    simpa [prefixWord, tailWord_6855253, baseEnd_6855253] using wordTrace_append hprefix tailTrace_6855253
  have hstable : (prefixWord ++ tailWord_6855253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855253).length < 2 ^ (prefixWord ++ tailWord_6855253).sum := by decide
  have hdescent : baseEnd_6855253 < baseStart_6855253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855274 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_6855274 : Nat := 118140960795 + 6855274 * 2 ^ 59
def prefixEnd_6855274 : Nat := 4983230072969 + 3 ^ 40 * 6855274 * 2
def baseEnd_6855274 : Nat := 3520050580270116942648175

theorem tailTrace_6855274 : CollatzResearch.WordTrace tailWord_6855274 prefixEnd_6855274 3520050580270116942648175 := by
  unfold tailWord_6855274
  simp only [CollatzResearch.WordTrace]
  refine ⟨62508095941630140108287219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166688255844347040288765917 62508095941630140108287219)
  ·
    refine ⟨93762143912445210162430829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62508095941630140108287219 93762143912445210162430829)
    ·
      refine ⟨35160803967166953810911561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93762143912445210162430829 35160803967166953810911561)
      ·
        refine ⟨26370602975375215358183671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35160803967166953810911561 26370602975375215358183671)
        ·
          refine ⟨39555904463062823037275507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26370602975375215358183671 39555904463062823037275507)
          ·
            refine ⟨59333856694594234555913261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39555904463062823037275507 59333856694594234555913261)
            ·
              refine ⟨22250196260472837958467473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59333856694594234555913261 22250196260472837958467473)
              ·
                refine ⟨16687647195354628468850605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22250196260472837958467473 16687647195354628468850605)
                ·
                  refine ⟨6257867698257985675818977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16687647195354628468850605 6257867698257985675818977)
                  ·
                    refine ⟨4693400773693489256864233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6257867698257985675818977 4693400773693489256864233)
                    ·
                      refine ⟨3520050580270116942648175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4693400773693489256864233 3520050580270116942648175)
                      ·
                        rfl

theorem cell23_6855274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_6855274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855274 prefixEnd_6855274 := by exact prefixLift 6855274
  have htrace : WordTrace (prefixWord ++ tailWord_6855274) baseStart_6855274 baseEnd_6855274 := by
    simpa [prefixWord, tailWord_6855274, baseEnd_6855274] using wordTrace_append hprefix tailTrace_6855274
  have hstable : (prefixWord ++ tailWord_6855274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855274).length < 2 ^ (prefixWord ++ tailWord_6855274).sum := by decide
  have hdescent : baseEnd_6855274 < baseStart_6855274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855277 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_6855277 : Nat := 118140960795 + 6855277 * 2 ^ 59
def prefixEnd_6855277 : Nat := 4983230072969 + 3 ^ 40 * 6855277 * 2
def baseEnd_6855277 : Nat := 3520052120712080430910661

theorem tailTrace_6855277 : CollatzResearch.WordTrace tailWord_6855277 prefixEnd_6855277 3520052120712080430910661 := by
  unfold tailWord_6855277
  simp only [CollatzResearch.WordTrace]
  refine ⟨250032493185509691945508085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166688328790339794630338723 250032493185509691945508085)
  ·
    refine ⟨23440546236141533619891383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250032493185509691945508085 23440546236141533619891383)
    ·
      refine ⟨35160819354212300429837075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23440546236141533619891383 35160819354212300429837075)
      ·
        refine ⟨52741229031318450644755613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35160819354212300429837075 52741229031318450644755613)
        ·
          refine ⟨19777960886744418991783355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52741229031318450644755613 19777960886744418991783355)
          ·
            refine ⟨29666941330116628487675033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19777960886744418991783355 29666941330116628487675033)
            ·
              refine ⟨22250205997587471365756275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29666941330116628487675033 22250205997587471365756275)
              ·
                refine ⟨33375308996381207048634413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22250205997587471365756275 33375308996381207048634413)
                ·
                  refine ⟨12515740873642952643237905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33375308996381207048634413 12515740873642952643237905)
                  ·
                    refine ⟨9386805655232214482428429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12515740873642952643237905 9386805655232214482428429)
                    ·
                      refine ⟨3520052120712080430910661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9386805655232214482428429 3520052120712080430910661)
                      ·
                        rfl

theorem cell23_6855277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_6855277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855277 prefixEnd_6855277 := by exact prefixLift 6855277
  have htrace : WordTrace (prefixWord ++ tailWord_6855277) baseStart_6855277 baseEnd_6855277 := by
    simpa [prefixWord, tailWord_6855277, baseEnd_6855277] using wordTrace_append hprefix tailTrace_6855277
  have hstable : (prefixWord ++ tailWord_6855277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855277).length < 2 ^ (prefixWord ++ tailWord_6855277).sum := by decide
  have hdescent : baseEnd_6855277 < baseStart_6855277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855307 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 2, 1, 3]
def baseStart_6855307 : Nat := 118140960795 + 6855307 * 2 ^ 59
def prefixEnd_6855307 : Nat := 4983230072969 + 3 ^ 40 * 6855307 * 2
def baseEnd_6855307 : Nat := 3520067525131715313535523

theorem tailTrace_6855307 : CollatzResearch.WordTrace tailWord_6855307 prefixEnd_6855307 3520067525131715313535523 := by
  unfold tailWord_6855307
  simp only [CollatzResearch.WordTrace]
  refine ⟨250033587375401007069100175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166689058250267338046066783 250033587375401007069100175)
  ·
    refine ⟨375050381063101510603650263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250033587375401007069100175 375050381063101510603650263)
    ·
      refine ⟨562575571594652265905475395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375050381063101510603650263 562575571594652265905475395)
      ·
        refine ⟨843863357391978398858213093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562575571594652265905475395 843863357391978398858213093)
        ·
          refine ⟨158224379510995949785914955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 843863357391978398858213093 158224379510995949785914955)
          ·
            refine ⟨237336569266493924678872433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158224379510995949785914955 237336569266493924678872433)
            ·
              refine ⟨178002426949870443509154325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237336569266493924678872433 178002426949870443509154325)
              ·
                refine ⟨8343863763275177039491609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178002426949870443509154325 8343863763275177039491609)
                ·
                  refine ⟨6257897822456382779618707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8343863763275177039491609 6257897822456382779618707)
                  ·
                    refine ⟨9386846733684574169428061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6257897822456382779618707 9386846733684574169428061)
                    ·
                      refine ⟨3520067525131715313535523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9386846733684574169428061 3520067525131715313535523)
                      ·
                        rfl

theorem cell23_6855307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 1, 3].length) (baseStart_6855307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855307 prefixEnd_6855307 := by exact prefixLift 6855307
  have htrace : WordTrace (prefixWord ++ tailWord_6855307) baseStart_6855307 baseEnd_6855307 := by
    simpa [prefixWord, tailWord_6855307, baseEnd_6855307] using wordTrace_append hprefix tailTrace_6855307
  have hstable : (prefixWord ++ tailWord_6855307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855307).length < 2 ^ (prefixWord ++ tailWord_6855307).sum := by decide
  have hdescent : baseEnd_6855307 < baseStart_6855307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855324 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_6855324 : Nat := 118140960795 + 6855324 * 2 ^ 59
def prefixEnd_6855324 : Nat := 4983230072969 + 3 ^ 40 * 6855324 * 2
def baseEnd_6855324 : Nat := 3520076254302841747022945

theorem tailTrace_6855324 : CollatzResearch.WordTrace tailWord_6855324 prefixEnd_6855324 3520076254302841747022945 := by
  unfold tailWord_6855324
  simp only [CollatzResearch.WordTrace]
  refine ⟨125017103708169709486234513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166689471610892945981646017 125017103708169709486234513)
  ·
    refine ⟨93762827781127282114675885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125017103708169709486234513 93762827781127282114675885)
    ·
      refine ⟨35161060417922730793003457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93762827781127282114675885 35161060417922730793003457)
      ·
        refine ⟨26370795313442048094752593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35161060417922730793003457 26370795313442048094752593)
        ·
          refine ⟨19778096485081536071064445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26370795313442048094752593 19778096485081536071064445)
          ·
            refine ⟨7416786181905576026649167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19778096485081536071064445 7416786181905576026649167)
            ·
              refine ⟨11125179272858364039973751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7416786181905576026649167 11125179272858364039973751)
              ·
                refine ⟨16687768909287546059960627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11125179272858364039973751 16687768909287546059960627)
                ·
                  refine ⟨25031653363931319089940941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16687768909287546059960627 25031653363931319089940941)
                  ·
                    refine ⟨9386870011474244658727853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25031653363931319089940941 9386870011474244658727853)
                    ·
                      refine ⟨3520076254302841747022945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9386870011474244658727853 3520076254302841747022945)
                      ·
                        rfl

theorem cell23_6855324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_6855324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855324 prefixEnd_6855324 := by exact prefixLift 6855324
  have htrace : WordTrace (prefixWord ++ tailWord_6855324) baseStart_6855324 baseEnd_6855324 := by
    simpa [prefixWord, tailWord_6855324, baseEnd_6855324] using wordTrace_append hprefix tailTrace_6855324
  have hstable : (prefixWord ++ tailWord_6855324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855324).length < 2 ^ (prefixWord ++ tailWord_6855324).sum := by decide
  have hdescent : baseEnd_6855324 < baseStart_6855324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855457 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_6855457 : Nat := 118140960795 + 6855457 * 2 ^ 59
def prefixEnd_6855457 : Nat := 4983230072969 + 3 ^ 40 * 6855457 * 2
def baseEnd_6855457 : Nat := 3520144547229889726659833

theorem tailTrace_6855457 : CollatzResearch.WordTrace tailWord_6855457 prefixEnd_6855457 3520144547229889726659833 := by
  unfold tailWord_6855457
  simp only [CollatzResearch.WordTrace]
  refine ⟨250039058324857582687060625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166692705549905055124707083 250039058324857582687060625)
  ·
    refine ⟨187529293743643187015295469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250039058324857582687060625 187529293743643187015295469)
    ·
      refine ⟨70323485153866195130735801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187529293743643187015295469 70323485153866195130735801)
      ·
        refine ⟨52742613865399646348051851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70323485153866195130735801 52742613865399646348051851)
        ·
          refine ⟨79113920798099469522077777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52742613865399646348051851 79113920798099469522077777)
          ·
            refine ⟨59335440598574602141558333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79113920798099469522077777 59335440598574602141558333)
            ·
              refine ⟨22250790224465475803084375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59335440598574602141558333 22250790224465475803084375)
              ·
                refine ⟨33376185336698213704626563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22250790224465475803084375 33376185336698213704626563)
                ·
                  refine ⟨50064278005047320556939845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33376185336698213704626563 50064278005047320556939845)
                  ·
                    refine ⟨9387052125946372604426221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50064278005047320556939845 9387052125946372604426221)
                    ·
                      refine ⟨3520144547229889726659833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9387052125946372604426221 3520144547229889726659833)
                      ·
                        rfl

theorem cell23_6855457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_6855457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855457 prefixEnd_6855457 := by exact prefixLift 6855457
  have htrace : WordTrace (prefixWord ++ tailWord_6855457) baseStart_6855457 baseEnd_6855457 := by
    simpa [prefixWord, tailWord_6855457, baseEnd_6855457] using wordTrace_append hprefix tailTrace_6855457
  have hstable : (prefixWord ++ tailWord_6855457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855457).length < 2 ^ (prefixWord ++ tailWord_6855457).sum := by decide
  have hdescent : baseEnd_6855457 < baseStart_6855457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855477 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 8]
def baseStart_6855477 : Nat := 118140960795 + 6855477 * 2 ^ 59
def prefixEnd_6855477 : Nat := 4983230072969 + 3 ^ 40 * 6855477 * 2
def baseEnd_6855477 : Nat := 391128312982553294267749

theorem tailTrace_6855477 : CollatzResearch.WordTrace tailWord_6855477 prefixEnd_6855477 391128312982553294267749 := by
  unfold tailWord_6855477
  simp only [CollatzResearch.WordTrace]
  refine ⟨250039787784785126102788685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166693191856523417401859123 250039787784785126102788685)
  ·
    refine ⟨93764920419294422288545757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250039787784785126102788685 93764920419294422288545757)
    ·
      refine ⟨35161845157235408358204659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93764920419294422288545757 35161845157235408358204659)
      ·
        refine ⟨52742767735853112537306989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35161845157235408358204659 52742767735853112537306989)
        ·
          refine ⟨19778537900944917201490121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52742767735853112537306989 19778537900944917201490121)
          ·
            refine ⟨14833903425708687901117591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19778537900944917201490121 14833903425708687901117591)
            ·
              refine ⟨22250855138563031851676387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14833903425708687901117591 22250855138563031851676387)
              ·
                refine ⟨33376282707844547777514581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22250855138563031851676387 33376282707844547777514581)
                ·
                  refine ⟨391128312982553294267749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33376282707844547777514581 391128312982553294267749)
                  ·
                    rfl

theorem cell23_6855477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_6855477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855477 prefixEnd_6855477 := by exact prefixLift 6855477
  have htrace : WordTrace (prefixWord ++ tailWord_6855477) baseStart_6855477 baseEnd_6855477 := by
    simpa [prefixWord, tailWord_6855477, baseEnd_6855477] using wordTrace_append hprefix tailTrace_6855477
  have hstable : (prefixWord ++ tailWord_6855477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855477).length < 2 ^ (prefixWord ++ tailWord_6855477).sum := by decide
  have hdescent : baseEnd_6855477 < baseStart_6855477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855480 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_6855480 : Nat := 118140960795 + 6855480 * 2 ^ 59
def prefixEnd_6855480 : Nat := 4983230072969 + 3 ^ 40 * 6855480 * 2
def baseEnd_6855480 : Nat := 3520156357284943136672227

theorem tailTrace_6855480 : CollatzResearch.WordTrace tailWord_6855480 prefixEnd_6855480 3520156357284943136672227 := by
  unfold tailWord_6855480
  simp only [CollatzResearch.WordTrace]
  refine ⟨125019948601887128807573947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166693264802516171743431929 125019948601887128807573947)
  ·
    refine ⟨187529922902830693211360921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125019948601887128807573947 187529922902830693211360921)
    ·
      refine ⟨140647442177123019908520691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187529922902830693211360921 140647442177123019908520691)
      ·
        refine ⟨210971163265684529862781037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140647442177123019908520691 210971163265684529862781037)
        ·
          refine ⟨79114186224631698698542889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210971163265684529862781037 79114186224631698698542889)
          ·
            refine ⟨59335639668473774023907167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79114186224631698698542889 59335639668473774023907167)
            ·
              refine ⟨89003459502710661035860751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59335639668473774023907167 89003459502710661035860751)
              ·
                refine ⟨133505189254065991553791127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89003459502710661035860751 133505189254065991553791127)
                ·
                  refine ⟨200257783881098987330686691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133505189254065991553791127 200257783881098987330686691)
                  ·
                    refine ⟨300386675821648480996030037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200257783881098987330686691 300386675821648480996030037)
                    ·
                      refine ⟨3520156357284943136672227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 300386675821648480996030037 3520156357284943136672227)
                      ·
                        rfl

theorem cell23_6855480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_6855480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855480 prefixEnd_6855480 := by exact prefixLift 6855480
  have htrace : WordTrace (prefixWord ++ tailWord_6855480) baseStart_6855480 baseEnd_6855480 := by
    simpa [prefixWord, tailWord_6855480, baseEnd_6855480] using wordTrace_append hprefix tailTrace_6855480
  have hstable : (prefixWord ++ tailWord_6855480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855480).length < 2 ^ (prefixWord ++ tailWord_6855480).sum := by decide
  have hdescent : baseEnd_6855480 < baseStart_6855480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855504 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 3, 1, 3]
def baseStart_6855504 : Nat := 118140960795 + 6855504 * 2 ^ 59
def prefixEnd_6855504 : Nat := 4983230072969 + 3 ^ 40 * 6855504 * 2
def baseEnd_6855504 : Nat := 3520168680820651042772117

theorem tailTrace_6855504 : CollatzResearch.WordTrace tailWord_6855504 prefixEnd_6855504 3520168680820651042772117 := by
  unfold tailWord_6855504
  simp only [CollatzResearch.WordTrace]
  refine ⟨125020386277843654857010783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166693848370458206476014377 125020386277843654857010783)
  ·
    refine ⟨187530579416765482285516175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125020386277843654857010783 187530579416765482285516175)
    ·
      refine ⟨281295869125148223428274263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187530579416765482285516175 281295869125148223428274263)
      ·
        refine ⟨421943803687722335142411395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281295869125148223428274263 421943803687722335142411395)
        ·
          refine ⟨632915705531583502713617093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421943803687722335142411395 632915705531583502713617093)
          ·
            refine ⟨118671694787171906758803205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 632915705531583502713617093 118671694787171906758803205)
            ·
              refine ⟨22250942772594732517275601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118671694787171906758803205 22250942772594732517275601)
              ·
                refine ⟨16688207079446049387956701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22250942772594732517275601 16688207079446049387956701)
                ·
                  refine ⟨6258077654792268520483763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16688207079446049387956701 6258077654792268520483763)
                  ·
                    refine ⟨9387116482188402780725645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6258077654792268520483763 9387116482188402780725645)
                    ·
                      refine ⟨3520168680820651042772117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9387116482188402780725645 3520168680820651042772117)
                      ·
                        rfl

theorem cell23_6855504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3, 1, 3].length) (baseStart_6855504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855504 prefixEnd_6855504 := by exact prefixLift 6855504
  have htrace : WordTrace (prefixWord ++ tailWord_6855504) baseStart_6855504 baseEnd_6855504 := by
    simpa [prefixWord, tailWord_6855504, baseEnd_6855504] using wordTrace_append hprefix tailTrace_6855504
  have hstable : (prefixWord ++ tailWord_6855504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855504).length < 2 ^ (prefixWord ++ tailWord_6855504).sum := by decide
  have hdescent : baseEnd_6855504 < baseStart_6855504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855514 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2]
def baseStart_6855514 : Nat := 118140960795 + 6855514 * 2 ^ 59
def prefixEnd_6855514 : Nat := 4983230072969 + 3 ^ 40 * 6855514 * 2
def baseEnd_6855514 : Nat := 3520173815627196003647071

theorem tailTrace_6855514 : CollatzResearch.WordTrace tailWord_6855514 prefixEnd_6855514 3520173815627196003647071 := by
  unfold tailWord_6855514
  simp only [CollatzResearch.WordTrace]
  refine ⟨62510284321412770355471399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166694091523767387614590397 62510284321412770355471399)
  ·
    refine ⟨93765426482119155533207099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62510284321412770355471399 93765426482119155533207099)
    ·
      refine ⟨140648139723178733299810649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93765426482119155533207099 140648139723178733299810649)
      ·
        refine ⟨105486104792384049974857987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140648139723178733299810649 105486104792384049974857987)
        ·
          refine ⟨158229157188576074962286981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105486104792384049974857987 158229157188576074962286981)
          ·
            refine ⟨29667966972858014055428809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158229157188576074962286981 29667966972858014055428809)
            ·
              refine ⟨22250975229643510541571607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29667966972858014055428809 22250975229643510541571607)
              ·
                refine ⟨33376462844465265812357411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22250975229643510541571607 33376462844465265812357411)
                ·
                  refine ⟨50064694266697898718536117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33376462844465265812357411 50064694266697898718536117)
                  ·
                    refine ⟨4693565087502928004862761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50064694266697898718536117 4693565087502928004862761)
                    ·
                      refine ⟨3520173815627196003647071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4693565087502928004862761 3520173815627196003647071)
                      ·
                        rfl

theorem cell23_6855514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_6855514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855514 prefixEnd_6855514 := by exact prefixLift 6855514
  have htrace : WordTrace (prefixWord ++ tailWord_6855514) baseStart_6855514 baseEnd_6855514 := by
    simpa [prefixWord, tailWord_6855514, baseEnd_6855514] using wordTrace_append hprefix tailTrace_6855514
  have hstable : (prefixWord ++ tailWord_6855514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855514).length < 2 ^ (prefixWord ++ tailWord_6855514).sum := by decide
  have hdescent : baseEnd_6855514 < baseStart_6855514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855521 : List Nat := [1, 2, 3, 1, 1, 1, 2, 7, 1, 1, 3]
def baseStart_6855521 : Nat := 118140960795 + 6855521 * 2 ^ 59
def prefixEnd_6855521 : Nat := 4983230072969 + 3 ^ 40 * 6855521 * 2
def baseEnd_6855521 : Nat := 3520177409991777476259539

theorem tailTrace_6855521 : CollatzResearch.WordTrace tailWord_6855521 prefixEnd_6855521 3520177409991777476259539 := by
  unfold tailWord_6855521
  simp only [CollatzResearch.WordTrace]
  refine ⟨250041392596625721617390417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166694261731083814411593611 250041392596625721617390417)
  ·
    refine ⟨187531044447469291213042813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250041392596625721617390417 187531044447469291213042813)
    ·
      refine ⟨70324141667800984204891055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187531044447469291213042813 70324141667800984204891055)
      ·
        refine ⟨105486212501701476307336583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70324141667800984204891055 105486212501701476307336583)
        ·
          refine ⟨158229318752552214461004875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105486212501701476307336583 158229318752552214461004875)
          ·
            refine ⟨237343978128828321691507313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158229318752552214461004875 237343978128828321691507313)
            ·
              refine ⟨178007983596621241268630485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237343978128828321691507313 178007983596621241268630485)
              ·
                refine ⟨4172062115545810342233527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 178007983596621241268630485 4172062115545810342233527)
                ·
                  refine ⟨6258093173318715513350291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172062115545810342233527 6258093173318715513350291)
                  ·
                    refine ⟨9387139759978073270025437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6258093173318715513350291 9387139759978073270025437)
                    ·
                      refine ⟨3520177409991777476259539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9387139759978073270025437 3520177409991777476259539)
                      ·
                        rfl

theorem cell23_6855521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_6855521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855521 prefixEnd_6855521 := by exact prefixLift 6855521
  have htrace : WordTrace (prefixWord ++ tailWord_6855521) baseStart_6855521 baseEnd_6855521 := by
    simpa [prefixWord, tailWord_6855521, baseEnd_6855521] using wordTrace_append hprefix tailTrace_6855521
  have hstable : (prefixWord ++ tailWord_6855521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855521).length < 2 ^ (prefixWord ++ tailWord_6855521).sum := by decide
  have hdescent : baseEnd_6855521 < baseStart_6855521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855524 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_6855524 : Nat := 118140960795 + 6855524 * 2 ^ 59
def prefixEnd_6855524 : Nat := 4983230072969 + 3 ^ 40 * 6855524 * 2
def baseEnd_6855524 : Nat := 1173392983477913654840675

theorem tailTrace_6855524 : CollatzResearch.WordTrace tailWord_6855524 prefixEnd_6855524 1173392983477913654840675 := by
  unfold tailWord_6855524
  simp only [CollatzResearch.WordTrace]
  refine ⟨125020751007807426564874813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166694334677076568753166417 125020751007807426564874813)
  ·
    refine ⟨46882781627927784961828055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125020751007807426564874813 46882781627927784961828055)
    ·
      refine ⟨70324172441891677442742083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46882781627927784961828055 70324172441891677442742083)
      ·
        refine ⟨105486258662837516164113125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70324172441891677442742083 105486258662837516164113125)
        ·
          refine ⟨19778673499282034280771211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105486258662837516164113125 19778673499282034280771211)
          ·
            refine ⟨29668010248923051421156817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19778673499282034280771211 29668010248923051421156817)
            ·
              refine ⟨22251007686692288565867613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29668010248923051421156817 22251007686692288565867613)
              ·
                refine ⟨8344127882509608212200355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22251007686692288565867613 8344127882509608212200355)
                ·
                  refine ⟨12516191823764412318300533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8344127882509608212200355 12516191823764412318300533)
                  ·
                    refine ⟨1173392983477913654840675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12516191823764412318300533 1173392983477913654840675)
                    ·
                      rfl

theorem cell23_6855524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_6855524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855524 prefixEnd_6855524 := by exact prefixLift 6855524
  have htrace : WordTrace (prefixWord ++ tailWord_6855524) baseStart_6855524 baseEnd_6855524 := by
    simpa [prefixWord, tailWord_6855524, baseEnd_6855524] using wordTrace_append hprefix tailTrace_6855524
  have hstable : (prefixWord ++ tailWord_6855524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855524).length < 2 ^ (prefixWord ++ tailWord_6855524).sum := by decide
  have hdescent : baseEnd_6855524 < baseStart_6855524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855547 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 5]
def baseStart_6855547 : Nat := 118140960795 + 6855547 * 2 ^ 59
def prefixEnd_6855547 : Nat := 4983230072969 + 3 ^ 40 * 6855547 * 2
def baseEnd_6855547 : Nat := 3520190760488794374534419

theorem tailTrace_6855547 : CollatzResearch.WordTrace tailWord_6855547 prefixEnd_6855547 3520190760488794374534419 := by
  unfold tailWord_6855547
  simp only [CollatzResearch.WordTrace]
  refine ⟨250042340894531528057836895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166694893929687685371891263 250042340894531528057836895)
  ·
    refine ⟨375063511341797292086755343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250042340894531528057836895 375063511341797292086755343)
    ·
      refine ⟨562595267012695938130133015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375063511341797292086755343 562595267012695938130133015)
      ·
        refine ⟨843892900519043907195199523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562595267012695938130133015 843892900519043907195199523)
        ·
          refine ⟨1265839350778565860792799285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843892900519043907195199523 1265839350778565860792799285)
          ·
            refine ⟨118672439135490549449324933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1265839350778565860792799285 118672439135490549449324933)
            ·
              refine ⟨22251082337904478021748425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118672439135490549449324933 22251082337904478021748425)
              ·
                refine ⟨16688311753428358516311319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22251082337904478021748425 16688311753428358516311319)
                ·
                  refine ⟨25032467630142537774466979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16688311753428358516311319 25032467630142537774466979)
                  ·
                    refine ⟨37548701445213806661700469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25032467630142537774466979 37548701445213806661700469)
                    ·
                      refine ⟨3520190760488794374534419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37548701445213806661700469 3520190760488794374534419)
                      ·
                        rfl

theorem cell23_6855547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 5].length) (baseStart_6855547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855547 prefixEnd_6855547 := by exact prefixLift 6855547
  have htrace : WordTrace (prefixWord ++ tailWord_6855547) baseStart_6855547 baseEnd_6855547 := by
    simpa [prefixWord, tailWord_6855547, baseEnd_6855547] using wordTrace_append hprefix tailTrace_6855547
  have hstable : (prefixWord ++ tailWord_6855547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855547).length < 2 ^ (prefixWord ++ tailWord_6855547).sum := by decide
  have hdescent : baseEnd_6855547 < baseStart_6855547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855557 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_6855557 : Nat := 118140960795 + 6855557 * 2 ^ 59
def prefixEnd_6855557 : Nat := 4983230072969 + 3 ^ 40 * 6855557 * 2
def baseEnd_6855557 : Nat := 3520195895295339335409373

theorem tailTrace_6855557 : CollatzResearch.WordTrace tailWord_6855557 prefixEnd_6855557 3520195895295339335409373 := by
  unfold tailWord_6855557
  simp only [CollatzResearch.WordTrace]
  refine ⟨250042705624495299765700925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166695137082996866510467283 250042705624495299765700925)
  ·
    refine ⟨93766014609185737412137847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250042705624495299765700925 93766014609185737412137847)
    ·
      refine ⟨140649021913778606118206771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93766014609185737412137847 140649021913778606118206771)
      ·
        refine ⟨210973532870667909177310157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140649021913778606118206771 210973532870667909177310157)
        ·
          refine ⟨79115074826500465941491309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210973532870667909177310157 79115074826500465941491309)
          ·
            refine ⟨29668153059937674728059241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79115074826500465941491309 29668153059937674728059241)
            ·
              refine ⟨22251114794953256046044431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29668153059937674728059241 22251114794953256046044431)
              ·
                refine ⟨33376672192429884069066647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22251114794953256046044431 33376672192429884069066647)
                ·
                  refine ⟨50065008288644826103599971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33376672192429884069066647 50065008288644826103599971)
                  ·
                    refine ⟨75097512432967239155399957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50065008288644826103599971 75097512432967239155399957)
                    ·
                      refine ⟨3520195895295339335409373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75097512432967239155399957 3520195895295339335409373)
                      ·
                        rfl

theorem cell23_6855557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_6855557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855557 prefixEnd_6855557 := by exact prefixLift 6855557
  have htrace : WordTrace (prefixWord ++ tailWord_6855557) baseStart_6855557 baseEnd_6855557 := by
    simpa [prefixWord, tailWord_6855557, baseEnd_6855557] using wordTrace_append hprefix tailTrace_6855557
  have hstable : (prefixWord ++ tailWord_6855557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855557).length < 2 ^ (prefixWord ++ tailWord_6855557).sum := by decide
  have hdescent : baseEnd_6855557 < baseStart_6855557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855561 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 4]
def baseStart_6855561 : Nat := 118140960795 + 6855561 * 2 ^ 59
def prefixEnd_6855561 : Nat := 4983230072969 + 3 ^ 40 * 6855561 * 2
def baseEnd_6855561 : Nat := 3520197949217957319759355

theorem tailTrace_6855561 : CollatzResearch.WordTrace tailWord_6855561 prefixEnd_6855561 3520197949217957319759355 := by
  unfold tailWord_6855561
  simp only [CollatzResearch.WordTrace]
  refine ⟨250042851516480808448846537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166695234344320538965897691 250042851516480808448846537)
  ·
    refine ⟨187532138637360606336634903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250042851516480808448846537 187532138637360606336634903)
    ·
      refine ⟨281298207956040909504952355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187532138637360606336634903 281298207956040909504952355)
      ·
        refine ⟨421947311934061364257428533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281298207956040909504952355 421947311934061364257428533)
        ·
          refine ⟨39557560493818252899133925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 421947311934061364257428533 39557560493818252899133925)
          ·
            refine ⟨7417042592590922418587611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39557560493818252899133925 7417042592590922418587611)
            ·
              refine ⟨11125563888886383627881417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417042592590922418587611 11125563888886383627881417)
              ·
                refine ⟨8344172916664787720911063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11125563888886383627881417 8344172916664787720911063)
                ·
                  refine ⟨12516259374997181581366595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8344172916664787720911063 12516259374997181581366595)
                  ·
                    refine ⟨18774389062495772372049893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12516259374997181581366595 18774389062495772372049893)
                    ·
                      refine ⟨3520197949217957319759355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18774389062495772372049893 3520197949217957319759355)
                      ·
                        rfl

theorem cell23_6855561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 4].length) (baseStart_6855561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855561 prefixEnd_6855561 := by exact prefixLift 6855561
  have htrace : WordTrace (prefixWord ++ tailWord_6855561) baseStart_6855561 baseEnd_6855561 := by
    simpa [prefixWord, tailWord_6855561, baseEnd_6855561] using wordTrace_append hprefix tailTrace_6855561
  have hstable : (prefixWord ++ tailWord_6855561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855561).length < 2 ^ (prefixWord ++ tailWord_6855561).sum := by decide
  have hdescent : baseEnd_6855561 < baseStart_6855561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855578 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4]
def baseStart_6855578 : Nat := 118140960795 + 6855578 * 2 ^ 59
def prefixEnd_6855578 : Nat := 4983230072969 + 3 ^ 40 * 6855578 * 2
def baseEnd_6855578 : Nat := 3520206678389083753246777

theorem tailTrace_6855578 : CollatzResearch.WordTrace tailWord_6855578 prefixEnd_6855578 3520206678389083753246777 := by
  unfold tailWord_6855578
  simp only [CollatzResearch.WordTrace]
  refine ⟨62510867889354805088053847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166695647704946146901476925 62510867889354805088053847)
  ·
    refine ⟨93766301834032207632080771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62510867889354805088053847 93766301834032207632080771)
    ·
      refine ⟨140649452751048311448121157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93766301834032207632080771 140649452751048311448121157)
      ·
        refine ⟨26371772390821558396522717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140649452751048311448121157 26371772390821558396522717)
        ·
          refine ⟨9889414646558084398696019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26371772390821558396522717 9889414646558084398696019)
          ·
            refine ⟨14834121969837126598044029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9889414646558084398696019 14834121969837126598044029)
            ·
              refine ⟨5562795738688922474266511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14834121969837126598044029 5562795738688922474266511)
              ·
                refine ⟨8344193608033383711399767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562795738688922474266511 8344193608033383711399767)
                ·
                  refine ⟨12516290412050075567099651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8344193608033383711399767 12516290412050075567099651)
                  ·
                    refine ⟨18774435618075113350649477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12516290412050075567099651 18774435618075113350649477)
                    ·
                      refine ⟨3520206678389083753246777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18774435618075113350649477 3520206678389083753246777)
                      ·
                        rfl

theorem cell23_6855578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_6855578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855578 prefixEnd_6855578 := by exact prefixLift 6855578
  have htrace : WordTrace (prefixWord ++ tailWord_6855578) baseStart_6855578 baseEnd_6855578 := by
    simpa [prefixWord, tailWord_6855578, baseEnd_6855578] using wordTrace_append hprefix tailTrace_6855578
  have hstable : (prefixWord ++ tailWord_6855578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855578).length < 2 ^ (prefixWord ++ tailWord_6855578).sum := by decide
  have hdescent : baseEnd_6855578 < baseStart_6855578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855601 : List Nat := [1, 2, 2, 4, 4, 1, 1, 8]
def baseStart_6855601 : Nat := 118140960795 + 6855601 * 2 ^ 59
def prefixEnd_6855601 : Nat := 4983230072969 + 3 ^ 40 * 6855601 * 2
def baseEnd_6855601 : Nat := 130378462534968043083673

theorem tailTrace_6855601 : CollatzResearch.WordTrace tailWord_6855601 prefixEnd_6855601 130378462534968043083673 := by
  unfold tailWord_6855601
  simp only [CollatzResearch.WordTrace]
  refine ⟨250044310436335895280302657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166696206957557263520201771 250044310436335895280302657)
  ·
    refine ⟨187533232827251921460226993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250044310436335895280302657 187533232827251921460226993)
    ·
      refine ⟨140649924620438941095170245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187533232827251921460226993 140649924620438941095170245)
      ·
        refine ⟨26371860866332301455344421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140649924620438941095170245 26371860866332301455344421)
        ·
          refine ⟨4944723912437306522877079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26371860866332301455344421 4944723912437306522877079)
          ·
            refine ⟨7417085868655959784315619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4944723912437306522877079 7417085868655959784315619)
            ·
              refine ⟨11125628802983939676473429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417085868655959784315619 11125628802983939676473429)
              ·
                refine ⟨130378462534968043083673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11125628802983939676473429 130378462534968043083673)
                ·
                  rfl

theorem cell23_6855601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 8].length) (baseStart_6855601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855601 prefixEnd_6855601 := by exact prefixLift 6855601
  have htrace : WordTrace (prefixWord ++ tailWord_6855601) baseStart_6855601 baseEnd_6855601 := by
    simpa [prefixWord, tailWord_6855601, baseEnd_6855601] using wordTrace_append hprefix tailTrace_6855601
  have hstable : (prefixWord ++ tailWord_6855601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855601).length < 2 ^ (prefixWord ++ tailWord_6855601).sum := by decide
  have hdescent : baseEnd_6855601 < baseStart_6855601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855629 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6855629 : Nat := 118140960795 + 6855629 * 2 ^ 59
def prefixEnd_6855629 : Nat := 4983230072969 + 3 ^ 40 * 6855629 * 2
def baseEnd_6855629 : Nat := 3520232865902463053709043

theorem tailTrace_6855629 : CollatzResearch.WordTrace tailWord_6855629 prefixEnd_6855629 3520232865902463053709043 := by
  unfold tailWord_6855629
  simp only [CollatzResearch.WordTrace]
  refine ⟨250045331680234456062321941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166696887786822970708214627 250045331680234456062321941)
  ·
    refine ⟨11720874922510990127921341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 250045331680234456062321941 11720874922510990127921341)
    ·
      refine ⟨4395328095941621297970503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11720874922510990127921341 4395328095941621297970503)
      ·
        refine ⟨6592992143912431946955755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4395328095941621297970503 6592992143912431946955755)
        ·
          refine ⟨9889488215868647920433633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6592992143912431946955755 9889488215868647920433633)
          ·
            refine ⟨7417116161901485940325225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9889488215868647920433633 7417116161901485940325225)
            ·
              refine ⟨5562837121426114455243919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7417116161901485940325225 5562837121426114455243919)
              ·
                refine ⟨8344255682139171682865879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562837121426114455243919 8344255682139171682865879)
                ·
                  refine ⟨12516383523208757524298819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8344255682139171682865879 12516383523208757524298819)
                  ·
                    refine ⟨18774575284813136286448229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12516383523208757524298819 18774575284813136286448229)
                    ·
                      refine ⟨3520232865902463053709043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18774575284813136286448229 3520232865902463053709043)
                      ·
                        rfl

theorem cell23_6855629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6855629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855629 prefixEnd_6855629 := by exact prefixLift 6855629
  have htrace : WordTrace (prefixWord ++ tailWord_6855629) baseStart_6855629 baseEnd_6855629 := by
    simpa [prefixWord, tailWord_6855629, baseEnd_6855629] using wordTrace_append hprefix tailTrace_6855629
  have hstable : (prefixWord ++ tailWord_6855629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855629).length < 2 ^ (prefixWord ++ tailWord_6855629).sum := by decide
  have hdescent : baseEnd_6855629 < baseStart_6855629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855645 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_6855645 : Nat := 118140960795 + 6855645 * 2 ^ 59
def prefixEnd_6855645 : Nat := 4983230072969 + 3 ^ 40 * 6855645 * 2
def baseEnd_6855645 : Nat := 3520241081592934991108969

theorem tailTrace_6855645 : CollatzResearch.WordTrace tailWord_6855645 prefixEnd_6855645 3520241081592934991108969 := by
  unfold tailWord_6855645
  simp only [CollatzResearch.WordTrace]
  refine ⟨250045915248176490794904389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166697276832117660529936259 250045915248176490794904389)
  ·
    refine ⟨46883609109033092024044573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250045915248176490794904389 46883609109033092024044573)
    ·
      refine ⟨17581353415887409509016715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46883609109033092024044573 17581353415887409509016715)
      ·
        refine ⟨26372030123831114263525073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17581353415887409509016715 26372030123831114263525073)
        ·
          refine ⟨19779022592873335697643805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26372030123831114263525073 19779022592873335697643805)
          ·
            refine ⟨7417133472327500886616427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19779022592873335697643805 7417133472327500886616427)
            ·
              refine ⟨11125700208491251329924641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417133472327500886616427 11125700208491251329924641)
              ·
                refine ⟨8344275156368438497443481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11125700208491251329924641 8344275156368438497443481)
                ·
                  refine ⟨6258206367276328873082611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8344275156368438497443481 6258206367276328873082611)
                  ·
                    refine ⟨9387309550914493309623917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6258206367276328873082611 9387309550914493309623917)
                    ·
                      refine ⟨3520241081592934991108969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9387309550914493309623917 3520241081592934991108969)
                      ·
                        rfl

theorem cell23_6855645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_6855645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855645 prefixEnd_6855645 := by exact prefixLift 6855645
  have htrace : WordTrace (prefixWord ++ tailWord_6855645) baseStart_6855645 baseEnd_6855645 := by
    simpa [prefixWord, tailWord_6855645, baseEnd_6855645] using wordTrace_append hprefix tailTrace_6855645
  have hstable : (prefixWord ++ tailWord_6855645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855645).length < 2 ^ (prefixWord ++ tailWord_6855645).sum := by decide
  have hdescent : baseEnd_6855645 < baseStart_6855645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855691 : List Nat := [1, 1, 1, 1, 6, 2, 3, 3, 5]
def baseStart_6855691 : Nat := 118140960795 + 6855691 * 2 ^ 59
def prefixEnd_6855691 : Nat := 4983230072969 + 3 ^ 40 * 6855691 * 2
def baseEnd_6855691 : Nat := 391140522411449090125973

theorem tailTrace_6855691 : CollatzResearch.WordTrace tailWord_6855691 prefixEnd_6855691 391140522411449090125973 := by
  unfold tailWord_6855691
  simp only [CollatzResearch.WordTrace]
  refine ⟨250047593006009840651078927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166698395337339893767385951 250047593006009840651078927)
  ·
    refine ⟨375071389509014760976618391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250047593006009840651078927 375071389509014760976618391)
    ·
      refine ⟨562607084263522141464927587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375071389509014760976618391 562607084263522141464927587)
      ·
        refine ⟨843910626395283212197391381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562607084263522141464927587 843910626395283212197391381)
        ·
          refine ⟨39558310612278900571752721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 843910626395283212197391381 39558310612278900571752721)
          ·
            refine ⟨29668732959209175428814541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39558310612278900571752721 29668732959209175428814541)
            ·
              refine ⟨11125774859703440785805453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29668732959209175428814541 11125774859703440785805453)
              ·
                refine ⟨4172165572388790294677045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11125774859703440785805453 4172165572388790294677045)
                ·
                  refine ⟨391140522411449090125973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4172165572388790294677045 391140522411449090125973)
                  ·
                    rfl

theorem cell23_6855691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 5].length) (baseStart_6855691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855691 prefixEnd_6855691 := by exact prefixLift 6855691
  have htrace : WordTrace (prefixWord ++ tailWord_6855691) baseStart_6855691 baseEnd_6855691 := by
    simpa [prefixWord, tailWord_6855691, baseEnd_6855691] using wordTrace_append hprefix tailTrace_6855691
  have hstable : (prefixWord ++ tailWord_6855691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855691).length < 2 ^ (prefixWord ++ tailWord_6855691).sum := by decide
  have hdescent : baseEnd_6855691 < baseStart_6855691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855697 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_6855697 : Nat := 118140960795 + 6855697 * 2 ^ 59
def prefixEnd_6855697 : Nat := 4983230072969 + 3 ^ 40 * 6855697 * 2
def baseEnd_6855697 : Nat := 3520267782586968787658729

theorem tailTrace_6855697 : CollatzResearch.WordTrace tailWord_6855697 prefixEnd_6855697 3520267782586968787658729 := by
  unfold tailWord_6855697
  simp only [CollatzResearch.WordTrace]
  refine ⟨250047811843988103675797345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166698541229325402450531563 250047811843988103675797345)
  ·
    refine ⟨187535858882991077756848009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250047811843988103675797345 187535858882991077756848009)
    ·
      refine ⟨140651894162243308317636007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187535858882991077756848009 140651894162243308317636007)
      ·
        refine ⟨210977841243364962476454011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140651894162243308317636007 210977841243364962476454011)
        ·
          refine ⟨316466761865047443714681017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210977841243364962476454011 316466761865047443714681017)
          ·
            refine ⟨237350071398785582786010763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316466761865047443714681017 237350071398785582786010763)
            ·
              refine ⟨356025107098178374179016145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237350071398785582786010763 356025107098178374179016145)
              ·
                refine ⟨267018830323633780634262109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356025107098178374179016145 267018830323633780634262109)
                ·
                  refine ⟨100132061371362667737848291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267018830323633780634262109 100132061371362667737848291)
                  ·
                    refine ⟨150198092057044001606772437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100132061371362667737848291 150198092057044001606772437)
                    ·
                      refine ⟨3520267782586968787658729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150198092057044001606772437 3520267782586968787658729)
                      ·
                        rfl

theorem cell23_6855697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_6855697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855697 prefixEnd_6855697 := by exact prefixLift 6855697
  have htrace : WordTrace (prefixWord ++ tailWord_6855697) baseStart_6855697 baseEnd_6855697 := by
    simpa [prefixWord, tailWord_6855697, baseEnd_6855697] using wordTrace_append hprefix tailTrace_6855697
  have hstable : (prefixWord ++ tailWord_6855697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855697).length < 2 ^ (prefixWord ++ tailWord_6855697).sum := by decide
  have hdescent : baseEnd_6855697 < baseStart_6855697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855704 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 4, 5]
def baseStart_6855704 : Nat := 118140960795 + 6855704 * 2 ^ 59
def prefixEnd_6855704 : Nat := 4983230072969 + 3 ^ 40 * 6855704 * 2
def baseEnd_6855704 : Nat := 1173423792317183420090399

theorem tailTrace_6855704 : CollatzResearch.WordTrace tailWord_6855704 prefixEnd_6855704 1173423792317183420090399 := by
  unfold tailWord_6855704
  simp only [CollatzResearch.WordTrace]
  refine ⟨125024033577481371935651083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166698711436641829247534777 125024033577481371935651083)
  ·
    refine ⟨187536050366222057903476625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125024033577481371935651083 187536050366222057903476625)
    ·
      refine ⟨140652037774666543427607469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187536050366222057903476625 140652037774666543427607469)
      ·
        refine ⟨52744514165499953785352801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140652037774666543427607469 52744514165499953785352801)
        ·
          refine ⟨39558385624124965339014601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52744514165499953785352801 39558385624124965339014601)
          ·
            refine ⟨29668789218093724004260951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39558385624124965339014601 29668789218093724004260951)
            ·
              refine ⟨44503183827140586006391427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29668789218093724004260951 44503183827140586006391427)
              ·
                refine ⟨66754775740710879009587141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44503183827140586006391427 66754775740710879009587141)
                ·
                  refine ⟨12516520451383289814297589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66754775740710879009587141 12516520451383289814297589)
                  ·
                    refine ⟨1173423792317183420090399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12516520451383289814297589 1173423792317183420090399)
                    ·
                      rfl

theorem cell23_6855704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_6855704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855704 prefixEnd_6855704 := by exact prefixLift 6855704
  have htrace : WordTrace (prefixWord ++ tailWord_6855704) baseStart_6855704 baseEnd_6855704 := by
    simpa [prefixWord, tailWord_6855704, baseEnd_6855704] using wordTrace_append hprefix tailTrace_6855704
  have hstable : (prefixWord ++ tailWord_6855704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855704).length < 2 ^ (prefixWord ++ tailWord_6855704).sum := by decide
  have hdescent : baseEnd_6855704 < baseStart_6855704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855708 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 7]
def baseStart_6855708 : Nat := 118140960795 + 6855708 * 2 ^ 59
def prefixEnd_6855708 : Nat := 4983230072969 + 3 ^ 40 * 6855708 * 2
def baseEnd_6855708 : Nat := 391141492319352027180131

theorem tailTrace_6855708 : CollatzResearch.WordTrace tailWord_6855708 prefixEnd_6855708 391141492319352027180131 := by
  unfold tailWord_6855708
  simp only [CollatzResearch.WordTrace]
  refine ⟨125024106523474126277223889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166698808697965501702965185 125024106523474126277223889)
  ·
    refine ⟨93768079892605594707917917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125024106523474126277223889 93768079892605594707917917)
    ·
      refine ⟨35163029959727098015469219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93768079892605594707917917 35163029959727098015469219)
      ·
        refine ⟨52744544939590647023203829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35163029959727098015469219 52744544939590647023203829)
        ·
          refine ⟨4944801088086623158425359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52744544939590647023203829 4944801088086623158425359)
          ·
            refine ⟨7417201632129934737638039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4944801088086623158425359 7417201632129934737638039)
            ·
              refine ⟨11125802448194902106457059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417201632129934737638039 11125802448194902106457059)
              ·
                refine ⟨16688703672292353159685589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11125802448194902106457059 16688703672292353159685589)
                ·
                  refine ⟨391141492319352027180131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16688703672292353159685589 391141492319352027180131)
                  ·
                    rfl

theorem cell23_6855708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_6855708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855708 prefixEnd_6855708 := by exact prefixLift 6855708
  have htrace : WordTrace (prefixWord ++ tailWord_6855708) baseStart_6855708 baseEnd_6855708 := by
    simpa [prefixWord, tailWord_6855708, baseEnd_6855708] using wordTrace_append hprefix tailTrace_6855708
  have hstable : (prefixWord ++ tailWord_6855708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855708).length < 2 ^ (prefixWord ++ tailWord_6855708).sum := by decide
  have hdescent : baseEnd_6855708 < baseStart_6855708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855714 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_6855714 : Nat := 118140960795 + 6855714 * 2 ^ 59
def prefixEnd_6855714 : Nat := 4983230072969 + 3 ^ 40 * 6855714 * 2
def baseEnd_6855714 : Nat := 3520276511758095221146151

theorem tailTrace_6855714 : CollatzResearch.WordTrace tailWord_6855714 prefixEnd_6855714 3520276511758095221146151 := by
  unfold tailWord_6855714
  simp only [CollatzResearch.WordTrace]
  refine ⟨62512107971231628894791549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166698954589951010386110797 62512107971231628894791549)
  ·
    refine ⟨23442040489211860835546831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62512107971231628894791549 23442040489211860835546831)
    ·
      refine ⟨35163060733817791253320247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23442040489211860835546831 35163060733817791253320247)
      ·
        refine ⟨52744591100726686879980371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35163060733817791253320247 52744591100726686879980371)
        ·
          refine ⟨79116886651090030319970557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52744591100726686879980371 79116886651090030319970557)
          ·
            refine ⟨29668832494158761369988959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79116886651090030319970557 29668832494158761369988959)
            ·
              refine ⟨44503248741238142054983439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29668832494158761369988959 44503248741238142054983439)
              ·
                refine ⟨66754873111857213082475159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44503248741238142054983439 66754873111857213082475159)
                ·
                  refine ⟨100132309667785819623712739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66754873111857213082475159 100132309667785819623712739)
                  ·
                    refine ⟨150198464501678729435569109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100132309667785819623712739 150198464501678729435569109)
                    ·
                      refine ⟨3520276511758095221146151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150198464501678729435569109 3520276511758095221146151)
                      ·
                        rfl

theorem cell23_6855714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_6855714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855714 prefixEnd_6855714 := by exact prefixLift 6855714
  have htrace : WordTrace (prefixWord ++ tailWord_6855714) baseStart_6855714 baseEnd_6855714 := by
    simpa [prefixWord, tailWord_6855714, baseEnd_6855714] using wordTrace_append hprefix tailTrace_6855714
  have hstable : (prefixWord ++ tailWord_6855714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855714).length < 2 ^ (prefixWord ++ tailWord_6855714).sum := by decide
  have hdescent : baseEnd_6855714 < baseStart_6855714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855719 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_6855719 : Nat := 118140960795 + 6855719 * 2 ^ 59
def prefixEnd_6855719 : Nat := 4983230072969 + 3 ^ 40 * 6855719 * 2
def baseEnd_6855719 : Nat := 3520279079161367701583629

theorem tailTrace_6855719 : CollatzResearch.WordTrace tailWord_6855719 prefixEnd_6855719 3520279079161367701583629 := by
  unfold tailWord_6855719
  simp only [CollatzResearch.WordTrace]
  refine ⟨250048614249908401433098211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166699076166605600955398807 250048614249908401433098211)
  ·
    refine ⟨375072921374862602149647317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250048614249908401433098211 375072921374862602149647317)
    ·
      refine ⟨8790771594723342237882359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 375072921374862602149647317 8790771594723342237882359)
      ·
        refine ⟨13186157392085013356823539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8790771594723342237882359 13186157392085013356823539)
        ·
          refine ⟨19779236088127520035235309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13186157392085013356823539 19779236088127520035235309)
          ·
            refine ⟨7417213533047820013213241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19779236088127520035235309 7417213533047820013213241)
            ·
              refine ⟨5562910149785865009909931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7417213533047820013213241 5562910149785865009909931)
              ·
                refine ⟨8344365224678797514864897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562910149785865009909931 8344365224678797514864897)
                ·
                  refine ⟨6258273918509098136148673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8344365224678797514864897 6258273918509098136148673)
                  ·
                    refine ⟨4693705438881823602111505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6258273918509098136148673 4693705438881823602111505)
                    ·
                      refine ⟨3520279079161367701583629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4693705438881823602111505 3520279079161367701583629)
                      ·
                        rfl

theorem cell23_6855719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_6855719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855719 prefixEnd_6855719 := by exact prefixLift 6855719
  have htrace : WordTrace (prefixWord ++ tailWord_6855719) baseStart_6855719 baseEnd_6855719 := by
    simpa [prefixWord, tailWord_6855719, baseEnd_6855719] using wordTrace_append hprefix tailTrace_6855719
  have hstable : (prefixWord ++ tailWord_6855719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855719).length < 2 ^ (prefixWord ++ tailWord_6855719).sum := by decide
  have hdescent : baseEnd_6855719 < baseStart_6855719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855724 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_6855724 : Nat := 118140960795 + 6855724 * 2 ^ 59
def prefixEnd_6855724 : Nat := 4983230072969 + 3 ^ 40 * 6855724 * 2
def baseEnd_6855724 : Nat := 3520281646564640182021105

theorem tailTrace_6855724 : CollatzResearch.WordTrace tailWord_6855724 prefixEnd_6855724 3520281646564640182021105 := by
  unfold tailWord_6855724
  simp only [CollatzResearch.WordTrace]
  refine ⟨125024398307445143643515113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166699197743260191524686817 125024398307445143643515113)
  ·
    refine ⟨93768298730583857732636335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125024398307445143643515113 93768298730583857732636335)
    ·
      refine ⟨140652448095875786598954503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93768298730583857732636335 140652448095875786598954503)
      ·
        refine ⟨210978672143813679898431755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140652448095875786598954503 210978672143813679898431755)
        ·
          refine ⟨316468008215720519847647633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210978672143813679898431755 316468008215720519847647633)
          ·
            refine ⟨237351006161790389885735725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316468008215720519847647633 237351006161790389885735725)
            ·
              refine ⟨89006627310671396207150897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237351006161790389885735725 89006627310671396207150897)
              ·
                refine ⟨66754970483003547155363173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89006627310671396207150897 66754970483003547155363173)
                ·
                  refine ⟨12516556965563165091630595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66754970483003547155363173 12516556965563165091630595)
                  ·
                    refine ⟨18774835448344747637445893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12516556965563165091630595 18774835448344747637445893)
                    ·
                      refine ⟨3520281646564640182021105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18774835448344747637445893 3520281646564640182021105)
                      ·
                        rfl

theorem cell23_6855724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_6855724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855724 prefixEnd_6855724 := by exact prefixLift 6855724
  have htrace : WordTrace (prefixWord ++ tailWord_6855724) baseStart_6855724 baseEnd_6855724 := by
    simpa [prefixWord, tailWord_6855724, baseEnd_6855724] using wordTrace_append hprefix tailTrace_6855724
  have hstable : (prefixWord ++ tailWord_6855724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855724).length < 2 ^ (prefixWord ++ tailWord_6855724).sum := by decide
  have hdescent : baseEnd_6855724 < baseStart_6855724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855727 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_6855727 : Nat := 118140960795 + 6855727 * 2 ^ 59
def prefixEnd_6855727 : Nat := 4983230072969 + 3 ^ 40 * 6855727 * 2
def baseEnd_6855727 : Nat := 3520283187006603670283591

theorem tailTrace_6855727 : CollatzResearch.WordTrace tailWord_6855727 prefixEnd_6855727 3520283187006603670283591 := by
  unfold tailWord_6855727
  simp only [CollatzResearch.WordTrace]
  refine ⟨250048906033879418799389435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166699270689252945866259623 250048906033879418799389435)
  ·
    refine ⟨375073359050819128199084153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250048906033879418799389435 375073359050819128199084153)
    ·
      refine ⟨281305019288114346149313115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375073359050819128199084153 281305019288114346149313115)
      ·
        refine ⟨421957528932171519223969673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281305019288114346149313115 421957528932171519223969673)
        ·
          refine ⟨316468146699128639417977255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421957528932171519223969673 316468146699128639417977255)
          ·
            refine ⟨474702220048692959126965883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316468146699128639417977255 474702220048692959126965883)
            ·
              refine ⟨712053330073039438690448825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474702220048692959126965883 712053330073039438690448825)
              ·
                refine ⟨534039997554779579017836619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712053330073039438690448825 534039997554779579017836619)
                ·
                  refine ⟨801059996332169368526754929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534039997554779579017836619 801059996332169368526754929)
                  ·
                    refine ⟨600794997249127026395066197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 801059996332169368526754929 600794997249127026395066197)
                    ·
                      refine ⟨3520283187006603670283591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 600794997249127026395066197 3520283187006603670283591)
                      ·
                        rfl

theorem cell23_6855727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_6855727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855727 prefixEnd_6855727 := by exact prefixLift 6855727
  have htrace : WordTrace (prefixWord ++ tailWord_6855727) baseStart_6855727 baseEnd_6855727 := by
    simpa [prefixWord, tailWord_6855727, baseEnd_6855727] using wordTrace_append hprefix tailTrace_6855727
  have hstable : (prefixWord ++ tailWord_6855727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855727).length < 2 ^ (prefixWord ++ tailWord_6855727).sum := by decide
  have hdescent : baseEnd_6855727 < baseStart_6855727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855741 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6855741 : Nat := 118140960795 + 6855741 * 2 ^ 59
def prefixEnd_6855741 : Nat := 4983230072969 + 3 ^ 40 * 6855741 * 2
def baseEnd_6855741 : Nat := 3520290375735766615508527

theorem tailTrace_6855741 : CollatzResearch.WordTrace tailWord_6855741 prefixEnd_6855741 3520290375735766615508527 := by
  unfold tailWord_6855741
  simp only [CollatzResearch.WordTrace]
  refine ⟨250049416655828699190399077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166699611103885799460266051 250049416655828699190399077)
  ·
    refine ⟨46884265622967881098199827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250049416655828699190399077 46884265622967881098199827)
    ·
      refine ⟨70326398434451821647299741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46884265622967881098199827 70326398434451821647299741)
      ·
        refine ⟨26372399412919433117737403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70326398434451821647299741 26372399412919433117737403)
        ·
          refine ⟨39558599119379149676606105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26372399412919433117737403 39558599119379149676606105)
          ·
            refine ⟨29668949339534362257454579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39558599119379149676606105 29668949339534362257454579)
            ·
              refine ⟨44503424009301543386181869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29668949339534362257454579 44503424009301543386181869)
              ·
                refine ⟨16688784003488078769818201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44503424009301543386181869 16688784003488078769818201)
                ·
                  refine ⟨12516588002616059077363651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16688784003488078769818201 12516588002616059077363651)
                  ·
                    refine ⟨18774882003924088616045477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12516588002616059077363651 18774882003924088616045477)
                    ·
                      refine ⟨3520290375735766615508527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18774882003924088616045477 3520290375735766615508527)
                      ·
                        rfl

theorem cell23_6855741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6855741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855741 prefixEnd_6855741 := by exact prefixLift 6855741
  have htrace : WordTrace (prefixWord ++ tailWord_6855741) baseStart_6855741 baseEnd_6855741 := by
    simpa [prefixWord, tailWord_6855741, baseEnd_6855741] using wordTrace_append hprefix tailTrace_6855741
  have hstable : (prefixWord ++ tailWord_6855741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855741).length < 2 ^ (prefixWord ++ tailWord_6855741).sum := by decide
  have hdescent : baseEnd_6855741 < baseStart_6855741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855761 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 2, 2, 3]
def baseStart_6855761 : Nat := 118140960795 + 6855761 * 2 ^ 59
def prefixEnd_6855761 : Nat := 4983230072969 + 3 ^ 40 * 6855761 * 2
def baseEnd_6855761 : Nat := 3520300645348856537258435

theorem tailTrace_6855761 : CollatzResearch.WordTrace tailWord_6855761 prefixEnd_6855761 3520300645348856537258435 := by
  unfold tailWord_6855761
  simp only [CollatzResearch.WordTrace]
  refine ⟨250050146115756242606127137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166700097410504161737418091 250050146115756242606127137)
  ·
    refine ⟨187537609586817181954595353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250050146115756242606127137 187537609586817181954595353)
    ·
      refine ⟨140653207190112886465946515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187537609586817181954595353 140653207190112886465946515)
      ·
        refine ⟨210979810785169329698919773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140653207190112886465946515 210979810785169329698919773)
        ·
          refine ⟨79117429044438498637094915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210979810785169329698919773 79117429044438498637094915)
          ·
            refine ⟨118676143566657747955642373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79117429044438498637094915 118676143566657747955642373)
            ·
              refine ⟨22251776918748327741682945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118676143566657747955642373 22251776918748327741682945)
              ·
                refine ⟨16688832689061245806262209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22251776918748327741682945 16688832689061245806262209)
                ·
                  refine ⟨12516624516795934354696657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16688832689061245806262209 12516624516795934354696657)
                  ·
                    refine ⟨9387468387596950766022493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12516624516795934354696657 9387468387596950766022493)
                    ·
                      refine ⟨3520300645348856537258435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9387468387596950766022493 3520300645348856537258435)
                      ·
                        rfl

theorem cell23_6855761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_6855761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855761 prefixEnd_6855761 := by exact prefixLift 6855761
  have htrace : WordTrace (prefixWord ++ tailWord_6855761) baseStart_6855761 baseEnd_6855761 := by
    simpa [prefixWord, tailWord_6855761, baseEnd_6855761] using wordTrace_append hprefix tailTrace_6855761
  have hstable : (prefixWord ++ tailWord_6855761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855761).length < 2 ^ (prefixWord ++ tailWord_6855761).sum := by decide
  have hdescent : baseEnd_6855761 < baseStart_6855761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855764 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 8]
def baseStart_6855764 : Nat := 118140960795 + 6855764 * 2 ^ 59
def prefixEnd_6855764 : Nat := 4983230072969 + 3 ^ 40 * 6855764 * 2
def baseEnd_6855764 : Nat := 391144687310091113946769

theorem tailTrace_6855764 : CollatzResearch.WordTrace tailWord_6855764 prefixEnd_6855764 391144687310091113946769 := by
  unfold tailWord_6855764
  simp only [CollatzResearch.WordTrace]
  refine ⟨125025127767372687059243173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166700170356496916078990897 125025127767372687059243173)
  ·
    refine ⟨23442211456382378823608095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125025127767372687059243173 23442211456382378823608095)
    ·
      refine ⟨35163317184573568235412143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23442211456382378823608095 35163317184573568235412143)
      ·
        refine ⟨52744975776860352353118215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35163317184573568235412143 52744975776860352353118215)
        ·
          refine ⟨79117463665290528529677323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52744975776860352353118215 79117463665290528529677323)
          ·
            refine ⟨118676195497935792794515985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79117463665290528529677323 118676195497935792794515985)
            ·
              refine ⟨89007146623451844595886989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118676195497935792794515985 89007146623451844595886989)
              ·
                refine ⟨33377679983794441723457621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89007146623451844595886989 33377679983794441723457621)
                ·
                  refine ⟨391144687310091113946769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33377679983794441723457621 391144687310091113946769)
                  ·
                    rfl

theorem cell23_6855764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_6855764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855764 prefixEnd_6855764 := by exact prefixLift 6855764
  have htrace : WordTrace (prefixWord ++ tailWord_6855764) baseStart_6855764 baseEnd_6855764 := by
    simpa [prefixWord, tailWord_6855764, baseEnd_6855764] using wordTrace_append hprefix tailTrace_6855764
  have hstable : (prefixWord ++ tailWord_6855764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855764).length < 2 ^ (prefixWord ++ tailWord_6855764).sum := by decide
  have hdescent : baseEnd_6855764 < baseStart_6855764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855768 : List Nat := [2, 1, 2, 2, 1, 3, 3, 4, 1, 4]
def baseStart_6855768 : Nat := 118140960795 + 6855768 * 2 ^ 59
def prefixEnd_6855768 : Nat := 4983230072969 + 3 ^ 40 * 6855768 * 2
def baseEnd_6855768 : Nat := 1173434746571146003290301

theorem tailTrace_6855768 : CollatzResearch.WordTrace tailWord_6855768 prefixEnd_6855768 1173434746571146003290301 := by
  unfold tailWord_6855768
  simp only [CollatzResearch.WordTrace]
  refine ⟨125025200713365441400815979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166700267617820588534421305 125025200713365441400815979)
  ·
    refine ⟨187537801070048162101223969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125025200713365441400815979 187537801070048162101223969)
    ·
      refine ⟨140653350802536121575917977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187537801070048162101223969 140653350802536121575917977)
      ·
        refine ⟨105490013101902091181938483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140653350802536121575917977 105490013101902091181938483)
        ·
          refine ⟨158235019652853136772907725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105490013101902091181938483 158235019652853136772907725)
          ·
            refine ⟨59338132369819926289840397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158235019652853136772907725 59338132369819926289840397)
            ·
              refine ⟨22251799638682472358690149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59338132369819926289840397 22251799638682472358690149)
              ·
                refine ⟨4172212432252963567254403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22251799638682472358690149 4172212432252963567254403)
                ·
                  refine ⟨6258318648379445350881605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172212432252963567254403 6258318648379445350881605)
                  ·
                    refine ⟨1173434746571146003290301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6258318648379445350881605 1173434746571146003290301)
                    ·
                      rfl

theorem cell23_6855768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_6855768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855768 prefixEnd_6855768 := by exact prefixLift 6855768
  have htrace : WordTrace (prefixWord ++ tailWord_6855768) baseStart_6855768 baseEnd_6855768 := by
    simpa [prefixWord, tailWord_6855768, baseEnd_6855768] using wordTrace_append hprefix tailTrace_6855768
  have hstable : (prefixWord ++ tailWord_6855768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855768).length < 2 ^ (prefixWord ++ tailWord_6855768).sum := by decide
  have hdescent : baseEnd_6855768 < baseStart_6855768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855811 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 1, 5]
def baseStart_6855811 : Nat := 118140960795 + 6855811 * 2 ^ 59
def prefixEnd_6855811 : Nat := 4983230072969 + 3 ^ 40 * 6855811 * 2
def baseEnd_6855811 : Nat := 1173442106460527113877735

theorem tailTrace_6855811 : CollatzResearch.WordTrace tailWord_6855811 prefixEnd_6855811 1173442106460527113877735 := by
  unfold tailWord_6855811
  simp only [CollatzResearch.WordTrace]
  refine ⟨250051969765575101145447287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166701313177050067430298191 250051969765575101145447287)
  ·
    refine ⟨375077954648362651718170931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250051969765575101145447287 375077954648362651718170931)
    ·
      refine ⟨562616931972543977577256397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375077954648362651718170931 562616931972543977577256397)
      ·
        refine ⟨210981349489703991591471149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 562616931972543977577256397 210981349489703991591471149)
        ·
          refine ⟨79118006058638996846801681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210981349489703991591471149 79118006058638996846801681)
          ·
            refine ⟨59338504543979247635101261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79118006058638996846801681 59338504543979247635101261)
            ·
              refine ⟨22251939203992217863162973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59338504543979247635101261 22251939203992217863162973)
              ·
                refine ⟨8344477201497081698686115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22251939203992217863162973 8344477201497081698686115)
                ·
                  refine ⟨12516715802245622548029173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8344477201497081698686115 12516715802245622548029173)
                  ·
                    refine ⟨1173442106460527113877735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12516715802245622548029173 1173442106460527113877735)
                    ·
                      rfl

theorem cell23_6855811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 5].length) (baseStart_6855811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855811 prefixEnd_6855811 := by exact prefixLift 6855811
  have htrace : WordTrace (prefixWord ++ tailWord_6855811) baseStart_6855811 baseEnd_6855811 := by
    simpa [prefixWord, tailWord_6855811, baseEnd_6855811] using wordTrace_append hprefix tailTrace_6855811
  have hstable : (prefixWord ++ tailWord_6855811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855811).length < 2 ^ (prefixWord ++ tailWord_6855811).sum := by decide
  have hdescent : baseEnd_6855811 < baseStart_6855811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855818 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2]
def baseStart_6855818 : Nat := 118140960795 + 6855818 * 2 ^ 59
def prefixEnd_6855818 : Nat := 4983230072969 + 3 ^ 40 * 6855818 * 2
def baseEnd_6855818 : Nat := 3520329913746162814245673

theorem tailTrace_6855818 : CollatzResearch.WordTrace tailWord_6855818 prefixEnd_6855818 3520329913746162814245673 := by
  unfold tailWord_6855818
  simp only [CollatzResearch.WordTrace]
  refine ⟨62513056269137435335238027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166701483384366494227301405 62513056269137435335238027)
  ·
    refine ⟨93769584403706153002857041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62513056269137435335238027 93769584403706153002857041)
    ·
      refine ⟨70327188302779614752142781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93769584403706153002857041 70327188302779614752142781)
      ·
        refine ⟨26372695613542355532053543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70327188302779614752142781 26372695613542355532053543)
        ·
          refine ⟨39559043420313533298080315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26372695613542355532053543 39559043420313533298080315)
          ·
            refine ⟨59338565130470299947120473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39559043420313533298080315 59338565130470299947120473)
            ·
              refine ⟨44503923847852724960340355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59338565130470299947120473 44503923847852724960340355)
              ·
                refine ⟨66755885771779087440510533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44503923847852724960340355 66755885771779087440510533)
                ·
                  refine ⟨12516728582208578895095725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66755885771779087440510533 12516728582208578895095725)
                  ·
                    refine ⟨4693773218328217085660897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12516728582208578895095725 4693773218328217085660897)
                    ·
                      refine ⟨3520329913746162814245673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4693773218328217085660897 3520329913746162814245673)
                      ·
                        rfl

theorem cell23_6855818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_6855818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855818 prefixEnd_6855818 := by exact prefixLift 6855818
  have htrace : WordTrace (prefixWord ++ tailWord_6855818) baseStart_6855818 baseEnd_6855818 := by
    simpa [prefixWord, tailWord_6855818, baseEnd_6855818] using wordTrace_append hprefix tailTrace_6855818
  have hstable : (prefixWord ++ tailWord_6855818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855818).length < 2 ^ (prefixWord ++ tailWord_6855818).sum := by decide
  have hdescent : baseEnd_6855818 < baseStart_6855818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855868 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_6855868 : Nat := 118140960795 + 6855868 * 2 ^ 59
def prefixEnd_6855868 : Nat := 4983230072969 + 3 ^ 40 * 6855868 * 2
def baseEnd_6855868 : Nat := 3520355587778887618620443

theorem tailTrace_6855868 : CollatzResearch.WordTrace tailWord_6855868 prefixEnd_6855868 3520355587778887618620443 := by
  unfold tailWord_6855868
  simp only [CollatzResearch.WordTrace]
  refine ⟨125027024363184299940136129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166702699150912399920181505 125027024363184299940136129)
  ·
    refine ⟨93770268272388224955102097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125027024363184299940136129 93770268272388224955102097)
    ·
      refine ⟨70327701204291168716326573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93770268272388224955102097 70327701204291168716326573)
      ·
        refine ⟨26372887951609188268622465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70327701204291168716326573 26372887951609188268622465)
        ·
          refine ⟨19779665963706891201466849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26372887951609188268622465 19779665963706891201466849)
          ·
            refine ⟨14834749472780168401100137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19779665963706891201466849 14834749472780168401100137)
            ·
              refine ⟨11126062104585126300825103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14834749472780168401100137 11126062104585126300825103)
              ·
                refine ⟨16689093156877689451237655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11126062104585126300825103 16689093156877689451237655)
                ·
                  refine ⟨25033639735316534176856483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16689093156877689451237655 25033639735316534176856483)
                  ·
                    refine ⟨37550459602974801265284725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25033639735316534176856483 37550459602974801265284725)
                    ·
                      refine ⟨3520355587778887618620443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37550459602974801265284725 3520355587778887618620443)
                      ·
                        rfl

theorem cell23_6855868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_6855868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855868 prefixEnd_6855868 := by exact prefixLift 6855868
  have htrace : WordTrace (prefixWord ++ tailWord_6855868) baseStart_6855868 baseEnd_6855868 := by
    simpa [prefixWord, tailWord_6855868, baseEnd_6855868] using wordTrace_append hprefix tailTrace_6855868
  have hstable : (prefixWord ++ tailWord_6855868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855868).length < 2 ^ (prefixWord ++ tailWord_6855868).sum := by decide
  have hdescent : baseEnd_6855868 < baseStart_6855868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855882 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2]
def baseStart_6855882 : Nat := 118140960795 + 6855882 * 2 ^ 59
def prefixEnd_6855882 : Nat := 4983230072969 + 3 ^ 40 * 6855882 * 2
def baseEnd_6855882 : Nat := 3520362776508050563845379

theorem tailTrace_6855882 : CollatzResearch.WordTrace tailWord_6855882 prefixEnd_6855882 3520362776508050563845379 := by
  unfold tailWord_6855882
  simp only [CollatzResearch.WordTrace]
  refine ⟨62513639837079470067820475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166703039565545253514187933 62513639837079470067820475)
  ·
    refine ⟨93770459755619205101730713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62513639837079470067820475 93770459755619205101730713)
    ·
      refine ⟨70327844816714403826298035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93770459755619205101730713 70327844816714403826298035)
      ·
        refine ⟨105491767225071605739447053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70327844816714403826298035 105491767225071605739447053)
        ·
          refine ⟨39559412709401852152292645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105491767225071605739447053 39559412709401852152292645)
          ·
            refine ⟨7417389883012847278554871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39559412709401852152292645 7417389883012847278554871)
            ·
              refine ⟨11126084824519270917832307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417389883012847278554871 11126084824519270917832307)
              ·
                refine ⟨16689127236778906376748461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11126084824519270917832307 16689127236778906376748461)
                ·
                  refine ⟨6258422713792089891280673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16689127236778906376748461 6258422713792089891280673)
                  ·
                    refine ⟨4693817035344067418460505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6258422713792089891280673 4693817035344067418460505)
                    ·
                      refine ⟨3520362776508050563845379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4693817035344067418460505 3520362776508050563845379)
                      ·
                        rfl

theorem cell23_6855882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_6855882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855882 prefixEnd_6855882 := by exact prefixLift 6855882
  have htrace : WordTrace (prefixWord ++ tailWord_6855882) baseStart_6855882 baseEnd_6855882 := by
    simpa [prefixWord, tailWord_6855882, baseEnd_6855882] using wordTrace_append hprefix tailTrace_6855882
  have hstable : (prefixWord ++ tailWord_6855882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855882).length < 2 ^ (prefixWord ++ tailWord_6855882).sum := by decide
  have hdescent : baseEnd_6855882 < baseStart_6855882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855892 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_6855892 : Nat := 118140960795 + 6855892 * 2 ^ 59
def prefixEnd_6855892 : Nat := 4983230072969 + 3 ^ 40 * 6855892 * 2
def baseEnd_6855892 : Nat := 1173455970438198508240111

theorem tailTrace_6855892 : CollatzResearch.WordTrace tailWord_6855892 prefixEnd_6855892 1173455970438198508240111 := by
  unfold tailWord_6855892
  simp only [CollatzResearch.WordTrace]
  refine ⟨125027462039140825989572965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166703282718854434652763953 125027462039140825989572965)
  ·
    refine ⟨23442649132338904873044931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125027462039140825989572965 23442649132338904873044931)
    ·
      refine ⟨35163973698508357309567397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23442649132338904873044931 35163973698508357309567397)
      ·
        refine ⟨6593245068470316995543887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35163973698508357309567397 6593245068470316995543887)
        ·
          refine ⟨9889867602705475493315831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6593245068470316995543887 9889867602705475493315831)
          ·
            refine ⟨14834801404058213239973747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9889867602705475493315831 14834801404058213239973747)
            ·
              refine ⟨22252202106087319859960621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14834801404058213239973747 22252202106087319859960621)
              ·
                refine ⟨8344575789782744947485233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22252202106087319859960621 8344575789782744947485233)
                ·
                  refine ⟨6258431842337058710613925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8344575789782744947485233 6258431842337058710613925)
                  ·
                    refine ⟨1173455970438198508240111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6258431842337058710613925 1173455970438198508240111)
                    ·
                      rfl

theorem cell23_6855892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_6855892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855892 prefixEnd_6855892 := by exact prefixLift 6855892
  have htrace : WordTrace (prefixWord ++ tailWord_6855892) baseStart_6855892 baseEnd_6855892 := by
    simpa [prefixWord, tailWord_6855892, baseEnd_6855892] using wordTrace_append hprefix tailTrace_6855892
  have hstable : (prefixWord ++ tailWord_6855892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855892).length < 2 ^ (prefixWord ++ tailWord_6855892).sum := by decide
  have hdescent : baseEnd_6855892 < baseStart_6855892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855932 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_6855932 : Nat := 118140960795 + 6855932 * 2 ^ 59
def prefixEnd_6855932 : Nat := 4983230072969 + 3 ^ 40 * 6855932 * 2
def baseEnd_6855932 : Nat := 3520388450540775368220149

theorem tailTrace_6855932 : CollatzResearch.WordTrace tailWord_6855932 prefixEnd_6855932 3520388450540775368220149 := by
  unfold tailWord_6855932
  simp only [CollatzResearch.WordTrace]
  refine ⟨125028191499068369405301025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166704255332091159207068033 125028191499068369405301025)
  ·
    refine ⟨93771143624301277053975769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125028191499068369405301025 93771143624301277053975769)
    ·
      refine ⟨70328357718225957790481827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93771143624301277053975769 70328357718225957790481827)
      ·
        refine ⟨105492536577338936685722741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70328357718225957790481827 105492536577338936685722741)
        ·
          refine ⟨9889925304125525314286507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105492536577338936685722741 9889925304125525314286507)
          ·
            refine ⟨14834887956188287971429761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9889925304125525314286507 14834887956188287971429761)
            ·
              refine ⟨11126165967141215978572321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14834887956188287971429761 11126165967141215978572321)
              ·
                refine ⟨8344624475355911983929241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11126165967141215978572321 8344624475355911983929241)
                ·
                  refine ⟨6258468356516933987946931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8344624475355911983929241 6258468356516933987946931)
                  ·
                    refine ⟨9387702534775400981920397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6258468356516933987946931 9387702534775400981920397)
                    ·
                      refine ⟨3520388450540775368220149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9387702534775400981920397 3520388450540775368220149)
                      ·
                        rfl

theorem cell23_6855932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_6855932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855932 prefixEnd_6855932 := by exact prefixLift 6855932
  have htrace : WordTrace (prefixWord ++ tailWord_6855932) baseStart_6855932 baseEnd_6855932 := by
    simpa [prefixWord, tailWord_6855932, baseEnd_6855932] using wordTrace_append hprefix tailTrace_6855932
  have hstable : (prefixWord ++ tailWord_6855932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855932).length < 2 ^ (prefixWord ++ tailWord_6855932).sum := by decide
  have hdescent : baseEnd_6855932 < baseStart_6855932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855941 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 1, 6, 3]
def baseStart_6855941 : Nat := 118140960795 + 6855941 * 2 ^ 59
def prefixEnd_6855941 : Nat := 4983230072969 + 3 ^ 40 * 6855941 * 2
def baseEnd_6855941 : Nat := 3520393071866665833007607

theorem tailTrace_6855941 : CollatzResearch.WordTrace tailWord_6855941 prefixEnd_6855941 3520393071866665833007607 := by
  unfold tailWord_6855941
  simp only [CollatzResearch.WordTrace]
  refine ⟨250056711255104133347679677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166704474170069422231786451 250056711255104133347679677)
  ·
    refine ⟨93771266720664050005379879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250056711255104133347679677 93771266720664050005379879)
    ·
      refine ⟨140656900080996075008069819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93771266720664050005379879 140656900080996075008069819)
      ·
        refine ⟨210985350121494112512104729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140656900080996075008069819 210985350121494112512104729)
        ·
          refine ⟨158239012591120584384078547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210985350121494112512104729 158239012591120584384078547)
          ·
            refine ⟨237358518886680876576117821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158239012591120584384078547 237358518886680876576117821)
            ·
              refine ⟨89009444582505328716044183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237358518886680876576117821 89009444582505328716044183)
              ·
                refine ⟨133514166873757993074066275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89009444582505328716044183 133514166873757993074066275)
                ·
                  refine ⟨200271250310636989611099413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133514166873757993074066275 200271250310636989611099413)
                  ·
                    refine ⟨9387714858311108888020285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 200271250310636989611099413 9387714858311108888020285)
                    ·
                      refine ⟨3520393071866665833007607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9387714858311108888020285 3520393071866665833007607)
                      ·
                        rfl

theorem cell23_6855941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_6855941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855941 prefixEnd_6855941 := by exact prefixLift 6855941
  have htrace : WordTrace (prefixWord ++ tailWord_6855941) baseStart_6855941 baseEnd_6855941 := by
    simpa [prefixWord, tailWord_6855941, baseEnd_6855941] using wordTrace_append hprefix tailTrace_6855941
  have hstable : (prefixWord ++ tailWord_6855941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855941).length < 2 ^ (prefixWord ++ tailWord_6855941).sum := by decide
  have hdescent : baseEnd_6855941 < baseStart_6855941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6855989 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_6855989 : Nat := 118140960795 + 6855989 * 2 ^ 59
def prefixEnd_6855989 : Nat := 4983230072969 + 3 ^ 40 * 6855989 * 2
def baseEnd_6855989 : Nat := 3520417718938081645207387

theorem tailTrace_6855989 : CollatzResearch.WordTrace tailWord_6855989 prefixEnd_6855989 3520417718938081645207387 := by
  unfold tailWord_6855989
  simp only [CollatzResearch.WordTrace]
  refine ⟨250058461958930237545427021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166705641305953491696951347 250058461958930237545427021)
  ·
    refine ⟨93771923234598839079535133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250058461958930237545427021 93771923234598839079535133)
    ·
      refine ⟨35164471212974564654825675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93771923234598839079535133 35164471212974564654825675)
      ·
        refine ⟨52746706819461846982238513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35164471212974564654825675 52746706819461846982238513)
        ·
          refine ⟨39560030114596385236678885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52746706819461846982238513 39560030114596385236678885)
          ·
            refine ⟨7417505646486822231877291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39560030114596385236678885 7417505646486822231877291)
            ·
              refine ⟨11126258469730233347815937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417505646486822231877291 11126258469730233347815937)
              ·
                refine ⟨8344693852297675010861953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11126258469730233347815937 8344693852297675010861953)
                ·
                  refine ⟨6258520389223256258146465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8344693852297675010861953 6258520389223256258146465)
                  ·
                    refine ⟨4693890291917442193609849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6258520389223256258146465 4693890291917442193609849)
                    ·
                      refine ⟨3520417718938081645207387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4693890291917442193609849 3520417718938081645207387)
                      ·
                        rfl

theorem cell23_6855989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_6855989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6855989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6855989 prefixEnd_6855989 := by exact prefixLift 6855989
  have htrace : WordTrace (prefixWord ++ tailWord_6855989) baseStart_6855989 baseEnd_6855989 := by
    simpa [prefixWord, tailWord_6855989, baseEnd_6855989] using wordTrace_append hprefix tailTrace_6855989
  have hstable : (prefixWord ++ tailWord_6855989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6855989).length < 2 ^ (prefixWord ++ tailWord_6855989).sum := by decide
  have hdescent : baseEnd_6855989 < baseStart_6855989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6855989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856031 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_6856031 : Nat := 118140960795 + 6856031 * 2 ^ 59
def prefixEnd_6856031 : Nat := 4983230072969 + 3 ^ 40 * 6856031 * 2
def baseEnd_6856031 : Nat := 3520439285125570480882193

theorem tailTrace_6856031 : CollatzResearch.WordTrace tailWord_6856031 prefixEnd_6856031 3520439285125570480882193 := by
  unfold tailWord_6856031
  simp only [CollatzResearch.WordTrace]
  refine ⟨250059993824778078718455947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166706662549852052478970631 250059993824778078718455947)
  ·
    refine ⟨375089990737167118077683921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250059993824778078718455947 375089990737167118077683921)
    ·
      refine ⟨281317493052875338558262941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375089990737167118077683921 281317493052875338558262941)
      ·
        refine ⟨105494059894828251959348603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281317493052875338558262941 105494059894828251959348603)
        ·
          refine ⟨158241089842242377939022905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105494059894828251959348603 158241089842242377939022905)
          ·
            refine ⟨118680817381681783454267179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158241089842242377939022905 118680817381681783454267179)
            ·
              refine ⟨178021226072522675181400769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118680817381681783454267179 178021226072522675181400769)
              ·
                refine ⟨133515919554392006386050577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178021226072522675181400769 133515919554392006386050577)
                ·
                  refine ⟨100136939665794004789537933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133515919554392006386050577 100136939665794004789537933)
                  ·
                    refine ⟨37551352374672751796076725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100136939665794004789537933 37551352374672751796076725)
                    ·
                      refine ⟨3520439285125570480882193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37551352374672751796076725 3520439285125570480882193)
                      ·
                        rfl

theorem cell23_6856031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_6856031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856031 prefixEnd_6856031 := by exact prefixLift 6856031
  have htrace : WordTrace (prefixWord ++ tailWord_6856031) baseStart_6856031 baseEnd_6856031 := by
    simpa [prefixWord, tailWord_6856031, baseEnd_6856031] using wordTrace_append hprefix tailTrace_6856031
  have hstable : (prefixWord ++ tailWord_6856031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856031).length < 2 ^ (prefixWord ++ tailWord_6856031).sum := by decide
  have hdescent : baseEnd_6856031 < baseStart_6856031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856041 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_6856041 : Nat := 118140960795 + 6856041 * 2 ^ 59
def prefixEnd_6856041 : Nat := 4983230072969 + 3 ^ 40 * 6856041 * 2
def baseEnd_6856041 : Nat := 3520444419932115441757147

theorem tailTrace_6856041 : CollatzResearch.WordTrace tailWord_6856041 prefixEnd_6856041 3520444419932115441757147 := by
  unfold tailWord_6856041
  simp only [CollatzResearch.WordTrace]
  refine ⟨250060358554741850426319977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166706905703161233617546651 250060358554741850426319977)
  ·
    refine ⟨187545268916056387819739983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250060358554741850426319977 187545268916056387819739983)
    ·
      refine ⟨281317903374084581729609975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187545268916056387819739983 281317903374084581729609975)
      ·
        refine ⟨421976855061126872594414963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281317903374084581729609975 421976855061126872594414963)
        ·
          refine ⟨632965282591690308891622445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421976855061126872594414963 632965282591690308891622445)
          ·
            refine ⟨237361980971883865834358417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632965282591690308891622445 237361980971883865834358417)
            ·
              refine ⟨178021485728912899375768813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237361980971883865834358417 178021485728912899375768813)
              ·
                refine ⟨66758057148342337265913305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178021485728912899375768813 66758057148342337265913305)
                ·
                  refine ⟨50068542861256752949434979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66758057148342337265913305 50068542861256752949434979)
                  ·
                    refine ⟨75102814291885129424152469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50068542861256752949434979 75102814291885129424152469)
                    ·
                      refine ⟨3520444419932115441757147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75102814291885129424152469 3520444419932115441757147)
                      ·
                        rfl

theorem cell23_6856041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_6856041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856041 prefixEnd_6856041 := by exact prefixLift 6856041
  have htrace : WordTrace (prefixWord ++ tailWord_6856041) baseStart_6856041 baseEnd_6856041 := by
    simpa [prefixWord, tailWord_6856041, baseEnd_6856041] using wordTrace_append hprefix tailTrace_6856041
  have hstable : (prefixWord ++ tailWord_6856041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856041).length < 2 ^ (prefixWord ++ tailWord_6856041).sum := by decide
  have hdescent : baseEnd_6856041 < baseStart_6856041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856045 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_6856045 : Nat := 118140960795 + 6856045 * 2 ^ 59
def prefixEnd_6856045 : Nat := 4983230072969 + 3 ^ 40 * 6856045 * 2
def baseEnd_6856045 : Nat := 3520446473854733426107129

theorem tailTrace_6856045 : CollatzResearch.WordTrace tailWord_6856045 prefixEnd_6856045 3520446473854733426107129 := by
  unfold tailWord_6856045
  simp only [CollatzResearch.WordTrace]
  refine ⟨250060504446727359109465589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166707002964484906072977059 250060504446727359109465589)
  ·
    refine ⟨23443172291880689916512399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250060504446727359109465589 23443172291880689916512399)
    ·
      refine ⟨35164758437821034874768599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23443172291880689916512399 35164758437821034874768599)
      ·
        refine ⟨52747137656731552312152899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35164758437821034874768599 52747137656731552312152899)
        ·
          refine ⟨79120706485097328468229349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52747137656731552312152899 79120706485097328468229349)
          ·
            refine ⟨14835132465955749087793003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79120706485097328468229349 14835132465955749087793003)
            ·
              refine ⟨22252698698933623631689505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14835132465955749087793003 22252698698933623631689505)
              ·
                refine ⟨16689524024200217723767129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22252698698933623631689505 16689524024200217723767129)
                ·
                  refine ⟨12517143018150163292825347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16689524024200217723767129 12517143018150163292825347)
                  ·
                    refine ⟨18775714527225244939238021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12517143018150163292825347 18775714527225244939238021)
                    ·
                      refine ⟨3520446473854733426107129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18775714527225244939238021 3520446473854733426107129)
                      ·
                        rfl

theorem cell23_6856045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_6856045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856045 prefixEnd_6856045 := by exact prefixLift 6856045
  have htrace : WordTrace (prefixWord ++ tailWord_6856045) baseStart_6856045 baseEnd_6856045 := by
    simpa [prefixWord, tailWord_6856045, baseEnd_6856045] using wordTrace_append hprefix tailTrace_6856045
  have hstable : (prefixWord ++ tailWord_6856045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856045).length < 2 ^ (prefixWord ++ tailWord_6856045).sum := by decide
  have hdescent : baseEnd_6856045 < baseStart_6856045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856081 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 2, 9]
def baseStart_6856081 : Nat := 118140960795 + 6856081 * 2 ^ 59
def prefixEnd_6856081 : Nat := 4983230072969 + 3 ^ 40 * 6856081 * 2
def baseEnd_6856081 : Nat := 1173488319719431761752321

theorem tailTrace_6856081 : CollatzResearch.WordTrace tailWord_6856081 prefixEnd_6856081 1173488319719431761752321 := by
  unfold tailWord_6856081
  simp only [CollatzResearch.WordTrace]
  refine ⟨250061817474596937257776097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166707878316397958171850731 250061817474596937257776097)
  ·
    refine ⟨187546363105947702943332073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250061817474596937257776097 187546363105947702943332073)
    ·
      refine ⟨140659772329460777207499055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187546363105947702943332073 140659772329460777207499055)
      ·
        refine ⟨210989658494191165811248583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140659772329460777207499055 210989658494191165811248583)
        ·
          refine ⟨316484487741286748716872875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210989658494191165811248583 316484487741286748716872875)
          ·
            refine ⟨474726731611930123075309313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316484487741286748716872875 474726731611930123075309313)
            ·
              refine ⟨356045048708947592306481985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474726731611930123075309313 356045048708947592306481985)
              ·
                refine ⟨267033786531710694229861489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356045048708947592306481985 267033786531710694229861489)
                ·
                  refine ⟨200275339898783020672396117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267033786531710694229861489 200275339898783020672396117)
                  ·
                    refine ⟨1173488319719431761752321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 200275339898783020672396117 1173488319719431761752321)
                    ·
                      rfl

theorem cell23_6856081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_6856081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856081 prefixEnd_6856081 := by exact prefixLift 6856081
  have htrace : WordTrace (prefixWord ++ tailWord_6856081) baseStart_6856081 baseEnd_6856081 := by
    simpa [prefixWord, tailWord_6856081, baseEnd_6856081] using wordTrace_append hprefix tailTrace_6856081
  have hstable : (prefixWord ++ tailWord_6856081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856081).length < 2 ^ (prefixWord ++ tailWord_6856081).sum := by decide
  have hdescent : baseEnd_6856081 < baseStart_6856081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856091 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 7]
def baseStart_6856091 : Nat := 118140960795 + 6856091 * 2 ^ 59
def prefixEnd_6856091 : Nat := 4983230072969 + 3 ^ 40 * 6856091 * 2
def baseEnd_6856091 : Nat := 3520470093964840246131917

theorem tailTrace_6856091 : CollatzResearch.WordTrace tailWord_6856091 prefixEnd_6856091 3520470093964840246131917 := by
  unfold tailWord_6856091
  simp only [CollatzResearch.WordTrace]
  refine ⟨250062182204560708965640127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166708121469707139310426751 250062182204560708965640127)
  ·
    refine ⟨375093273306841063448460191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250062182204560708965640127 375093273306841063448460191)
    ·
      refine ⟨562639909960261595172690287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375093273306841063448460191 562639909960261595172690287)
      ·
        refine ⟨843959864940392392759035431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562639909960261595172690287 843959864940392392759035431)
        ·
          refine ⟨1265939797410588589138553147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843959864940392392759035431 1265939797410588589138553147)
          ·
            refine ⟨1898909696115882883707829721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265939797410588589138553147 1898909696115882883707829721)
            ·
              refine ⟨1424182272086912162780872291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898909696115882883707829721 1424182272086912162780872291)
              ·
                refine ⟨2136273408130368244171308437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424182272086912162780872291 2136273408130368244171308437)
                ·
                  refine ⟨100137816006111011445530083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2136273408130368244171308437 100137816006111011445530083)
                  ·
                    refine ⟨150206724009166517168295125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100137816006111011445530083 150206724009166517168295125)
                    ·
                      refine ⟨3520470093964840246131917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150206724009166517168295125 3520470093964840246131917)
                      ·
                        rfl

theorem cell23_6856091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_6856091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856091 prefixEnd_6856091 := by exact prefixLift 6856091
  have htrace : WordTrace (prefixWord ++ tailWord_6856091) baseStart_6856091 baseEnd_6856091 := by
    simpa [prefixWord, tailWord_6856091, baseEnd_6856091] using wordTrace_append hprefix tailTrace_6856091
  have hstable : (prefixWord ++ tailWord_6856091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856091).length < 2 ^ (prefixWord ++ tailWord_6856091).sum := by decide
  have hdescent : baseEnd_6856091 < baseStart_6856091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856128 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 1, 6]
def baseStart_6856128 : Nat := 118140960795 + 6856128 * 2 ^ 59
def prefixEnd_6856128 : Nat := 4983230072969 + 3 ^ 40 * 6856128 * 2
def baseEnd_6856128 : Nat := 1173496364249685533789749

theorem tailTrace_6856128 : CollatzResearch.WordTrace tailWord_6856128 prefixEnd_6856128 1173496364249685533789749 := by
  unfold tailWord_6856128
  simp only [CollatzResearch.WordTrace]
  refine ⟨125031765852713332142368519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166709021136951109523158025 125031765852713332142368519)
  ·
    refine ⟨187547648779069998213552779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125031765852713332142368519 187547648779069998213552779)
    ·
      refine ⟨281321473168604997320329169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187547648779069998213552779 281321473168604997320329169)
      ·
        refine ⟨210991104876453747990246877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281321473168604997320329169 210991104876453747990246877)
        ·
          refine ⟨79121664328670155496342579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210991104876453747990246877 79121664328670155496342579)
          ·
            refine ⟨118682496493005233244513869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79121664328670155496342579 118682496493005233244513869)
            ·
              refine ⟨44505936184876962466692701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118682496493005233244513869 44505936184876962466692701)
              ·
                refine ⟨16689726069328860925009763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44505936184876962466692701 16689726069328860925009763)
                ·
                  refine ⟨25034589103993291387514645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16689726069328860925009763 25034589103993291387514645)
                  ·
                    refine ⟨1173496364249685533789749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25034589103993291387514645 1173496364249685533789749)
                    ·
                      rfl

theorem cell23_6856128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_6856128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856128 prefixEnd_6856128 := by exact prefixLift 6856128
  have htrace : WordTrace (prefixWord ++ tailWord_6856128) baseStart_6856128 baseEnd_6856128 := by
    simpa [prefixWord, tailWord_6856128, baseEnd_6856128] using wordTrace_append hprefix tailTrace_6856128
  have hstable : (prefixWord ++ tailWord_6856128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856128).length < 2 ^ (prefixWord ++ tailWord_6856128).sum := by decide
  have hdescent : baseEnd_6856128 < baseStart_6856128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856130 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_6856130 : Nat := 118140960795 + 6856130 * 2 ^ 59
def prefixEnd_6856130 : Nat := 4983230072969 + 3 ^ 40 * 6856130 * 2
def baseEnd_6856130 : Nat := 3520490119710365593544239

theorem tailTrace_6856130 : CollatzResearch.WordTrace tailWord_6856130 prefixEnd_6856130 3520490119710365593544239 := by
  unfold tailWord_6856130
  simp only [CollatzResearch.WordTrace]
  refine ⟨62515901162854854656577461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166709069767612945750873229 62515901162854854656577461)
  ·
    refine ⟨5860865734017642624054137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62515901162854854656577461 5860865734017642624054137)
    ·
      refine ⟨4395649300513231968040603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5860865734017642624054137 4395649300513231968040603)
      ·
        refine ⟨6593473950769847952060905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4395649300513231968040603 6593473950769847952060905)
        ·
          refine ⟨4945105463077385964045679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6593473950769847952060905 4945105463077385964045679)
          ·
            refine ⟨7417658194616078946068519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945105463077385964045679 7417658194616078946068519)
            ·
              refine ⟨11126487291924118419102779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417658194616078946068519 11126487291924118419102779)
              ·
                refine ⟨16689730937886177628654169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11126487291924118419102779 16689730937886177628654169)
                ·
                  refine ⟨12517298203414633221490627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16689730937886177628654169 12517298203414633221490627)
                  ·
                    refine ⟨18775947305121949832235941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12517298203414633221490627 18775947305121949832235941)
                    ·
                      refine ⟨3520490119710365593544239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18775947305121949832235941 3520490119710365593544239)
                      ·
                        rfl

theorem cell23_6856130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_6856130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856130 prefixEnd_6856130 := by exact prefixLift 6856130
  have htrace : WordTrace (prefixWord ++ tailWord_6856130) baseStart_6856130 baseEnd_6856130 := by
    simpa [prefixWord, tailWord_6856130, baseEnd_6856130] using wordTrace_append hprefix tailTrace_6856130
  have hstable : (prefixWord ++ tailWord_6856130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856130).length < 2 ^ (prefixWord ++ tailWord_6856130).sum := by decide
  have hdescent : baseEnd_6856130 < baseStart_6856130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856135 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_6856135 : Nat := 118140960795 + 6856135 * 2 ^ 59
def prefixEnd_6856135 : Nat := 4983230072969 + 3 ^ 40 * 6856135 * 2
def baseEnd_6856135 : Nat := 3520492687113638073981715

theorem tailTrace_6856135 : CollatzResearch.WordTrace tailWord_6856135 prefixEnd_6856135 3520492687113638073981715 := by
  unfold tailWord_6856135
  simp only [CollatzResearch.WordTrace]
  refine ⟨250063787016401304480241859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166709191344267536320161239 250063787016401304480241859)
  ·
    refine ⟨375095680524601956720362789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250063787016401304480241859 375095680524601956720362789)
    ·
      refine ⟨70330440098362866885068023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375095680524601956720362789 70330440098362866885068023)
      ·
        refine ⟨105495660147544300327602035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70330440098362866885068023 105495660147544300327602035)
        ·
          refine ⟨158243490221316450491403053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105495660147544300327602035 158243490221316450491403053)
          ·
            refine ⟨59341308832993668934276145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158243490221316450491403053 59341308832993668934276145)
            ·
              refine ⟨44505981624745251700707109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59341308832993668934276145 44505981624745251700707109)
              ·
                refine ⟨8344871554639734693882583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44505981624745251700707109 8344871554639734693882583)
                ·
                  refine ⟨12517307331959602040823875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8344871554639734693882583 12517307331959602040823875)
                  ·
                    refine ⟨18775960997939403061235813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12517307331959602040823875 18775960997939403061235813)
                    ·
                      refine ⟨3520492687113638073981715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18775960997939403061235813 3520492687113638073981715)
                      ·
                        rfl

theorem cell23_6856135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_6856135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856135 prefixEnd_6856135 := by exact prefixLift 6856135
  have htrace : WordTrace (prefixWord ++ tailWord_6856135) baseStart_6856135 baseEnd_6856135 := by
    simpa [prefixWord, tailWord_6856135, baseEnd_6856135] using wordTrace_append hprefix tailTrace_6856135
  have hstable : (prefixWord ++ tailWord_6856135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856135).length < 2 ^ (prefixWord ++ tailWord_6856135).sum := by decide
  have hdescent : baseEnd_6856135 < baseStart_6856135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856152 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 1, 1, 4]
def baseStart_6856152 : Nat := 118140960795 + 6856152 * 2 ^ 59
def prefixEnd_6856152 : Nat := 4983230072969 + 3 ^ 40 * 6856152 * 2
def baseEnd_6856152 : Nat := 3520501416284764507469137

theorem tailTrace_6856152 : CollatzResearch.WordTrace tailWord_6856152 prefixEnd_6856152 3520501416284764507469137 := by
  unfold tailWord_6856152
  simp only [CollatzResearch.WordTrace]
  refine ⟨125032203528669858191805355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166709604704893144255740473 125032203528669858191805355)
  ·
    refine ⟨187548305293004787287708033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125032203528669858191805355 187548305293004787287708033)
    ·
      refine ⟨140661228969753590465781025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187548305293004787287708033 140661228969753590465781025)
      ·
        refine ⟨105495921727315192849335769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140661228969753590465781025 105495921727315192849335769)
        ·
          refine ⟨79121941295486394637001827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105495921727315192849335769 79121941295486394637001827)
          ·
            refine ⟨118682911943229591955502741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79121941295486394637001827 118682911943229591955502741)
            ·
              refine ⟨5563261497338887122914191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118682911943229591955502741 5563261497338887122914191)
              ·
                refine ⟨8344892246008330684371287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5563261497338887122914191 8344892246008330684371287)
                ·
                  refine ⟨12517338369012496026556931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8344892246008330684371287 12517338369012496026556931)
                  ·
                    refine ⟨18776007553518744039835397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12517338369012496026556931 18776007553518744039835397)
                    ·
                      refine ⟨3520501416284764507469137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18776007553518744039835397 3520501416284764507469137)
                      ·
                        rfl

theorem cell23_6856152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_6856152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856152 prefixEnd_6856152 := by exact prefixLift 6856152
  have htrace : WordTrace (prefixWord ++ tailWord_6856152) baseStart_6856152 baseEnd_6856152 := by
    simpa [prefixWord, tailWord_6856152, baseEnd_6856152] using wordTrace_append hprefix tailTrace_6856152
  have hstable : (prefixWord ++ tailWord_6856152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856152).length < 2 ^ (prefixWord ++ tailWord_6856152).sum := by decide
  have hdescent : baseEnd_6856152 < baseStart_6856152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856182 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_6856182 : Nat := 118140960795 + 6856182 * 2 ^ 59
def prefixEnd_6856182 : Nat := 4983230072969 + 3 ^ 40 * 6856182 * 2
def baseEnd_6856182 : Nat := 3520516820704399390093999

theorem tailTrace_6856182 : CollatzResearch.WordTrace tailWord_6856182 prefixEnd_6856182 3520516820704399390093999 := by
  unfold tailWord_6856182
  simp only [CollatzResearch.WordTrace]
  refine ⟨15629093827951939469200175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166710334164820687671468533 15629093827951939469200175)
  ·
    refine ⟨23443640741927909203800263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15629093827951939469200175 23443640741927909203800263)
    ·
      refine ⟨35165461112891863805700395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23443640741927909203800263 35165461112891863805700395)
      ·
        refine ⟨52748191669337795708550593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35165461112891863805700395 52748191669337795708550593)
        ·
          refine ⟨39561143752003346781412945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52748191669337795708550593 39561143752003346781412945)
          ·
            refine ⟨29670857814002510086059709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39561143752003346781412945 29670857814002510086059709)
            ·
              refine ⟨11126571680250941282272391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29670857814002510086059709 11126571680250941282272391)
              ·
                refine ⟨16689857520376411923408587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11126571680250941282272391 16689857520376411923408587)
                ·
                  refine ⟨25034786280564617885112881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16689857520376411923408587 25034786280564617885112881)
                  ·
                    refine ⟨18776089710423463413834661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25034786280564617885112881 18776089710423463413834661)
                    ·
                      refine ⟨3520516820704399390093999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18776089710423463413834661 3520516820704399390093999)
                      ·
                        rfl

theorem cell23_6856182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_6856182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856182 prefixEnd_6856182 := by exact prefixLift 6856182
  have htrace : WordTrace (prefixWord ++ tailWord_6856182) baseStart_6856182 baseEnd_6856182 := by
    simpa [prefixWord, tailWord_6856182, baseEnd_6856182] using wordTrace_append hprefix tailTrace_6856182
  have hstable : (prefixWord ++ tailWord_6856182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856182).length < 2 ^ (prefixWord ++ tailWord_6856182).sum := by decide
  have hdescent : baseEnd_6856182 < baseStart_6856182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856188 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_6856188 : Nat := 118140960795 + 6856188 * 2 ^ 59
def prefixEnd_6856188 : Nat := 4983230072969 + 3 ^ 40 * 6856188 * 2
def baseEnd_6856188 : Nat := 1173506633862775455539657

theorem tailTrace_6856188 : CollatzResearch.WordTrace tailWord_6856188 prefixEnd_6856188 1173506633862775455539657 := by
  unfold tailWord_6856188
  simp only [CollatzResearch.WordTrace]
  refine ⟨125032860042604647265960609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166710480056806196354614145 125032860042604647265960609)
  ·
    refine ⟨93774645031953485449470457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125032860042604647265960609 93774645031953485449470457)
    ·
      refine ⟨70330983773965114087102843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93774645031953485449470457 70330983773965114087102843)
      ·
        refine ⟨105496475660947671130654265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70330983773965114087102843 105496475660947671130654265)
        ·
          refine ⟨79122356745710753347990699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105496475660947671130654265 79122356745710753347990699)
          ·
            refine ⟨118683535118566130021986049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79122356745710753347990699 118683535118566130021986049)
            ·
              refine ⟨89012651338924597516489537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118683535118566130021986049 89012651338924597516489537)
              ·
                refine ⟨66759488504193448137367153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89012651338924597516489537 66759488504193448137367153)
                ·
                  refine ⟨50069616378145086103025365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66759488504193448137367153 50069616378145086103025365)
                  ·
                    refine ⟨1173506633862775455539657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50069616378145086103025365 1173506633862775455539657)
                    ·
                      rfl

theorem cell23_6856188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_6856188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856188 prefixEnd_6856188 := by exact prefixLift 6856188
  have htrace : WordTrace (prefixWord ++ tailWord_6856188) baseStart_6856188 baseEnd_6856188 := by
    simpa [prefixWord, tailWord_6856188, baseEnd_6856188] using wordTrace_append hprefix tailTrace_6856188
  have hstable : (prefixWord ++ tailWord_6856188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856188).length < 2 ^ (prefixWord ++ tailWord_6856188).sum := by decide
  have hdescent : baseEnd_6856188 < baseStart_6856188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856202 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_6856202 : Nat := 118140960795 + 6856202 * 2 ^ 59
def prefixEnd_6856202 : Nat := 4983230072969 + 3 ^ 40 * 6856202 * 2
def baseEnd_6856202 : Nat := 3520527090317489311843907

theorem tailTrace_6856202 : CollatzResearch.WordTrace tailWord_6856202 prefixEnd_6856202 3520527090317489311843907 := by
  unfold tailWord_6856202
  simp only [CollatzResearch.WordTrace]
  refine ⟨62516557676789643730732715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166710820471439049948620573 62516557676789643730732715)
  ·
    refine ⟨93774836515184465596099073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62516557676789643730732715 93774836515184465596099073)
    ·
      refine ⟨70331127386388349197074305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93774836515184465596099073 70331127386388349197074305)
      ·
        refine ⟨52748345539791261897805729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70331127386388349197074305 52748345539791261897805729)
        ·
          refine ⟨39561259154843446423354297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52748345539791261897805729 39561259154843446423354297)
          ·
            refine ⟨29670944366132584817515723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39561259154843446423354297 29670944366132584817515723)
            ·
              refine ⟨44506416549198877226273585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29670944366132584817515723 44506416549198877226273585)
              ·
                refine ⟨33379812411899157919705189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44506416549198877226273585 33379812411899157919705189)
                ·
                  refine ⟨6258714827231092109944723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33379812411899157919705189 6258714827231092109944723)
                  ·
                    refine ⟨9388072240846638164917085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6258714827231092109944723 9388072240846638164917085)
                    ·
                      refine ⟨3520527090317489311843907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9388072240846638164917085 3520527090317489311843907)
                      ·
                        rfl

theorem cell23_6856202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_6856202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856202 prefixEnd_6856202 := by exact prefixLift 6856202
  have htrace : WordTrace (prefixWord ++ tailWord_6856202) baseStart_6856202 baseEnd_6856202 := by
    simpa [prefixWord, tailWord_6856202, baseEnd_6856202] using wordTrace_append hprefix tailTrace_6856202
  have hstable : (prefixWord ++ tailWord_6856202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856202).length < 2 ^ (prefixWord ++ tailWord_6856202).sum := by decide
  have hdescent : baseEnd_6856202 < baseStart_6856202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856203 : List Nat := [1, 1, 1, 1, 8, 2, 1, 3, 1, 2, 2]
def baseStart_6856203 : Nat := 118140960795 + 6856203 * 2 ^ 59
def prefixEnd_6856203 : Nat := 4983230072969 + 3 ^ 40 * 6856203 * 2
def baseEnd_6856203 : Nat := 3520527603798143807931403

theorem tailTrace_6856203 : CollatzResearch.WordTrace tailWord_6856203 prefixEnd_6856203 3520527603798143807931403 := by
  unfold tailWord_6856203
  simp only [CollatzResearch.WordTrace]
  refine ⟨250066267180154952093717263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166710844786769968062478175 250066267180154952093717263)
  ·
    refine ⟨375099400770232428140575895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250066267180154952093717263 375099400770232428140575895)
    ·
      refine ⟨562649101155348642210863843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375099400770232428140575895 562649101155348642210863843)
      ·
        refine ⟨843973651733022963316295765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562649101155348642210863843 843973651733022963316295765)
        ·
          refine ⟨9890316231246362851362841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 843973651733022963316295765 9890316231246362851362841)
          ·
            refine ⟨7417737173434772138522131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9890316231246362851362841 7417737173434772138522131)
            ·
              refine ⟨11126605760152158207783197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417737173434772138522131 11126605760152158207783197)
              ·
                refine ⟨4172477160057059327918699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11126605760152158207783197 4172477160057059327918699)
                ·
                  refine ⟨6258715740085588991878049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172477160057059327918699 6258715740085588991878049)
                  ·
                    refine ⟨4694036805064191743908537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6258715740085588991878049 4694036805064191743908537)
                    ·
                      refine ⟨3520527603798143807931403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694036805064191743908537 3520527603798143807931403)
                      ·
                        rfl

theorem cell23_6856203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 1, 2, 2].length) (baseStart_6856203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856203 prefixEnd_6856203 := by exact prefixLift 6856203
  have htrace : WordTrace (prefixWord ++ tailWord_6856203) baseStart_6856203 baseEnd_6856203 := by
    simpa [prefixWord, tailWord_6856203, baseEnd_6856203] using wordTrace_append hprefix tailTrace_6856203
  have hstable : (prefixWord ++ tailWord_6856203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856203).length < 2 ^ (prefixWord ++ tailWord_6856203).sum := by decide
  have hdescent : baseEnd_6856203 < baseStart_6856203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856242 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2]
def baseStart_6856242 : Nat := 118140960795 + 6856242 * 2 ^ 59
def prefixEnd_6856242 : Nat := 4983230072969 + 3 ^ 40 * 6856242 * 2
def baseEnd_6856242 : Nat := 3520547629543669155343723

theorem tailTrace_6856242 : CollatzResearch.WordTrace tailWord_6856242 prefixEnd_6856242 3520547629543669155343723 := by
  unfold tailWord_6856242
  simp only [CollatzResearch.WordTrace]
  refine ⟨62516922406753415438596745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166711793084675774502924653 62516922406753415438596745)
  ·
    refine ⟨46887691805065061578947559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62516922406753415438596745 46887691805065061578947559)
    ·
      refine ⟨70331537707597592368421339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46887691805065061578947559 70331537707597592368421339)
      ·
        refine ⟨105497306561396388552632009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70331537707597592368421339 105497306561396388552632009)
        ·
          refine ⟨79122979921047291414474007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105497306561396388552632009 79122979921047291414474007)
          ·
            refine ⟨118684469881570937121711011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79122979921047291414474007 118684469881570937121711011)
            ·
              refine ⟨178026704822356405682566517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118684469881570937121711011 178026704822356405682566517)
              ·
                refine ⟨16690003577095913032740611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178026704822356405682566517 16690003577095913032740611)
                ·
                  refine ⟨25035005365643869549110917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16690003577095913032740611 25035005365643869549110917)
                  ·
                    refine ⟨4694063506058225540458297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25035005365643869549110917 4694063506058225540458297)
                    ·
                      refine ⟨3520547629543669155343723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694063506058225540458297 3520547629543669155343723)
                      ·
                        rfl

theorem cell23_6856242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_6856242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856242 prefixEnd_6856242 := by exact prefixLift 6856242
  have htrace : WordTrace (prefixWord ++ tailWord_6856242) baseStart_6856242 baseEnd_6856242 := by
    simpa [prefixWord, tailWord_6856242, baseEnd_6856242] using wordTrace_append hprefix tailTrace_6856242
  have hstable : (prefixWord ++ tailWord_6856242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856242).length < 2 ^ (prefixWord ++ tailWord_6856242).sum := by decide
  have hdescent : baseEnd_6856242 < baseStart_6856242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856245 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_6856245 : Nat := 118140960795 + 6856245 * 2 ^ 59
def prefixEnd_6856245 : Nat := 4983230072969 + 3 ^ 40 * 6856245 * 2
def baseEnd_6856245 : Nat := 3520549169985632643606209

theorem tailTrace_6856245 : CollatzResearch.WordTrace tailWord_6856245 prefixEnd_6856245 3520549169985632643606209 := by
  unfold tailWord_6856245
  simp only [CollatzResearch.WordTrace]
  refine ⟨250067799046002793266746189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166711866030668528844497459 250067799046002793266746189)
  ·
    refine ⟨93775424642251047475029821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250067799046002793266746189 93775424642251047475029821)
    ·
      refine ⟨35165784240844142803136183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93775424642251047475029821 35165784240844142803136183)
      ·
        refine ⟨52748676361266214204704275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35165784240844142803136183 52748676361266214204704275)
        ·
          refine ⟨79123014541899321307056413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52748676361266214204704275 79123014541899321307056413)
          ·
            refine ⟨29671130453212245490146155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79123014541899321307056413 29671130453212245490146155)
            ·
              refine ⟨44506695679818368235219233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29671130453212245490146155 44506695679818368235219233)
              ·
                refine ⟨33380021759863776176414425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44506695679818368235219233 33380021759863776176414425)
                ·
                  refine ⟨25035016319897832132310819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33380021759863776176414425 25035016319897832132310819)
                  ·
                    refine ⟨37552524479846748198466229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25035016319897832132310819 37552524479846748198466229)
                    ·
                      refine ⟨3520549169985632643606209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37552524479846748198466229 3520549169985632643606209)
                      ·
                        rfl

theorem cell23_6856245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_6856245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856245 prefixEnd_6856245 := by exact prefixLift 6856245
  have htrace : WordTrace (prefixWord ++ tailWord_6856245) baseStart_6856245 baseEnd_6856245 := by
    simpa [prefixWord, tailWord_6856245, baseEnd_6856245] using wordTrace_append hprefix tailTrace_6856245
  have hstable : (prefixWord ++ tailWord_6856245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856245).length < 2 ^ (prefixWord ++ tailWord_6856245).sum := by decide
  have hdescent : baseEnd_6856245 < baseStart_6856245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856246 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_6856246 : Nat := 118140960795 + 6856246 * 2 ^ 59
def prefixEnd_6856246 : Nat := 4983230072969 + 3 ^ 40 * 6856246 * 2
def baseEnd_6856246 : Nat := 3520549683466287139693705

theorem tailTrace_6856246 : CollatzResearch.WordTrace tailWord_6856246 prefixEnd_6856246 3520549683466287139693705 := by
  unfold tailWord_6856246
  simp only [CollatzResearch.WordTrace]
  refine ⟨15629239719937448152345787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166711890345999446958355061 15629239719937448152345787)
  ·
    refine ⟨23443859579906172228518681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15629239719937448152345787 23443859579906172228518681)
    ·
      refine ⟨17582894684929629171389011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23443859579906172228518681 17582894684929629171389011)
      ·
        refine ⟨26374342027394443757083517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17582894684929629171389011 26374342027394443757083517)
        ·
          refine ⟨9890378260272916408906319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26374342027394443757083517 9890378260272916408906319)
          ·
            refine ⟨14835567390409374613359479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9890378260272916408906319 14835567390409374613359479)
            ·
              refine ⟨22253351085614061920039219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14835567390409374613359479 22253351085614061920039219)
              ·
                refine ⟨33380026628421092880058829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22253351085614061920039219 33380026628421092880058829)
                ·
                  refine ⟨12517509985657909830022061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33380026628421092880058829 12517509985657909830022061)
                  ·
                    refine ⟨4694066244621716186258273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12517509985657909830022061 4694066244621716186258273)
                    ·
                      refine ⟨3520549683466287139693705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694066244621716186258273 3520549683466287139693705)
                      ·
                        rfl

theorem cell23_6856246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_6856246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856246 prefixEnd_6856246 := by exact prefixLift 6856246
  have htrace : WordTrace (prefixWord ++ tailWord_6856246) baseStart_6856246 baseEnd_6856246 := by
    simpa [prefixWord, tailWord_6856246, baseEnd_6856246] using wordTrace_append hprefix tailTrace_6856246
  have hstable : (prefixWord ++ tailWord_6856246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856246).length < 2 ^ (prefixWord ++ tailWord_6856246).sum := by decide
  have hdescent : baseEnd_6856246 < baseStart_6856246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856276 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_6856276 : Nat := 118140960795 + 6856276 * 2 ^ 59
def prefixEnd_6856276 : Nat := 4983230072969 + 3 ^ 40 * 6856276 * 2
def baseEnd_6856276 : Nat := 3520565087885922022318567

theorem tailTrace_6856276 : CollatzResearch.WordTrace tailWord_6856276 prefixEnd_6856276 3520565087885922022318567 := by
  unfold tailWord_6856276
  simp only [CollatzResearch.WordTrace]
  refine ⟨125034464854445242780562341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166712619805926990374083121 125034464854445242780562341)
  ·
    refine ⟨23443962160208483021355439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125034464854445242780562341 23443962160208483021355439)
    ·
      refine ⟨35165943240312724532033159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23443962160208483021355439 35165943240312724532033159)
      ·
        refine ⟨52748914860469086798049739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35165943240312724532033159 52748914860469086798049739)
        ·
          refine ⟨79123372290703630197074609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52748914860469086798049739 79123372290703630197074609)
          ·
            refine ⟨59342529218027722647805957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79123372290703630197074609 59342529218027722647805957)
            ·
              refine ⟨11126724228380197996463617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59342529218027722647805957 11126724228380197996463617)
              ·
                refine ⟨8345043171285148497347713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11126724228380197996463617 8345043171285148497347713)
                ·
                  refine ⟨6258782378463861373010785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8345043171285148497347713 6258782378463861373010785)
                  ·
                    refine ⟨4694086783847896029758089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6258782378463861373010785 4694086783847896029758089)
                    ·
                      refine ⟨3520565087885922022318567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694086783847896029758089 3520565087885922022318567)
                      ·
                        rfl

theorem cell23_6856276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_6856276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856276 prefixEnd_6856276 := by exact prefixLift 6856276
  have htrace : WordTrace (prefixWord ++ tailWord_6856276) baseStart_6856276 baseEnd_6856276 := by
    simpa [prefixWord, tailWord_6856276, baseEnd_6856276] using wordTrace_append hprefix tailTrace_6856276
  have hstable : (prefixWord ++ tailWord_6856276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856276).length < 2 ^ (prefixWord ++ tailWord_6856276).sum := by decide
  have hdescent : baseEnd_6856276 < baseStart_6856276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856292 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_6856292 : Nat := 118140960795 + 6856292 * 2 ^ 59
def prefixEnd_6856292 : Nat := 4983230072969 + 3 ^ 40 * 6856292 * 2
def baseEnd_6856292 : Nat := 3520573303576393959718493

theorem tailTrace_6856292 : CollatzResearch.WordTrace tailWord_6856292 prefixEnd_6856292 3520573303576393959718493 := by
  unfold tailWord_6856292
  simp only [CollatzResearch.WordTrace]
  refine ⟨125034756638416260146853565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166713008851221680195804753 125034756638416260146853565)
  ·
    refine ⟨46888033739406097555070087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125034756638416260146853565 46888033739406097555070087)
    ·
      refine ⟨70332050609109146332605131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46888033739406097555070087 70332050609109146332605131)
      ·
        refine ⟨105498075913663719498907697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70332050609109146332605131 105498075913663719498907697)
        ·
          refine ⟨79123556935247789624180773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105498075913663719498907697 79123556935247789624180773)
          ·
            refine ⟨14835666925358960554533895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79123556935247789624180773 14835666925358960554533895)
            ·
              refine ⟨22253500388038440831800843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14835666925358960554533895 22253500388038440831800843)
              ·
                refine ⟨33380250582057661247701265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22253500388038440831800843 33380250582057661247701265)
                ·
                  refine ⟨25035187936543245935775949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33380250582057661247701265 25035187936543245935775949)
                  ·
                    refine ⟨9388195476203717225915981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25035187936543245935775949 9388195476203717225915981)
                    ·
                      refine ⟨3520573303576393959718493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9388195476203717225915981 3520573303576393959718493)
                      ·
                        rfl

theorem cell23_6856292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_6856292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856292 prefixEnd_6856292 := by exact prefixLift 6856292
  have htrace : WordTrace (prefixWord ++ tailWord_6856292) baseStart_6856292 baseEnd_6856292 := by
    simpa [prefixWord, tailWord_6856292, baseEnd_6856292] using wordTrace_append hprefix tailTrace_6856292
  have hstable : (prefixWord ++ tailWord_6856292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856292).length < 2 ^ (prefixWord ++ tailWord_6856292).sum := by decide
  have hdescent : baseEnd_6856292 < baseStart_6856292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856295 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 4, 5]
def baseStart_6856295 : Nat := 118140960795 + 6856295 * 2 ^ 59
def prefixEnd_6856295 : Nat := 4983230072969 + 3 ^ 40 * 6856295 * 2
def baseEnd_6856295 : Nat := 1173524948006119149326993

theorem tailTrace_6856295 : CollatzResearch.WordTrace tailWord_6856295 prefixEnd_6856295 1173524948006119149326993 := by
  unfold tailWord_6856295
  simp only [CollatzResearch.WordTrace]
  refine ⟨250069622695821651806066339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166713081797214434537377559 250069622695821651806066339)
  ·
    refine ⟨375104434043732477709099509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250069622695821651806066339 375104434043732477709099509)
    ·
      refine ⟨35166040691599919785228079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 375104434043732477709099509 35166040691599919785228079)
      ·
        refine ⟨52749061037399879677842119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35166040691599919785228079 52749061037399879677842119)
        ·
          refine ⟨79123591556099819516763179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52749061037399879677842119 79123591556099819516763179)
          ·
            refine ⟨118685387334149729275144769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79123591556099819516763179 118685387334149729275144769)
            ·
              refine ⟨89014040500612296956358577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118685387334149729275144769 89014040500612296956358577)
              ·
                refine ⟨66760530375459222717268933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89014040500612296956358577 66760530375459222717268933)
                ·
                  refine ⟨12517599445398604259487925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66760530375459222717268933 12517599445398604259487925)
                  ·
                    refine ⟨1173524948006119149326993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12517599445398604259487925 1173524948006119149326993)
                    ·
                      rfl

theorem cell23_6856295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_6856295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856295 prefixEnd_6856295 := by exact prefixLift 6856295
  have htrace : WordTrace (prefixWord ++ tailWord_6856295) baseStart_6856295 baseEnd_6856295 := by
    simpa [prefixWord, tailWord_6856295, baseEnd_6856295] using wordTrace_append hprefix tailTrace_6856295
  have hstable : (prefixWord ++ tailWord_6856295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856295).length < 2 ^ (prefixWord ++ tailWord_6856295).sum := by decide
  have hdescent : baseEnd_6856295 < baseStart_6856295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856315 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 4]
def baseStart_6856315 : Nat := 118140960795 + 6856315 * 2 ^ 59
def prefixEnd_6856315 : Nat := 4983230072969 + 3 ^ 40 * 6856315 * 2
def baseEnd_6856315 : Nat := 3520585113631447369730887

theorem tailTrace_6856315 : CollatzResearch.WordTrace tailWord_6856315 prefixEnd_6856315 3520585113631447369730887 := by
  unfold tailWord_6856315
  simp only [CollatzResearch.WordTrace]
  refine ⟨250070352155749195221794399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166713568103832796814529599 250070352155749195221794399)
  ·
    refine ⟨375105528233623792832691599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250070352155749195221794399 375105528233623792832691599)
    ·
      refine ⟨562658292350435689249037399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375105528233623792832691599 562658292350435689249037399)
      ·
        refine ⟨843987438525653533873556099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562658292350435689249037399 843987438525653533873556099)
        ·
          refine ⟨1265981157788480300810334149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843987438525653533873556099 1265981157788480300810334149)
          ·
            refine ⟨237371467085340056401937653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1265981157788480300810334149 237371467085340056401937653)
            ·
              refine ⟨22253575039250630287681655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237371467085340056401937653 22253575039250630287681655)
              ·
                refine ⟨33380362558875945431522483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22253575039250630287681655 33380362558875945431522483)
                ·
                  refine ⟨50070543838313918147283725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33380362558875945431522483 50070543838313918147283725)
                  ·
                    refine ⟨18776453939367719305231397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50070543838313918147283725 18776453939367719305231397)
                    ·
                      refine ⟨3520585113631447369730887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18776453939367719305231397 3520585113631447369730887)
                      ·
                        rfl

theorem cell23_6856315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 4].length) (baseStart_6856315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856315 prefixEnd_6856315 := by exact prefixLift 6856315
  have htrace : WordTrace (prefixWord ++ tailWord_6856315) baseStart_6856315 baseEnd_6856315 := by
    simpa [prefixWord, tailWord_6856315, baseEnd_6856315] using wordTrace_append hprefix tailTrace_6856315
  have hstable : (prefixWord ++ tailWord_6856315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856315).length < 2 ^ (prefixWord ++ tailWord_6856315).sum := by decide
  have hdescent : baseEnd_6856315 < baseStart_6856315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856332 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 4, 4, 2]
def baseStart_6856332 : Nat := 118140960795 + 6856332 * 2 ^ 59
def prefixEnd_6856332 : Nat := 4983230072969 + 3 ^ 40 * 6856332 * 2
def baseEnd_6856332 : Nat := 3520593842802573803218309

theorem tailTrace_6856332 : CollatzResearch.WordTrace tailWord_6856332 prefixEnd_6856332 3520593842802573803218309 := by
  unfold tailWord_6856332
  simp only [CollatzResearch.WordTrace]
  refine ⟨125035486098343803562581625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166713981464458404750108833 125035486098343803562581625)
  ·
    refine ⟨93776614573757852671936219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125035486098343803562581625 93776614573757852671936219)
    ·
      refine ⟨140664921860636779007904329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93776614573757852671936219 140664921860636779007904329)
      ·
        refine ⟨105498691395477584255928247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140664921860636779007904329 105498691395477584255928247)
        ·
          refine ⟨158248037093216376383892371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105498691395477584255928247 158248037093216376383892371)
          ·
            refine ⟨237372055639824564575838557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158248037093216376383892371 237372055639824564575838557)
            ·
              refine ⟨89014520864934211715939459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237372055639824564575838557 89014520864934211715939459)
              ·
                refine ⟨133521781297401317573909189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89014520864934211715939459 133521781297401317573909189)
                ·
                  refine ⟨25035333993262747045107973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133521781297401317573909189 25035333993262747045107973)
                  ·
                    refine ⟨4694125123736765070957745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25035333993262747045107973 4694125123736765070957745)
                    ·
                      refine ⟨3520593842802573803218309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694125123736765070957745 3520593842802573803218309)
                      ·
                        rfl

theorem cell23_6856332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_6856332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856332 prefixEnd_6856332 := by exact prefixLift 6856332
  have htrace : WordTrace (prefixWord ++ tailWord_6856332) baseStart_6856332 baseEnd_6856332 := by
    simpa [prefixWord, tailWord_6856332, baseEnd_6856332] using wordTrace_append hprefix tailTrace_6856332
  have hstable : (prefixWord ++ tailWord_6856332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856332).length < 2 ^ (prefixWord ++ tailWord_6856332).sum := by decide
  have hdescent : baseEnd_6856332 < baseStart_6856332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856335 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 3]
def baseStart_6856335 : Nat := 118140960795 + 6856335 * 2 ^ 59
def prefixEnd_6856335 : Nat := 4983230072969 + 3 ^ 40 * 6856335 * 2
def baseEnd_6856335 : Nat := 3520595383244537291480795

theorem tailTrace_6856335 : CollatzResearch.WordTrace tailWord_6856335 prefixEnd_6856335 3520595383244537291480795 := by
  unfold tailWord_6856335
  simp only [CollatzResearch.WordTrace]
  refine ⟨250071081615676738637522459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166714054410451159091681639 250071081615676738637522459)
  ·
    refine ⟨375106622423515107956283689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250071081615676738637522459 375106622423515107956283689)
    ·
      refine ⟨281329966817636330967212767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375106622423515107956283689 281329966817636330967212767)
      ·
        refine ⟨421994950226454496450819151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281329966817636330967212767 421994950226454496450819151)
        ·
          refine ⟨632992425339681744676228727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421994950226454496450819151 632992425339681744676228727)
          ·
            refine ⟨949488638009522617014343091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632992425339681744676228727 949488638009522617014343091)
            ·
              refine ⟨1424232957014283925521514637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949488638009522617014343091 1424232957014283925521514637)
              ·
                refine ⟨534087358880356472070567989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1424232957014283925521514637 534087358880356472070567989)
                ·
                  refine ⟨50070689895033419256615749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 534087358880356472070567989 50070689895033419256615749)
                  ·
                    refine ⟨9388254355318766110615453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50070689895033419256615749 9388254355318766110615453)
                    ·
                      refine ⟨3520595383244537291480795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9388254355318766110615453 3520595383244537291480795)
                      ·
                        rfl

theorem cell23_6856335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 3].length) (baseStart_6856335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856335 prefixEnd_6856335 := by exact prefixLift 6856335
  have htrace : WordTrace (prefixWord ++ tailWord_6856335) baseStart_6856335 baseEnd_6856335 := by
    simpa [prefixWord, tailWord_6856335, baseEnd_6856335] using wordTrace_append hprefix tailTrace_6856335
  have hstable : (prefixWord ++ tailWord_6856335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856335).length < 2 ^ (prefixWord ++ tailWord_6856335).sum := by decide
  have hdescent : baseEnd_6856335 < baseStart_6856335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856352 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 3]
def baseStart_6856352 : Nat := 118140960795 + 6856352 * 2 ^ 59
def prefixEnd_6856352 : Nat := 4983230072969 + 3 ^ 40 * 6856352 * 2
def baseEnd_6856352 : Nat := 3520604112415663724968217

theorem tailTrace_6856352 : CollatzResearch.WordTrace tailWord_6856352 prefixEnd_6856352 3520604112415663724968217 := by
  unfold tailWord_6856352
  simp only [CollatzResearch.WordTrace]
  refine ⟨125035850828307575270445655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166714467771076767027260873 125035850828307575270445655)
  ·
    refine ⟨187553776242461362905668483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125035850828307575270445655 187553776242461362905668483)
    ·
      refine ⟨281330664363692044358502725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187553776242461362905668483 281330664363692044358502725)
      ·
        refine ⟨52749499568192258317219261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281330664363692044358502725 52749499568192258317219261)
        ·
          refine ⟨19781062338072096868957223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52749499568192258317219261 19781062338072096868957223)
          ·
            refine ⟨29671593507108145303435835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19781062338072096868957223 29671593507108145303435835)
            ·
              refine ⟨44507390260662217955153753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29671593507108145303435835 44507390260662217955153753)
              ·
                refine ⟨33380542695496663466365315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44507390260662217955153753 33380542695496663466365315)
                ·
                  refine ⟨50070814043244995199547973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33380542695496663466365315 50070814043244995199547973)
                  ·
                    refine ⟨9388277633108436599915245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50070814043244995199547973 9388277633108436599915245)
                    ·
                      refine ⟨3520604112415663724968217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9388277633108436599915245 3520604112415663724968217)
                      ·
                        rfl

theorem cell23_6856352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_6856352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856352 prefixEnd_6856352 := by exact prefixLift 6856352
  have htrace : WordTrace (prefixWord ++ tailWord_6856352) baseStart_6856352 baseEnd_6856352 := by
    simpa [prefixWord, tailWord_6856352, baseEnd_6856352] using wordTrace_append hprefix tailTrace_6856352
  have hstable : (prefixWord ++ tailWord_6856352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856352).length < 2 ^ (prefixWord ++ tailWord_6856352).sum := by decide
  have hdescent : baseEnd_6856352 < baseStart_6856352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856419 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 3, 5]
def baseStart_6856419 : Nat := 118140960795 + 6856419 * 2 ^ 59
def prefixEnd_6856419 : Nat := 4983230072969 + 3 ^ 40 * 6856419 * 2
def baseEnd_6856419 : Nat := 1173546171873171654276803

theorem tailTrace_6856419 : CollatzResearch.WordTrace tailWord_6856419 prefixEnd_6856419 1173546171873171654276803 := by
  unfold tailWord_6856419
  simp only [CollatzResearch.WordTrace]
  refine ⟨250074145347372420983580311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166716096898248280655720207 250074145347372420983580311)
  ·
    refine ⟨375111218021058631475370467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250074145347372420983580311 375111218021058631475370467)
    ·
      refine ⟨562666827031587947213055701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375111218021058631475370467 562666827031587947213055701)
      ·
        refine ⟨13187503758552842512805993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 562666827031587947213055701 13187503758552842512805993)
        ·
          refine ⟨9890627818914631884604495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13187503758552842512805993 9890627818914631884604495)
          ·
            refine ⟨14835941728371947826906743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9890627818914631884604495 14835941728371947826906743)
            ·
              refine ⟨22253912592557921740360115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14835941728371947826906743 22253912592557921740360115)
              ·
                refine ⟨33380868888836882610540173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22253912592557921740360115 33380868888836882610540173)
                ·
                  refine ⟨12517825833313830978952565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33380868888836882610540173 12517825833313830978952565)
                  ·
                    refine ⟨1173546171873171654276803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12517825833313830978952565 1173546171873171654276803)
                    ·
                      rfl

theorem cell23_6856419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 5].length) (baseStart_6856419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856419 prefixEnd_6856419 := by exact prefixLift 6856419
  have htrace : WordTrace (prefixWord ++ tailWord_6856419) baseStart_6856419 baseEnd_6856419 := by
    simpa [prefixWord, tailWord_6856419, baseEnd_6856419] using wordTrace_append hprefix tailTrace_6856419
  have hstable : (prefixWord ++ tailWord_6856419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856419).length < 2 ^ (prefixWord ++ tailWord_6856419).sum := by decide
  have hdescent : baseEnd_6856419 < baseStart_6856419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856432 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 4, 4]
def baseStart_6856432 : Nat := 118140960795 + 6856432 * 2 ^ 59
def prefixEnd_6856432 : Nat := 4983230072969 + 3 ^ 40 * 6856432 * 2
def baseEnd_6856432 : Nat := 1173548396956007803989283

theorem tailTrace_6856432 : CollatzResearch.WordTrace tailWord_6856432 prefixEnd_6856432 1173548396956007803989283 := by
  unfold tailWord_6856432
  simp only [CollatzResearch.WordTrace]
  refine ⟨125037309748162662101901775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166716412997550216135869033 125037309748162662101901775)
  ·
    refine ⟨187555964622243993152852663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125037309748162662101901775 187555964622243993152852663)
    ·
      refine ⟨281333946933365989729278995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187555964622243993152852663 281333946933365989729278995)
      ·
        refine ⟨422000920400048984593918493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281333946933365989729278995 422000920400048984593918493)
        ·
          refine ⟨158250345150018369222719435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422000920400048984593918493 158250345150018369222719435)
          ·
            refine ⟨237375517725027553834079153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158250345150018369222719435 237375517725027553834079153)
            ·
              refine ⟨178031638293770665375559365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237375517725027553834079153 178031638293770665375559365)
              ·
                refine ⟨33380932180081999757917381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178031638293770665375559365 33380932180081999757917381)
                ·
                  refine ⟨6258924783765374954609509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33380932180081999757917381 6258924783765374954609509)
                  ·
                    refine ⟨1173548396956007803989283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6258924783765374954609509 1173548396956007803989283)
                    ·
                      rfl

theorem cell23_6856432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4, 4].length) (baseStart_6856432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856432 prefixEnd_6856432 := by exact prefixLift 6856432
  have htrace : WordTrace (prefixWord ++ tailWord_6856432) baseStart_6856432 baseEnd_6856432 := by
    simpa [prefixWord, tailWord_6856432, baseEnd_6856432] using wordTrace_append hprefix tailTrace_6856432
  have hstable : (prefixWord ++ tailWord_6856432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856432).length < 2 ^ (prefixWord ++ tailWord_6856432).sum := by decide
  have hdescent : baseEnd_6856432 < baseStart_6856432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856449 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 2, 4]
def baseStart_6856449 : Nat := 118140960795 + 6856449 * 2 ^ 59
def prefixEnd_6856449 : Nat := 4983230072969 + 3 ^ 40 * 6856449 * 2
def baseEnd_6856449 : Nat := 1173551306679716615151757

theorem tailTrace_6856449 : CollatzResearch.WordTrace tailWord_6856449 prefixEnd_6856449 1173551306679716615151757 := by
  unfold tailWord_6856449
  simp only [CollatzResearch.WordTrace]
  refine ⟨250075239537263736107172401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166716826358175824071448267 250075239537263736107172401)
  ·
    refine ⟨187556429652947802080379301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250075239537263736107172401 187556429652947802080379301)
    ·
      refine ⟨35166830559927712890071119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187556429652947802080379301 35166830559927712890071119)
      ·
        refine ⟨52750245839891569335106679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35166830559927712890071119 52750245839891569335106679)
        ·
          refine ⟨79125368759837354002660019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52750245839891569335106679 79125368759837354002660019)
          ·
            refine ⟨118688053139756031003990029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79125368759837354002660019 118688053139756031003990029)
            ·
              refine ⟨44508019927408511626496261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118688053139756031003990029 44508019927408511626496261)
              ·
                refine ⟨8345253736389095929968049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44508019927408511626496261 8345253736389095929968049)
                ·
                  refine ⟨6258940302291821947476037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8345253736389095929968049 6258940302291821947476037)
                  ·
                    refine ⟨1173551306679716615151757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6258940302291821947476037 1173551306679716615151757)
                    ·
                      rfl

theorem cell23_6856449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_6856449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856449 prefixEnd_6856449 := by exact prefixLift 6856449
  have htrace : WordTrace (prefixWord ++ tailWord_6856449) baseStart_6856449 baseEnd_6856449 := by
    simpa [prefixWord, tailWord_6856449, baseEnd_6856449] using wordTrace_append hprefix tailTrace_6856449
  have hstable : (prefixWord ++ tailWord_6856449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856449).length < 2 ^ (prefixWord ++ tailWord_6856449).sum := by decide
  have hdescent : baseEnd_6856449 < baseStart_6856449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856456 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 3, 2, 2]
def baseStart_6856456 : Nat := 118140960795 + 6856456 * 2 ^ 59
def prefixEnd_6856456 : Nat := 4983230072969 + 3 ^ 40 * 6856456 * 2
def baseEnd_6856456 : Nat := 3520657514403731318067739

theorem tailTrace_6856456 : CollatzResearch.WordTrace tailWord_6856456 prefixEnd_6856456 3520657514403731318067739 := by
  unfold tailWord_6856456
  simp only [CollatzResearch.WordTrace]
  refine ⟨125037747424119188151338611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166716996565492250868451481 125037747424119188151338611)
  ·
    refine ⟨187556621136178782227007917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125037747424119188151338611 187556621136178782227007917)
    ·
      refine ⟨70333732926067043335127969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187556621136178782227007917 70333732926067043335127969)
      ·
        refine ⟨52750299694550282501345977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70333732926067043335127969 52750299694550282501345977)
        ·
          refine ⟨39562724770912711876009483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52750299694550282501345977 39562724770912711876009483)
          ·
            refine ⟨59344087156369067814014225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39562724770912711876009483 59344087156369067814014225)
            ·
              refine ⟨44508065367276800860510669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59344087156369067814014225 44508065367276800860510669)
              ·
                refine ⟨16690524512728800322691501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44508065367276800860510669 16690524512728800322691501)
                ·
                  refine ⟨6258946692273300121009313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16690524512728800322691501 6258946692273300121009313)
                  ·
                    refine ⟨4694210019204975090756985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6258946692273300121009313 4694210019204975090756985)
                    ·
                      refine ⟨3520657514403731318067739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694210019204975090756985 3520657514403731318067739)
                      ·
                        rfl

theorem cell23_6856456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_6856456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856456 prefixEnd_6856456 := by exact prefixLift 6856456
  have htrace : WordTrace (prefixWord ++ tailWord_6856456) baseStart_6856456 baseEnd_6856456 := by
    simpa [prefixWord, tailWord_6856456, baseEnd_6856456] using wordTrace_append hprefix tailTrace_6856456
  have hstable : (prefixWord ++ tailWord_6856456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856456).length < 2 ^ (prefixWord ++ tailWord_6856456).sum := by decide
  have hdescent : baseEnd_6856456 < baseStart_6856456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856462 : List Nat := [4, 1, 1, 2, 1, 1, 5, 8]
def baseStart_6856462 : Nat := 118140960795 + 6856462 * 2 ^ 59
def prefixEnd_6856462 : Nat := 4983230072969 + 3 ^ 40 * 6856462 * 2
def baseEnd_6856462 : Nat := 130394836862505862762693

theorem tailTrace_6856462 : CollatzResearch.WordTrace tailWord_6856462 prefixEnd_6856462 130394836862505862762693 := by
  unfold tailWord_6856462
  simp only [CollatzResearch.WordTrace]
  refine ⟨31259464210777079915924455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166717142457477759551597093 31259464210777079915924455)
  ·
    refine ⟨46889196316165619873886683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31259464210777079915924455 46889196316165619873886683)
    ·
      refine ⟨70333794474248429810830025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46889196316165619873886683 70333794474248429810830025)
      ·
        refine ⟨52750345855686322358122519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70333794474248429810830025 52750345855686322358122519)
        ·
          refine ⟨79125518783529483537183779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52750345855686322358122519 79125518783529483537183779)
          ·
            refine ⟨118688278175294225305775669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79125518783529483537183779 118688278175294225305775669)
            ·
              refine ⟨11127026078933833622416469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118688278175294225305775669 11127026078933833622416469)
              ·
                refine ⟨130394836862505862762693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11127026078933833622416469 130394836862505862762693)
                ·
                  rfl

theorem cell23_6856462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_6856462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856462 prefixEnd_6856462 := by exact prefixLift 6856462
  have htrace : WordTrace (prefixWord ++ tailWord_6856462) baseStart_6856462 baseEnd_6856462 := by
    simpa [prefixWord, tailWord_6856462, baseEnd_6856462] using wordTrace_append hprefix tailTrace_6856462
  have hstable : (prefixWord ++ tailWord_6856462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856462).length < 2 ^ (prefixWord ++ tailWord_6856462).sum := by decide
  have hdescent : baseEnd_6856462 < baseStart_6856462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856466 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_6856466 : Nat := 118140960795 + 6856466 * 2 ^ 59
def prefixEnd_6856466 : Nat := 4983230072969 + 3 ^ 40 * 6856466 * 2
def baseEnd_6856466 : Nat := 1173554216403425426314231

theorem tailTrace_6856466 : CollatzResearch.WordTrace tailWord_6856466 prefixEnd_6856466 1173554216403425426314231 := by
  unfold tailWord_6856466
  simp only [CollatzResearch.WordTrace]
  refine ⟨62518964894550537002635313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166717239718801432007027501 62518964894550537002635313)
  ·
    refine ⟨46889223670912902751976485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62518964894550537002635313 46889223670912902751976485)
    ·
      refine ⟨8791729438296169265995591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46889223670912902751976485 8791729438296169265995591)
      ·
        refine ⟨13187594157444253898993387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8791729438296169265995591 13187594157444253898993387)
        ·
          refine ⟨19781391236166380848490081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13187594157444253898993387 19781391236166380848490081)
          ·
            refine ⟨14836043427124785636367561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19781391236166380848490081 14836043427124785636367561)
            ·
              refine ⟨11127032570343589227275671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14836043427124785636367561 11127032570343589227275671)
              ·
                refine ⟨16690548855515383840913507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11127032570343589227275671 16690548855515383840913507)
                ·
                  refine ⟨25035823283273075761370261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16690548855515383840913507 25035823283273075761370261)
                  ·
                    refine ⟨1173554216403425426314231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25035823283273075761370261 1173554216403425426314231)
                    ·
                      rfl

theorem cell23_6856466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_6856466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856466 prefixEnd_6856466 := by exact prefixLift 6856466
  have htrace : WordTrace (prefixWord ++ tailWord_6856466) baseStart_6856466 baseEnd_6856466 := by
    simpa [prefixWord, tailWord_6856466, baseEnd_6856466] using wordTrace_append hprefix tailTrace_6856466
  have hstable : (prefixWord ++ tailWord_6856466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856466).length < 2 ^ (prefixWord ++ tailWord_6856466).sum := by decide
  have hdescent : baseEnd_6856466 < baseStart_6856466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856469 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_6856469 : Nat := 118140960795 + 6856469 * 2 ^ 59
def prefixEnd_6856469 : Nat := 4983230072969 + 3 ^ 40 * 6856469 * 2
def baseEnd_6856469 : Nat := 3520664189652239767205179

theorem tailTrace_6856469 : CollatzResearch.WordTrace tailWord_6856469 prefixEnd_6856469 3520664189652239767205179 := by
  unfold tailWord_6856469
  simp only [CollatzResearch.WordTrace]
  refine ⟨250075968997191279522900461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166717312664794186348600307 250075968997191279522900461)
  ·
    refine ⟨93778488373946729821087673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250075968997191279522900461 93778488373946729821087673)
    ·
      refine ⟨70333866280460047365815755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93778488373946729821087673 70333866280460047365815755)
      ·
        refine ⟨105500799420690071048723633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70333866280460047365815755 105500799420690071048723633)
        ·
          refine ⟨79125599565517553286542725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105500799420690071048723633 79125599565517553286542725)
          ·
            refine ⟨14836049918534541241226761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79125599565517553286542725 14836049918534541241226761)
            ·
              refine ⟨11127037438900905930920071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14836049918534541241226761 11127037438900905930920071)
              ·
                refine ⟨16690556158351358896380107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11127037438900905930920071 16690556158351358896380107)
                ·
                  refine ⟨25035834237527038344570161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16690556158351358896380107 25035834237527038344570161)
                  ·
                    refine ⟨18776875678145278758427621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25035834237527038344570161 18776875678145278758427621)
                    ·
                      refine ⟨3520664189652239767205179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18776875678145278758427621 3520664189652239767205179)
                      ·
                        rfl

theorem cell23_6856469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_6856469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856469 prefixEnd_6856469 := by exact prefixLift 6856469
  have htrace : WordTrace (prefixWord ++ tailWord_6856469) baseStart_6856469 baseEnd_6856469 := by
    simpa [prefixWord, tailWord_6856469, baseEnd_6856469] using wordTrace_append hprefix tailTrace_6856469
  have hstable : (prefixWord ++ tailWord_6856469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856469).length < 2 ^ (prefixWord ++ tailWord_6856469).sum := by decide
  have hdescent : baseEnd_6856469 < baseStart_6856469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856506 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3]
def baseStart_6856506 : Nat := 118140960795 + 6856506 * 2 ^ 59
def prefixEnd_6856506 : Nat := 4983230072969 + 3 ^ 40 * 6856506 * 2
def baseEnd_6856506 : Nat := 3520683188436456122442509

theorem tailTrace_6856506 : CollatzResearch.WordTrace tailWord_6856506 prefixEnd_6856506 3520683188436456122442509 := by
  unfold tailWord_6856506
  simp only [CollatzResearch.WordTrace]
  refine ⟨62519329624514308710499343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166718212332038156561331581 62519329624514308710499343)
  ·
    refine ⟨93778994436771463065749015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62519329624514308710499343 93778994436771463065749015)
    ·
      refine ⟨140668491655157194598623523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93778994436771463065749015 140668491655157194598623523)
      ·
        refine ⟨211002737482735791897935285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140668491655157194598623523 211002737482735791897935285)
        ·
          refine ⟨19781506639006480490431433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211002737482735791897935285 19781506639006480490431433)
          ·
            refine ⟨14836129979254860367823575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19781506639006480490431433 14836129979254860367823575)
            ·
              refine ⟨22254194968882290551735363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14836129979254860367823575 22254194968882290551735363)
              ·
                refine ⟨33381292453323435827603045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22254194968882290551735363 33381292453323435827603045)
                ·
                  refine ⟨6258992334998144217675571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33381292453323435827603045 6258992334998144217675571)
                  ·
                    refine ⟨9388488502497216326513357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6258992334998144217675571 9388488502497216326513357)
                    ·
                      refine ⟨3520683188436456122442509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9388488502497216326513357 3520683188436456122442509)
                      ·
                        rfl

theorem cell23_6856506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_6856506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856506 prefixEnd_6856506 := by exact prefixLift 6856506
  have htrace : WordTrace (prefixWord ++ tailWord_6856506) baseStart_6856506 baseEnd_6856506 := by
    simpa [prefixWord, tailWord_6856506, baseEnd_6856506] using wordTrace_append hprefix tailTrace_6856506
  have hstable : (prefixWord ++ tailWord_6856506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856506).length < 2 ^ (prefixWord ++ tailWord_6856506).sum := by decide
  have hdescent : baseEnd_6856506 < baseStart_6856506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856522 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_6856522 : Nat := 118140960795 + 6856522 * 2 ^ 59
def prefixEnd_6856522 : Nat := 4983230072969 + 3 ^ 40 * 6856522 * 2
def baseEnd_6856522 : Nat := 1173563801375642686614145

theorem tailTrace_6856522 : CollatzResearch.WordTrace tailWord_6856522 prefixEnd_6856522 1173563801375642686614145 := by
  unfold tailWord_6856522
  simp only [CollatzResearch.WordTrace]
  refine ⟨62519475516499817393644955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166718601377332846383053213 62519475516499817393644955)
  ·
    refine ⟨93779213274749726090467433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62519475516499817393644955 93779213274749726090467433)
    ·
      refine ⟨70334409956062294567850575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93779213274749726090467433 70334409956062294567850575)
      ·
        refine ⟨105501614934093441851775863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70334409956062294567850575 105501614934093441851775863)
        ·
          refine ⟨158252422401140162777663795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105501614934093441851775863 158252422401140162777663795)
          ·
            refine ⟨237378633601710244166495693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158252422401140162777663795 237378633601710244166495693)
            ·
              refine ⟨89016987600641341562435885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237378633601710244166495693 89016987600641341562435885)
              ·
                refine ⟨33381370350240503085913457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89016987600641341562435885 33381370350240503085913457)
                ·
                  refine ⟨25036027762680377314435093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33381370350240503085913457 25036027762680377314435093)
                  ·
                    refine ⟨1173563801375642686614145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25036027762680377314435093 1173563801375642686614145)
                    ·
                      rfl

theorem cell23_6856522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_6856522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856522 prefixEnd_6856522 := by exact prefixLift 6856522
  have htrace : WordTrace (prefixWord ++ tailWord_6856522) baseStart_6856522 baseEnd_6856522 := by
    simpa [prefixWord, tailWord_6856522, baseEnd_6856522] using wordTrace_append hprefix tailTrace_6856522
  have hstable : (prefixWord ++ tailWord_6856522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856522).length < 2 ^ (prefixWord ++ tailWord_6856522).sum := by decide
  have hdescent : baseEnd_6856522 < baseStart_6856522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856533 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 1, 3, 2]
def baseStart_6856533 : Nat := 118140960795 + 6856533 * 2 ^ 59
def prefixEnd_6856533 : Nat := 4983230072969 + 3 ^ 40 * 6856533 * 2
def baseEnd_6856533 : Nat := 3520697052414127516804885

theorem tailTrace_6856533 : CollatzResearch.WordTrace tailWord_6856533 prefixEnd_6856533 3520697052414127516804885 := by
  unfold tailWord_6856533
  simp only [CollatzResearch.WordTrace]
  refine ⟨250078303268959418453230253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166718868845972945635486835 250078303268959418453230253)
  ·
    refine ⟨93779363725859781919961345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250078303268959418453230253 93779363725859781919961345)
    ·
      refine ⟨70334522794394836439971009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93779363725859781919961345 70334522794394836439971009)
      ·
        refine ⟨52750892095796127329978257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70334522794394836439971009 52750892095796127329978257)
        ·
          refine ⟨39563169071847095497483693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52750892095796127329978257 39563169071847095497483693)
          ·
            refine ⟨14836188401942660811556385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39563169071847095497483693 14836188401942660811556385)
            ·
              refine ⟨11127141301456995608667289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14836188401942660811556385 11127141301456995608667289)
              ·
                refine ⟨8345355976092746706500467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11127141301456995608667289 8345355976092746706500467)
                ·
                  refine ⟨12518033964139120059750701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8345355976092746706500467 12518033964139120059750701)
                  ·
                    refine ⟨4694262736552170022406513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12518033964139120059750701 4694262736552170022406513)
                    ·
                      refine ⟨3520697052414127516804885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694262736552170022406513 3520697052414127516804885)
                      ·
                        rfl

theorem cell23_6856533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_6856533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856533 prefixEnd_6856533 := by exact prefixLift 6856533
  have htrace : WordTrace (prefixWord ++ tailWord_6856533) baseStart_6856533 baseEnd_6856533 := by
    simpa [prefixWord, tailWord_6856533, baseEnd_6856533] using wordTrace_append hprefix tailTrace_6856533
  have hstable : (prefixWord ++ tailWord_6856533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856533).length < 2 ^ (prefixWord ++ tailWord_6856533).sum := by decide
  have hdescent : baseEnd_6856533 < baseStart_6856533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856562 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_6856562 : Nat := 118140960795 + 6856562 * 2 ^ 59
def prefixEnd_6856562 : Nat := 4983230072969 + 3 ^ 40 * 6856562 * 2
def baseEnd_6856562 : Nat := 3520711943353107903342251

theorem tailTrace_6856562 : CollatzResearch.WordTrace tailWord_6856562 prefixEnd_6856562 3520711943353107903342251 := by
  unfold tailWord_6856562
  simp only [CollatzResearch.WordTrace]
  refine ⟨62519840246463589101508985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166719573990569570937357293 62519840246463589101508985)
  ·
    refine ⟨46889880184847691826131739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62519840246463589101508985 46889880184847691826131739)
    ·
      refine ⟨70334820277271537739197609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46889880184847691826131739 70334820277271537739197609)
      ·
        refine ⟨52751115207953653304398207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70334820277271537739197609 52751115207953653304398207)
        ·
          refine ⟨79126672811930479956597311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52751115207953653304398207 79126672811930479956597311)
          ·
            refine ⟨118690009217895719934895967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79126672811930479956597311 118690009217895719934895967)
            ·
              refine ⟨178035013826843579902343951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118690009217895719934895967 178035013826843579902343951)
              ·
                refine ⟨267052520740265369853515927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178035013826843579902343951 267052520740265369853515927)
                ·
                  refine ⟨400578781110398054780273891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267052520740265369853515927 400578781110398054780273891)
                  ·
                    refine ⟨600868171665597082170410837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 400578781110398054780273891 600868171665597082170410837)
                    ·
                      refine ⟨3520711943353107903342251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 600868171665597082170410837 3520711943353107903342251)
                      ·
                        rfl

theorem cell23_6856562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_6856562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856562 prefixEnd_6856562 := by exact prefixLift 6856562
  have htrace : WordTrace (prefixWord ++ tailWord_6856562) baseStart_6856562 baseEnd_6856562 := by
    simpa [prefixWord, tailWord_6856562, baseEnd_6856562] using wordTrace_append hprefix tailTrace_6856562
  have hstable : (prefixWord ++ tailWord_6856562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856562).length < 2 ^ (prefixWord ++ tailWord_6856562).sum := by decide
  have hdescent : baseEnd_6856562 < baseStart_6856562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856580 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_6856580 : Nat := 118140960795 + 6856580 * 2 ^ 59
def prefixEnd_6856580 : Nat := 4983230072969 + 3 ^ 40 * 6856580 * 2
def baseEnd_6856580 : Nat := 3520721186004888832917169

theorem tailTrace_6856580 : CollatzResearch.WordTrace tailWord_6856580 prefixEnd_6856580 3520721186004888832917169 := by
  unfold tailWord_6856580
  simp only [CollatzResearch.WordTrace]
  refine ⟨125040008749894572740095597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166720011666526096986794129 125040008749894572740095597)
  ·
    refine ⟨46890003281210464777535849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125040008749894572740095597 46890003281210464777535849)
    ·
      refine ⟨35167502460907848583151887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46890003281210464777535849 35167502460907848583151887)
      ·
        refine ⟨52751253691361772874727831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35167502460907848583151887 52751253691361772874727831)
        ·
          refine ⟨79126880537042659312091747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52751253691361772874727831 79126880537042659312091747)
          ·
            refine ⟨118690320805563988968137621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79126880537042659312091747 118690320805563988968137621)
            ·
              refine ⟨5563608787760811982881451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118690320805563988968137621 5563608787760811982881451)
              ·
                refine ⟨8345413181641217974322177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5563608787760811982881451 8345413181641217974322177)
                ·
                  refine ⟨6259059886230913480741633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8345413181641217974322177 6259059886230913480741633)
                  ·
                    refine ⟨4694294914673185110556225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6259059886230913480741633 4694294914673185110556225)
                    ·
                      refine ⟨3520721186004888832917169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694294914673185110556225 3520721186004888832917169)
                      ·
                        rfl

theorem cell23_6856580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_6856580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856580 prefixEnd_6856580 := by exact prefixLift 6856580
  have htrace : WordTrace (prefixWord ++ tailWord_6856580) baseStart_6856580 baseEnd_6856580 := by
    simpa [prefixWord, tailWord_6856580, baseEnd_6856580] using wordTrace_append hprefix tailTrace_6856580
  have hstable : (prefixWord ++ tailWord_6856580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856580).length < 2 ^ (prefixWord ++ tailWord_6856580).sum := by decide
  have hdescent : baseEnd_6856580 < baseStart_6856580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856592 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_6856592 : Nat := 118140960795 + 6856592 * 2 ^ 59
def prefixEnd_6856592 : Nat := 4983230072969 + 3 ^ 40 * 6856592 * 2
def baseEnd_6856592 : Nat := 3520727347772742785967113

theorem tailTrace_6856592 : CollatzResearch.WordTrace tailWord_6856592 prefixEnd_6856592 3520727347772742785967113 := by
  unfold tailWord_6856592
  simp only [CollatzResearch.WordTrace]
  refine ⟨125040227587872835764814015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166720303450497114353085353 125040227587872835764814015)
  ·
    refine ⟨187560341381809253647221023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125040227587872835764814015 187560341381809253647221023)
    ·
      refine ⟨281340512072713880470831535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187560341381809253647221023 281340512072713880470831535)
      ·
        refine ⟨422010768109070820706247303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281340512072713880470831535 422010768109070820706247303)
        ·
          refine ⟨633016152163606231059370955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422010768109070820706247303 633016152163606231059370955)
          ·
            refine ⟨949524228245409346589056433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633016152163606231059370955 949524228245409346589056433)
            ·
              refine ⟨712143171184057009941792325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949524228245409346589056433 712143171184057009941792325)
              ·
                refine ⟨133526844597010689364086061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712143171184057009941792325 133526844597010689364086061)
                ·
                  refine ⟨50072566723879008511532273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133526844597010689364086061 50072566723879008511532273)
                  ·
                    refine ⟨37554425042909256383649205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50072566723879008511532273 37554425042909256383649205)
                    ·
                      refine ⟨3520727347772742785967113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37554425042909256383649205 3520727347772742785967113)
                      ·
                        rfl

theorem cell23_6856592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_6856592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856592 prefixEnd_6856592 := by exact prefixLift 6856592
  have htrace : WordTrace (prefixWord ++ tailWord_6856592) baseStart_6856592 baseEnd_6856592 := by
    simpa [prefixWord, tailWord_6856592, baseEnd_6856592] using wordTrace_append hprefix tailTrace_6856592
  have hstable : (prefixWord ++ tailWord_6856592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856592).length < 2 ^ (prefixWord ++ tailWord_6856592).sum := by decide
  have hdescent : baseEnd_6856592 < baseStart_6856592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856599 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 2, 5]
def baseStart_6856599 : Nat := 118140960795 + 6856599 * 2 ^ 59
def prefixEnd_6856599 : Nat := 4983230072969 + 3 ^ 40 * 6856599 * 2
def baseEnd_6856599 : Nat := 1173576980712441419526527

theorem tailTrace_6856599 : CollatzResearch.WordTrace tailWord_6856599 prefixEnd_6856599 1173576980712441419526527 := by
  unfold tailWord_6856599
  simp only [CollatzResearch.WordTrace]
  refine ⟨250080710486720311725132851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166720473657813541150088567 250080710486720311725132851)
  ·
    refine ⟨375121065730080467587699277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250080710486720311725132851 375121065730080467587699277)
    ·
      refine ⟨140670399648780175345387229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375121065730080467587699277 140670399648780175345387229)
      ·
        refine ⟨52751399868292565754520211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140670399648780175345387229 52751399868292565754520211)
        ·
          refine ⟨79127099802438848631780317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52751399868292565754520211 79127099802438848631780317)
          ·
            refine ⟨29672662425914568236917619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79127099802438848631780317 29672662425914568236917619)
            ·
              refine ⟨44508993638871852355376429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29672662425914568236917619 44508993638871852355376429)
              ·
                refine ⟨16690872614576944633266161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44508993638871852355376429 16690872614576944633266161)
                ·
                  refine ⟨12518154460932708474949621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16690872614576944633266161 12518154460932708474949621)
                  ·
                    refine ⟨1173576980712441419526527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12518154460932708474949621 1173576980712441419526527)
                    ·
                      rfl

theorem cell23_6856599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_6856599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856599 prefixEnd_6856599 := by exact prefixLift 6856599
  have htrace : WordTrace (prefixWord ++ tailWord_6856599) baseStart_6856599 baseEnd_6856599 := by
    simpa [prefixWord, tailWord_6856599, baseEnd_6856599] using wordTrace_append hprefix tailTrace_6856599
  have hstable : (prefixWord ++ tailWord_6856599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856599).length < 2 ^ (prefixWord ++ tailWord_6856599).sum := by decide
  have hdescent : baseEnd_6856599 < baseStart_6856599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856639 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 3]
def baseStart_6856639 : Nat := 118140960795 + 6856639 * 2 ^ 59
def prefixEnd_6856639 : Nat := 4983230072969 + 3 ^ 40 * 6856639 * 2
def baseEnd_6856639 : Nat := 3520751481363504102079397

theorem tailTrace_6856639 : CollatzResearch.WordTrace tailWord_6856639 prefixEnd_6856639 3520751481363504102079397 := by
  unfold tailWord_6856639
  simp only [CollatzResearch.WordTrace]
  refine ⟨250082169406575398556588971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166721446271050265704392647 250082169406575398556588971)
  ·
    refine ⟨375123254109863097834883457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250082169406575398556588971 375123254109863097834883457)
    ·
      refine ⟨281342440582397323376162593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375123254109863097834883457 281342440582397323376162593)
      ·
        refine ⟨211006830436797992532121945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281342440582397323376162593 211006830436797992532121945)
        ·
          refine ⟨158255122827598494399091459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211006830436797992532121945 158255122827598494399091459)
          ·
            refine ⟨237382684241397741598637189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158255122827598494399091459 237382684241397741598637189)
            ·
              refine ⟨44509253295262076549744473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237382684241397741598637189 44509253295262076549744473)
              ·
                refine ⟨33381939971446557412308355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44509253295262076549744473 33381939971446557412308355)
                ·
                  refine ⟨50072909957169836118462533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33381939971446557412308355 50072909957169836118462533)
                  ·
                    refine ⟨9388670616969344272211725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50072909957169836118462533 9388670616969344272211725)
                    ·
                      refine ⟨3520751481363504102079397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9388670616969344272211725 3520751481363504102079397)
                      ·
                        rfl

theorem cell23_6856639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_6856639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856639 prefixEnd_6856639 := by exact prefixLift 6856639
  have htrace : WordTrace (prefixWord ++ tailWord_6856639) baseStart_6856639 baseEnd_6856639 := by
    simpa [prefixWord, tailWord_6856639, baseEnd_6856639] using wordTrace_append hprefix tailTrace_6856639
  have hstable : (prefixWord ++ tailWord_6856639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856639).length < 2 ^ (prefixWord ++ tailWord_6856639).sum := by decide
  have hdescent : baseEnd_6856639 < baseStart_6856639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856656 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 3]
def baseStart_6856656 : Nat := 118140960795 + 6856656 * 2 ^ 59
def prefixEnd_6856656 : Nat := 4983230072969 + 3 ^ 40 * 6856656 * 2
def baseEnd_6856656 : Nat := 3520760210534630535566819

theorem tailTrace_6856656 : CollatzResearch.WordTrace tailWord_6856656 prefixEnd_6856656 3520760210534630535566819 := by
  unfold tailWord_6856656
  simp only [CollatzResearch.WordTrace]
  refine ⟨125041394723756905229978911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166721859631675873639971881 125041394723756905229978911)
  ·
    refine ⟨187562092085635357844968367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125041394723756905229978911 187562092085635357844968367)
    ·
      refine ⟨281343138128453036767452551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187562092085635357844968367 281343138128453036767452551)
      ·
        refine ⟨422014707192679555151178827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281343138128453036767452551 422014707192679555151178827)
        ·
          refine ⟨633022060789019332726768241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422014707192679555151178827 633022060789019332726768241)
          ·
            refine ⟨474766545591764499545076181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633022060789019332726768241 474766545591764499545076181)
            ·
              refine ⟨11127340912306980458087723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 474766545591764499545076181 11127340912306980458087723)
              ·
                refine ⟨16691011368460470687131585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11127340912306980458087723 16691011368460470687131585)
                ·
                  refine ⟨12518258526345353015348689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16691011368460470687131585 12518258526345353015348689)
                  ·
                    refine ⟨9388693894759014761511517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12518258526345353015348689 9388693894759014761511517)
                    ·
                      refine ⟨3520760210534630535566819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9388693894759014761511517 3520760210534630535566819)
                      ·
                        rfl

theorem cell23_6856656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 3].length) (baseStart_6856656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856656 prefixEnd_6856656 := by exact prefixLift 6856656
  have htrace : WordTrace (prefixWord ++ tailWord_6856656) baseStart_6856656 baseEnd_6856656 := by
    simpa [prefixWord, tailWord_6856656, baseEnd_6856656] using wordTrace_append hprefix tailTrace_6856656
  have hstable : (prefixWord ++ tailWord_6856656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856656).length < 2 ^ (prefixWord ++ tailWord_6856656).sum := by decide
  have hdescent : baseEnd_6856656 < baseStart_6856656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856663 : List Nat := [1, 1, 3, 2, 1, 1, 6, 3, 1, 4]
def baseStart_6856663 : Nat := 118140960795 + 6856663 * 2 ^ 59
def prefixEnd_6856663 : Nat := 4983230072969 + 3 ^ 40 * 6856663 * 2
def baseEnd_6856663 : Nat := 1173587934966404002726429

theorem tailTrace_6856663 : CollatzResearch.WordTrace tailWord_6856663 prefixEnd_6856663 1173587934966404002726429 := by
  unfold tailWord_6856663
  simp only [CollatzResearch.WordTrace]
  refine ⟨250083044758488450655462643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166722029838992300436975095 250083044758488450655462643)
  ·
    refine ⟨375124567137732675983193965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250083044758488450655462643 375124567137732675983193965)
    ·
      refine ⟨140671712676649753493697737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375124567137732675983193965 140671712676649753493697737)
      ·
        refine ⟨105503784507487315120273303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140671712676649753493697737 105503784507487315120273303)
        ·
          refine ⟨158255676761230972680409955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105503784507487315120273303 158255676761230972680409955)
          ·
            refine ⟨237383515141846459020614933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158255676761230972680409955 237383515141846459020614933)
            ·
              refine ⟨11127352272274052766591325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237383515141846459020614933 11127352272274052766591325)
              ·
                refine ⟨4172757102102769787471747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11127352272274052766591325 4172757102102769787471747)
                ·
                  refine ⟨6259135653154154681207621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172757102102769787471747 6259135653154154681207621)
                  ·
                    refine ⟨1173587934966404002726429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6259135653154154681207621 1173587934966404002726429)
                    ·
                      rfl

theorem cell23_6856663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_6856663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856663 prefixEnd_6856663 := by exact prefixLift 6856663
  have htrace : WordTrace (prefixWord ++ tailWord_6856663) baseStart_6856663 baseEnd_6856663 := by
    simpa [prefixWord, tailWord_6856663, baseEnd_6856663] using wordTrace_append hprefix tailTrace_6856663
  have hstable : (prefixWord ++ tailWord_6856663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856663).length < 2 ^ (prefixWord ++ tailWord_6856663).sum := by decide
  have hdescent : baseEnd_6856663 < baseStart_6856663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856696 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 1, 5, 2]
def baseStart_6856696 : Nat := 118140960795 + 6856696 * 2 ^ 59
def prefixEnd_6856696 : Nat := 4983230072969 + 3 ^ 40 * 6856696 * 2
def baseEnd_6856696 : Nat := 3520780749760810379066635

theorem tailTrace_6856696 : CollatzResearch.WordTrace tailWord_6856696 prefixEnd_6856696 3520780749760810379066635 := by
  unfold tailWord_6856696
  simp only [CollatzResearch.WordTrace]
  refine ⟨125042124183684448645706971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166722832244912598194275961 125042124183684448645706971)
  ·
    refine ⟨187563186275526672968560457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125042124183684448645706971 187563186275526672968560457)
    ·
      refine ⟨140672389706645004726420343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187563186275526672968560457 140672389706645004726420343)
      ·
        refine ⟨211008584559967507089630515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140672389706645004726420343 211008584559967507089630515)
        ·
          refine ⟨316512876839951260634445773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211008584559967507089630515 316512876839951260634445773)
          ·
            refine ⟨118692328814981722737917165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316512876839951260634445773 118692328814981722737917165)
            ·
              refine ⟨44509623305618146026718937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118692328814981722737917165 44509623305618146026718937)
              ·
                refine ⟨33382217479213609520039203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44509623305618146026718937 33382217479213609520039203)
                ·
                  refine ⟨50073326218820414280058805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33382217479213609520039203 50073326218820414280058805)
                  ·
                    refine ⟨4694374333014413838755513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50073326218820414280058805 4694374333014413838755513)
                    ·
                      refine ⟨3520780749760810379066635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694374333014413838755513 3520780749760810379066635)
                      ·
                        rfl

theorem cell23_6856696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 5, 2].length) (baseStart_6856696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856696 prefixEnd_6856696 := by exact prefixLift 6856696
  have htrace : WordTrace (prefixWord ++ tailWord_6856696) baseStart_6856696 baseEnd_6856696 := by
    simpa [prefixWord, tailWord_6856696, baseEnd_6856696] using wordTrace_append hprefix tailTrace_6856696
  have hstable : (prefixWord ++ tailWord_6856696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856696).length < 2 ^ (prefixWord ++ tailWord_6856696).sum := by decide
  have hdescent : baseEnd_6856696 < baseStart_6856696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856737 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 3, 1, 3]
def baseStart_6856737 : Nat := 118140960795 + 6856737 * 2 ^ 59
def prefixEnd_6856737 : Nat := 4983230072969 + 3 ^ 40 * 6856737 * 2
def baseEnd_6856737 : Nat := 3520801802467644718653947

theorem tailTrace_6856737 : CollatzResearch.WordTrace tailWord_6856737 prefixEnd_6856737 3520801802467644718653947 := by
  unfold tailWord_6856737
  simp only [CollatzResearch.WordTrace]
  refine ⟨250085743760220361293656465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166723829173480240862437643 250085743760220361293656465)
  ·
    refine ⟨187564307820165270970242349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250085743760220361293656465 187564307820165270970242349)
    ·
      refine ⟨70336615432561976613840881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187564307820165270970242349 70336615432561976613840881)
      ·
        refine ⟨52752461574421482460380661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70336615432561976613840881 52752461574421482460380661)
        ·
          refine ⟨4945543272602013980660687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52752461574421482460380661 4945543272602013980660687)
          ·
            refine ⟨7418314908903020970991031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945543272602013980660687 7418314908903020970991031)
            ·
              refine ⟨11127472363354531456486547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7418314908903020970991031 11127472363354531456486547)
              ·
                refine ⟨16691208545031797184729821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11127472363354531456486547 16691208545031797184729821)
                ·
                  refine ⟨6259203204386923944273683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16691208545031797184729821 6259203204386923944273683)
                  ·
                    refine ⟨9388804806580385916410525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6259203204386923944273683 9388804806580385916410525)
                    ·
                      refine ⟨3520801802467644718653947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9388804806580385916410525 3520801802467644718653947)
                      ·
                        rfl

theorem cell23_6856737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_6856737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856737 prefixEnd_6856737 := by exact prefixLift 6856737
  have htrace : WordTrace (prefixWord ++ tailWord_6856737) baseStart_6856737 baseEnd_6856737 := by
    simpa [prefixWord, tailWord_6856737, baseEnd_6856737] using wordTrace_append hprefix tailTrace_6856737
  have hstable : (prefixWord ++ tailWord_6856737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856737).length < 2 ^ (prefixWord ++ tailWord_6856737).sum := by decide
  have hdescent : baseEnd_6856737 < baseStart_6856737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856739 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 6]
def baseStart_6856739 : Nat := 118140960795 + 6856739 * 2 ^ 59
def prefixEnd_6856739 : Nat := 4983230072969 + 3 ^ 40 * 6856739 * 2
def baseEnd_6856739 : Nat := 3520802829428953710828937

theorem tailTrace_6856739 : CollatzResearch.WordTrace tailWord_6856739 prefixEnd_6856739 3520802829428953710828937 := by
  unfold tailWord_6856739
  simp only [CollatzResearch.WordTrace]
  refine ⟨250085816706213115635229271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166723877804142077090152847 250085816706213115635229271)
  ·
    refine ⟨375128725059319673452843907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250085816706213115635229271 375128725059319673452843907)
    ·
      refine ⟨562693087588979510179265861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375128725059319673452843907 562693087588979510179265861)
      ·
        refine ⟨105504953922933658158612349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 562693087588979510179265861 105504953922933658158612349)
        ·
          refine ⟨39564357721100121809479631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105504953922933658158612349 39564357721100121809479631)
          ·
            refine ⟨59346536581650182714219447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39564357721100121809479631 59346536581650182714219447)
            ·
              refine ⟨89019804872475274071329171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59346536581650182714219447 89019804872475274071329171)
              ·
                refine ⟨133529707308712911106993757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89019804872475274071329171 133529707308712911106993757)
                ·
                  refine ⟨50073640240767341665122659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133529707308712911106993757 50073640240767341665122659)
                  ·
                    refine ⟨75110460361151012497683989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50073640240767341665122659 75110460361151012497683989)
                    ·
                      refine ⟨3520802829428953710828937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75110460361151012497683989 3520802829428953710828937)
                      ·
                        rfl

theorem cell23_6856739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_6856739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856739 prefixEnd_6856739 := by exact prefixLift 6856739
  have htrace : WordTrace (prefixWord ++ tailWord_6856739) baseStart_6856739 baseEnd_6856739 := by
    simpa [prefixWord, tailWord_6856739, baseEnd_6856739] using wordTrace_append hprefix tailTrace_6856739
  have hstable : (prefixWord ++ tailWord_6856739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856739).length < 2 ^ (prefixWord ++ tailWord_6856739).sum := by decide
  have hdescent : baseEnd_6856739 < baseStart_6856739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856753 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 2, 4]
def baseStart_6856753 : Nat := 118140960795 + 6856753 * 2 ^ 59
def prefixEnd_6856753 : Nat := 4983230072969 + 3 ^ 40 * 6856753 * 2
def baseEnd_6856753 : Nat := 1173603339386038885351291

theorem tailTrace_6856753 : CollatzResearch.WordTrace tailWord_6856753 prefixEnd_6856753 1173603339386038885351291 := by
  unfold tailWord_6856753
  simp only [CollatzResearch.WordTrace]
  refine ⟨250086327328162396026238913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166724218218774930684159275 250086327328162396026238913)
  ·
    refine ⟨187564745496121797019679185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250086327328162396026238913 187564745496121797019679185)
    ·
      refine ⟨140673559122091347764759389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187564745496121797019679185 140673559122091347764759389)
      ·
        refine ⟨52752584670784255411784771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140673559122091347764759389 52752584670784255411784771)
        ·
          refine ⟨79128877006176383117677157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52752584670784255411784771 79128877006176383117677157)
          ·
            refine ⟨14836664438658071834564467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79128877006176383117677157 14836664438658071834564467)
            ·
              refine ⟨22254996657987107751846701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14836664438658071834564467 22254996657987107751846701)
              ·
                refine ⟨8345623746745165406942513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22254996657987107751846701 8345623746745165406942513)
                ·
                  refine ⟨6259217810058874055206885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8345623746745165406942513 6259217810058874055206885)
                  ·
                    refine ⟨1173603339386038885351291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6259217810058874055206885 1173603339386038885351291)
                    ·
                      rfl

theorem cell23_6856753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_6856753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856753 prefixEnd_6856753 := by exact prefixLift 6856753
  have htrace : WordTrace (prefixWord ++ tailWord_6856753) baseStart_6856753 baseEnd_6856753 := by
    simpa [prefixWord, tailWord_6856753, baseEnd_6856753] using wordTrace_append hprefix tailTrace_6856753
  have hstable : (prefixWord ++ tailWord_6856753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856753).length < 2 ^ (prefixWord ++ tailWord_6856753).sum := by decide
  have hdescent : baseEnd_6856753 < baseStart_6856753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856760 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 1, 1, 4]
def baseStart_6856760 : Nat := 118140960795 + 6856760 * 2 ^ 59
def prefixEnd_6856760 : Nat := 4983230072969 + 3 ^ 40 * 6856760 * 2
def baseEnd_6856760 : Nat := 3520813612522698128666341

theorem tailTrace_6856760 : CollatzResearch.WordTrace tailWord_6856760 prefixEnd_6856760 3520813612522698128666341 := by
  unfold tailWord_6856760
  simp only [CollatzResearch.WordTrace]
  refine ⟨125043291319568518110871867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166724388426091357481162489 125043291319568518110871867)
  ·
    refine ⟨187564936979352777166307801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125043291319568518110871867 187564936979352777166307801)
    ·
      refine ⟨140673702734514582874730851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187564936979352777166307801 140673702734514582874730851)
      ·
        refine ⟨211010554101771874312096277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140673702734514582874730851 211010554101771874312096277)
        ·
          refine ⟨9891119723520556608379513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 211010554101771874312096277 9891119723520556608379513)
          ·
            refine ⟨7418339792640417456284635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9891119723520556608379513 7418339792640417456284635)
            ·
              refine ⟨11127509688960626184426953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7418339792640417456284635 11127509688960626184426953)
              ·
                refine ⟨8345632266720469638320215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11127509688960626184426953 8345632266720469638320215)
                ·
                  refine ⟨12518448400080704457480323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8345632266720469638320215 12518448400080704457480323)
                  ·
                    refine ⟨18777672600121056686220485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12518448400080704457480323 18777672600121056686220485)
                    ·
                      refine ⟨3520813612522698128666341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18777672600121056686220485 3520813612522698128666341)
                      ·
                        rfl

theorem cell23_6856760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_6856760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856760 prefixEnd_6856760 := by exact prefixLift 6856760
  have htrace : WordTrace (prefixWord ++ tailWord_6856760) baseStart_6856760 baseEnd_6856760 := by
    simpa [prefixWord, tailWord_6856760, baseEnd_6856760] using wordTrace_append hprefix tailTrace_6856760
  have hstable : (prefixWord ++ tailWord_6856760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856760).length < 2 ^ (prefixWord ++ tailWord_6856760).sum := by decide
  have hdescent : baseEnd_6856760 < baseStart_6856760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856796 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_6856796 : Nat := 118140960795 + 6856796 * 2 ^ 59
def prefixEnd_6856796 : Nat := 4983230072969 + 3 ^ 40 * 6856796 * 2
def baseEnd_6856796 : Nat := 1173610699275419995938725

theorem tailTrace_6856796 : CollatzResearch.WordTrace tailWord_6856796 prefixEnd_6856796 1173610699275419995938725 := by
  unfold tailWord_6856796
  simp only [CollatzResearch.WordTrace]
  refine ⟨125043947833503307185027121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166725263778004409580036161 125043947833503307185027121)
  ·
    refine ⟨93782960875127480388770341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125043947833503307185027121 93782960875127480388770341)
    ·
      refine ⟨17584305164086402572894439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93782960875127480388770341 17584305164086402572894439)
      ·
        refine ⟨26376457746129603859341659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17584305164086402572894439 26376457746129603859341659)
        ·
          refine ⟨39564686619194405789012489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26376457746129603859341659 39564686619194405789012489)
          ·
            refine ⟨29673514964395804341759367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39564686619194405789012489 29673514964395804341759367)
            ·
              refine ⟨44510272446593706512639051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29673514964395804341759367 44510272446593706512639051)
              ·
                refine ⟨66765408669890559768958577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44510272446593706512639051 66765408669890559768958577)
                ·
                  refine ⟨50074056502417919826718933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66765408669890559768958577 50074056502417919826718933)
                  ·
                    refine ⟨1173610699275419995938725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50074056502417919826718933 1173610699275419995938725)
                    ·
                      rfl

theorem cell23_6856796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_6856796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856796 prefixEnd_6856796 := by exact prefixLift 6856796
  have htrace : WordTrace (prefixWord ++ tailWord_6856796) baseStart_6856796 baseEnd_6856796 := by
    simpa [prefixWord, tailWord_6856796, baseEnd_6856796] using wordTrace_append hprefix tailTrace_6856796
  have hstable : (prefixWord ++ tailWord_6856796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856796).length < 2 ^ (prefixWord ++ tailWord_6856796).sum := by decide
  have hdescent : baseEnd_6856796 < baseStart_6856796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856803 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 3, 3, 2]
def baseStart_6856803 : Nat := 118140960795 + 6856803 * 2 ^ 59
def prefixEnd_6856803 : Nat := 4983230072969 + 3 ^ 40 * 6856803 * 2
def baseEnd_6856803 : Nat := 3520835692190841460428643

theorem tailTrace_6856803 : CollatzResearch.WordTrace tailWord_6856803 prefixEnd_6856803 3520835692190841460428643 := by
  unfold tailWord_6856803
  simp only [CollatzResearch.WordTrace]
  refine ⟨250088150977981254565559063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166725433985320836377039375 250088150977981254565559063)
  ·
    refine ⟨375132226466971881848338595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250088150977981254565559063 375132226466971881848338595)
    ·
      refine ⟨562698339700457822772507893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375132226466971881848338595 562698339700457822772507893)
      ·
        refine ⟨52752969346917920884922615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 562698339700457822772507893 52752969346917920884922615)
        ·
          refine ⟨79129454020376881327383923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52752969346917920884922615 79129454020376881327383923)
          ·
            refine ⟨118694181030565321991075885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79129454020376881327383923 118694181030565321991075885)
            ·
              refine ⟨44510317886461995746653457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118694181030565321991075885 44510317886461995746653457)
              ·
                refine ⟨33382738414846496809990093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44510317886461995746653457 33382738414846496809990093)
                ·
                  refine ⟨12518526905567436303746285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33382738414846496809990093 12518526905567436303746285)
                  ·
                    refine ⟨4694447589587788613904857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12518526905567436303746285 4694447589587788613904857)
                    ·
                      refine ⟨3520835692190841460428643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694447589587788613904857 3520835692190841460428643)
                      ·
                        rfl

theorem cell23_6856803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_6856803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856803 prefixEnd_6856803 := by exact prefixLift 6856803
  have htrace : WordTrace (prefixWord ++ tailWord_6856803) baseStart_6856803 baseEnd_6856803 := by
    simpa [prefixWord, tailWord_6856803, baseEnd_6856803] using wordTrace_append hprefix tailTrace_6856803
  have hstable : (prefixWord ++ tailWord_6856803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856803).length < 2 ^ (prefixWord ++ tailWord_6856803).sum := by decide
  have hdescent : baseEnd_6856803 < baseStart_6856803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856810 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_6856810 : Nat := 118140960795 + 6856810 * 2 ^ 59
def prefixEnd_6856810 : Nat := 4983230072969 + 3 ^ 40 * 6856810 * 2
def baseEnd_6856810 : Nat := 3520839286555422933041111

theorem tailTrace_6856810 : CollatzResearch.WordTrace tailWord_6856810 prefixEnd_6856810 3520839286555422933041111 := by
  unfold tailWord_6856810
  simp only [CollatzResearch.WordTrace]
  refine ⟨62522101572238973690265971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166725604192637263174042589 62522101572238973690265971)
  ·
    refine ⟨93783152358358460535398957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62522101572238973690265971 93783152358358460535398957)
    ·
      refine ⟨35168682134384422700774609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93783152358358460535398957 35168682134384422700774609)
      ·
        refine ⟨26376511600788317025580957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35168682134384422700774609 26376511600788317025580957)
        ·
          refine ⟨9891191850295618884592859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26376511600788317025580957 9891191850295618884592859)
          ·
            refine ⟨14836787775443428326889289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9891191850295618884592859 14836787775443428326889289)
            ·
              refine ⟨11127590831582571245166967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14836787775443428326889289 11127590831582571245166967)
              ·
                refine ⟨16691386247373856867750451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11127590831582571245166967 16691386247373856867750451)
                ·
                  refine ⟨25037079371060785301625677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16691386247373856867750451 25037079371060785301625677)
                  ·
                    refine ⟨9388904764147794488109629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25037079371060785301625677 9388904764147794488109629)
                    ·
                      refine ⟨3520839286555422933041111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9388904764147794488109629 3520839286555422933041111)
                      ·
                        rfl

theorem cell23_6856810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_6856810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856810 prefixEnd_6856810 := by exact prefixLift 6856810
  have htrace : WordTrace (prefixWord ++ tailWord_6856810) baseStart_6856810 baseEnd_6856810 := by
    simpa [prefixWord, tailWord_6856810, baseEnd_6856810] using wordTrace_append hprefix tailTrace_6856810
  have hstable : (prefixWord ++ tailWord_6856810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856810).length < 2 ^ (prefixWord ++ tailWord_6856810).sum := by decide
  have hdescent : baseEnd_6856810 < baseStart_6856810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856836 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_6856836 : Nat := 118140960795 + 6856836 * 2 ^ 59
def prefixEnd_6856836 : Nat := 4983230072969 + 3 ^ 40 * 6856836 * 2
def baseEnd_6856836 : Nat := 3520852637052439831315991

theorem tailTrace_6856836 : CollatzResearch.WordTrace tailWord_6856836 prefixEnd_6856836 3520852637052439831315991 := by
  unfold tailWord_6856836
  simp only [CollatzResearch.WordTrace]
  refine ⟨125044677293430850600755181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166726236391241134134340241 125044677293430850600755181)
  ·
    refine ⟨46891753985036568975283193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125044677293430850600755181 46891753985036568975283193)
    ·
      refine ⟨35168815488777426731462395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46891753985036568975283193 35168815488777426731462395)
      ·
        refine ⟨52753223233166140097193593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35168815488777426731462395 52753223233166140097193593)
        ·
          refine ⟨39564917424874605072895195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52753223233166140097193593 39564917424874605072895195)
          ·
            refine ⟨59347376137311907609342793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39564917424874605072895195 59347376137311907609342793)
            ·
              refine ⟨44510532102983930707007095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59347376137311907609342793 44510532102983930707007095)
              ·
                refine ⟨66765798154475896060510643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44510532102983930707007095 66765798154475896060510643)
                ·
                  refine ⟨100148697231713844090765965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66765798154475896060510643 100148697231713844090765965)
                  ·
                    refine ⟨37555761461892691534037237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100148697231713844090765965 37555761461892691534037237)
                    ·
                      refine ⟨3520852637052439831315991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37555761461892691534037237 3520852637052439831315991)
                      ·
                        rfl

theorem cell23_6856836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_6856836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856836 prefixEnd_6856836 := by exact prefixLift 6856836
  have htrace : WordTrace (prefixWord ++ tailWord_6856836) baseStart_6856836 baseEnd_6856836 := by
    simpa [prefixWord, tailWord_6856836, baseEnd_6856836] using wordTrace_append hprefix tailTrace_6856836
  have hstable : (prefixWord ++ tailWord_6856836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856836).length < 2 ^ (prefixWord ++ tailWord_6856836).sum := by decide
  have hdescent : baseEnd_6856836 < baseStart_6856836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856837 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 1, 3, 2]
def baseStart_6856837 : Nat := 118140960795 + 6856837 * 2 ^ 59
def prefixEnd_6856837 : Nat := 4983230072969 + 3 ^ 40 * 6856837 * 2
def baseEnd_6856837 : Nat := 3520853150533094327403487

theorem tailTrace_6856837 : CollatzResearch.WordTrace tailWord_6856837 prefixEnd_6856837 3520853150533094327403487 := by
  unfold tailWord_6856837
  simp only [CollatzResearch.WordTrace]
  refine ⟨250089391059858078372296765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166726260706572052248197843 250089391059858078372296765)
  ·
    refine ⟨93783521647446779389611287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250089391059858078372296765 93783521647446779389611287)
    ·
      refine ⟨140675282471170169084416931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93783521647446779389611287 140675282471170169084416931)
      ·
        refine ⟨211012923706755253626625397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140675282471170169084416931 211012923706755253626625397)
        ·
          refine ⟨19782461597508305027496131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211012923706755253626625397 19782461597508305027496131)
          ·
            refine ⟨29673692396262457541244197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19782461597508305027496131 29673692396262457541244197)
            ·
              refine ⟨5563817324299210788983287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29673692396262457541244197 5563817324299210788983287)
              ·
                refine ⟨8345725986448816183474931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5563817324299210788983287 8345725986448816183474931)
                ·
                  refine ⟨12518588979673224275212397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8345725986448816183474931 12518588979673224275212397)
                  ·
                    refine ⟨4694470867377459103204649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12518588979673224275212397 4694470867377459103204649)
                    ·
                      refine ⟨3520853150533094327403487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694470867377459103204649 3520853150533094327403487)
                      ·
                        rfl

theorem cell23_6856837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 3, 2].length) (baseStart_6856837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856837 prefixEnd_6856837 := by exact prefixLift 6856837
  have htrace : WordTrace (prefixWord ++ tailWord_6856837) baseStart_6856837 baseEnd_6856837 := by
    simpa [prefixWord, tailWord_6856837, baseEnd_6856837] using wordTrace_append hprefix tailTrace_6856837
  have hstable : (prefixWord ++ tailWord_6856837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856837).length < 2 ^ (prefixWord ++ tailWord_6856837).sum := by decide
  have hdescent : baseEnd_6856837 < baseStart_6856837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856863 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 4]
def baseStart_6856863 : Nat := 118140960795 + 6856863 * 2 ^ 59
def prefixEnd_6856863 : Nat := 4983230072969 + 3 ^ 40 * 6856863 * 2
def baseEnd_6856863 : Nat := 3520866501030111225678367

theorem tailTrace_6856863 : CollatzResearch.WordTrace tailWord_6856863 prefixEnd_6856863 3520866501030111225678367 := by
  unfold tailWord_6856863
  simp only [CollatzResearch.WordTrace]
  refine ⟨250090339357763884812743243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166726892905175923208495495 250090339357763884812743243)
  ·
    refine ⟨375135509036645827219114865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250090339357763884812743243 375135509036645827219114865)
    ·
      refine ⟨281351631777484370414336149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375135509036645827219114865 281351631777484370414336149)
      ·
        refine ⟨13188357739569579863172007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 281351631777484370414336149 13188357739569579863172007)
        ·
          refine ⟨19782536609354369794758011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13188357739569579863172007 19782536609354369794758011)
          ·
            refine ⟨29673804914031554692137017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19782536609354369794758011 29673804914031554692137017)
            ·
              refine ⟨22255353685523666019102763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29673804914031554692137017 22255353685523666019102763)
              ·
                refine ⟨33383030528285499028654145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22255353685523666019102763 33383030528285499028654145)
                ·
                  refine ⟨25037272896214124271490609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33383030528285499028654145 25037272896214124271490609)
                  ·
                    refine ⟨18777954672160593203617957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25037272896214124271490609 18777954672160593203617957)
                    ·
                      refine ⟨3520866501030111225678367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18777954672160593203617957 3520866501030111225678367)
                      ·
                        rfl

theorem cell23_6856863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_6856863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856863 prefixEnd_6856863 := by exact prefixLift 6856863
  have htrace : WordTrace (prefixWord ++ tailWord_6856863) baseStart_6856863 baseEnd_6856863 := by
    simpa [prefixWord, tailWord_6856863, baseEnd_6856863] using wordTrace_append hprefix tailTrace_6856863
  have hstable : (prefixWord ++ tailWord_6856863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856863).length < 2 ^ (prefixWord ++ tailWord_6856863).sum := by decide
  have hdescent : baseEnd_6856863 < baseStart_6856863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856893 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 1, 7, 2]
def baseStart_6856893 : Nat := 118140960795 + 6856893 * 2 ^ 59
def prefixEnd_6856893 : Nat := 4983230072969 + 3 ^ 40 * 6856893 * 2
def baseEnd_6856893 : Nat := 3520881905449746108303229

theorem tailTrace_6856893 : CollatzResearch.WordTrace tailWord_6856893 prefixEnd_6856893 3520881905449746108303229 := by
  unfold tailWord_6856893
  simp only [CollatzResearch.WordTrace]
  refine ⟨250091433547655199936335333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166727622365103466624223555 250091433547655199936335333)
  ·
    refine ⟨46892143790185349988062875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250091433547655199936335333 46892143790185349988062875)
    ·
      refine ⟨70338215685278024982094313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46892143790185349988062875 70338215685278024982094313)
      ·
        refine ⟨52753661763958518736570735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70338215685278024982094313 52753661763958518736570735)
        ·
          refine ⟨79130492645937778104856103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52753661763958518736570735 79130492645937778104856103)
          ·
            refine ⟨118695738968906667157284155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79130492645937778104856103 118695738968906667157284155)
            ·
              refine ⟨178043608453360000735926233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118695738968906667157284155 178043608453360000735926233)
              ·
                refine ⟨133532706340020000551944675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178043608453360000735926233 133532706340020000551944675)
                ·
                  refine ⟨200299059510030000827917013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133532706340020000551944675 200299059510030000827917013)
                  ·
                    refine ⟨4694509207266328144404305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 200299059510030000827917013 4694509207266328144404305)
                    ·
                      refine ⟨3520881905449746108303229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694509207266328144404305 3520881905449746108303229)
                      ·
                        rfl

theorem cell23_6856893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_6856893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856893 prefixEnd_6856893 := by exact prefixLift 6856893
  have htrace : WordTrace (prefixWord ++ tailWord_6856893) baseStart_6856893 baseEnd_6856893 := by
    simpa [prefixWord, tailWord_6856893, baseEnd_6856893] using wordTrace_append hprefix tailTrace_6856893
  have hstable : (prefixWord ++ tailWord_6856893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856893).length < 2 ^ (prefixWord ++ tailWord_6856893).sum := by decide
  have hdescent : baseEnd_6856893 < baseStart_6856893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856918 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_6856918 : Nat := 118140960795 + 6856918 * 2 ^ 59
def prefixEnd_6856918 : Nat := 4983230072969 + 3 ^ 40 * 6856918 * 2
def baseEnd_6856918 : Nat := 3520894742466108510490615

theorem tailTrace_6856918 : CollatzResearch.WordTrace tailWord_6856918 prefixEnd_6856918 3520894742466108510490615 := by
  unfold tailWord_6856918
  simp only [CollatzResearch.WordTrace]
  refine ⟨15630771585785289325374713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166728230248376419470663605 15630771585785289325374713)
  ·
    refine ⟨11723078689338966994031035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15630771585785289325374713 11723078689338966994031035)
    ·
      refine ⟨17584618034008450491046553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11723078689338966994031035 17584618034008450491046553)
      ·
        refine ⟨13188463525506337868284915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17584618034008450491046553 13188463525506337868284915)
        ·
          refine ⟨19782695288259506802427373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13188463525506337868284915 19782695288259506802427373)
          ·
            refine ⟨7418510733097315050910265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19782695288259506802427373 7418510733097315050910265)
            ·
              refine ⟨5563883049822986288182699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7418510733097315050910265 5563883049822986288182699)
              ·
                refine ⟨8345824574734479432274049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5563883049822986288182699 8345824574734479432274049)
                ·
                  refine ⟨6259368431050859574205537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8345824574734479432274049 6259368431050859574205537)
                  ·
                    refine ⟨4694526323288144680654153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6259368431050859574205537 4694526323288144680654153)
                    ·
                      refine ⟨3520894742466108510490615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694526323288144680654153 3520894742466108510490615)
                      ·
                        rfl

theorem cell23_6856918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_6856918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856918 prefixEnd_6856918 := by exact prefixLift 6856918
  have htrace : WordTrace (prefixWord ++ tailWord_6856918) baseStart_6856918 baseEnd_6856918 := by
    simpa [prefixWord, tailWord_6856918, baseEnd_6856918] using wordTrace_append hprefix tailTrace_6856918
  have hstable : (prefixWord ++ tailWord_6856918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856918).length < 2 ^ (prefixWord ++ tailWord_6856918).sum := by decide
  have hdescent : baseEnd_6856918 < baseStart_6856918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856963 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 6]
def baseStart_6856963 : Nat := 118140960795 + 6856963 * 2 ^ 59
def prefixEnd_6856963 : Nat := 4983230072969 + 3 ^ 40 * 6856963 * 2
def baseEnd_6856963 : Nat := 391213094343951203825323

theorem tailTrace_6856963 : CollatzResearch.WordTrace tailWord_6856963 prefixEnd_6856963 391213094343951203825323 := by
  unfold tailWord_6856963
  simp only [CollatzResearch.WordTrace]
  refine ⟨250093986657401601891383543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166729324438267734594255695 250093986657401601891383543)
  ·
    refine ⟨375140979986102402837075315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250093986657401601891383543 375140979986102402837075315)
    ·
      refine ⟨562711469979153604255612973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375140979986102402837075315 562711469979153604255612973)
      ·
        refine ⟨211016801242182601595854865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 562711469979153604255612973 211016801242182601595854865)
        ·
          refine ⟨158262600931636951196891149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211016801242182601595854865 158262600931636951196891149)
          ·
            refine ⟨59348475349363856698834181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158262600931636951196891149 59348475349363856698834181)
            ·
              refine ⟨11127839128005723131031409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59348475349363856698834181 11127839128005723131031409)
              ·
                refine ⟨8345879346004292348273557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11127839128005723131031409 8345879346004292348273557)
                ·
                  refine ⟨391213094343951203825323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8345879346004292348273557 391213094343951203825323)
                  ·
                    rfl

theorem cell23_6856963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 6].length) (baseStart_6856963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856963 prefixEnd_6856963 := by exact prefixLift 6856963
  have htrace : WordTrace (prefixWord ++ tailWord_6856963) baseStart_6856963 baseEnd_6856963 := by
    simpa [prefixWord, tailWord_6856963, baseEnd_6856963] using wordTrace_append hprefix tailTrace_6856963
  have hstable : (prefixWord ++ tailWord_6856963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856963).length < 2 ^ (prefixWord ++ tailWord_6856963).sum := by decide
  have hdescent : baseEnd_6856963 < baseStart_6856963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6856993 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 3, 5]
def baseStart_6856993 : Nat := 118140960795 + 6856993 * 2 ^ 59
def prefixEnd_6856993 : Nat := 4983230072969 + 3 ^ 40 * 6856993 * 2
def baseEnd_6856993 : Nat := 1173644417838398572350923

theorem tailTrace_6856993 : CollatzResearch.WordTrace tailWord_6856993 prefixEnd_6856993 1173644417838398572350923 := by
  unfold tailWord_6856993
  simp only [CollatzResearch.WordTrace]
  refine ⟨250095080847292917014975633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166730053898195278009983755 250095080847292917014975633)
  ·
    refine ⟨187571310635469687761231725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250095080847292917014975633 187571310635469687761231725)
    ·
      refine ⟨70339241488301132910461897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187571310635469687761231725 70339241488301132910461897)
      ·
        refine ⟨52754431116225849682846423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70339241488301132910461897 52754431116225849682846423)
        ·
          refine ⟨79131646674338774524269635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52754431116225849682846423 79131646674338774524269635)
          ·
            refine ⟨118697470011508161786404453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79131646674338774524269635 118697470011508161786404453)
            ·
              refine ⟨22255775627157780334950835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118697470011508161786404453 22255775627157780334950835)
              ·
                refine ⟨33383663440736670502426253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22255775627157780334950835 33383663440736670502426253)
                ·
                  refine ⟨12518873790276251438409845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33383663440736670502426253 12518873790276251438409845)
                  ·
                    refine ⟨1173644417838398572350923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12518873790276251438409845 1173644417838398572350923)
                    ·
                      rfl

theorem cell23_6856993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_6856993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6856993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6856993 prefixEnd_6856993 := by exact prefixLift 6856993
  have htrace : WordTrace (prefixWord ++ tailWord_6856993) baseStart_6856993 baseEnd_6856993 := by
    simpa [prefixWord, tailWord_6856993, baseEnd_6856993] using wordTrace_append hprefix tailTrace_6856993
  have hstable : (prefixWord ++ tailWord_6856993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6856993).length < 2 ^ (prefixWord ++ tailWord_6856993).sum := by decide
  have hdescent : baseEnd_6856993 < baseStart_6856993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6856993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857007 : List Nat := [1, 1, 2, 1, 2, 1, 5, 5, 1, 1, 3]
def baseStart_6857007 : Nat := 118140960795 + 6857007 * 2 ^ 59
def prefixEnd_6857007 : Nat := 4983230072969 + 3 ^ 40 * 6857007 * 2
def baseEnd_6857007 : Nat := 3520940442244358662277705

theorem tailTrace_6857007 : CollatzResearch.WordTrace tailWord_6857007 prefixEnd_6857007 3520940442244358662277705 := by
  unfold tailWord_6857007
  simp only [CollatzResearch.WordTrace]
  refine ⟨250095591469242197405985275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166730394312828131603990183 250095591469242197405985275)
  ·
    refine ⟨375143387203863296108977913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250095591469242197405985275 375143387203863296108977913)
    ·
      refine ⟨281357540402897472081733435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375143387203863296108977913 281357540402897472081733435)
      ·
        refine ⟨422036310604346208122600153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281357540402897472081733435 422036310604346208122600153)
        ·
          refine ⟨316527232953259656091950115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422036310604346208122600153 316527232953259656091950115)
          ·
            refine ⟨474790849429889484137925173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316527232953259656091950115 474790849429889484137925173)
            ·
              refine ⟨44511642134052139137930485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 474790849429889484137925173 44511642134052139137930485)
              ·
                refine ⟨4172966450067388044180983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44511642134052139137930485 4172966450067388044180983)
                ·
                  refine ⟨6259449675101082066271475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172966450067388044180983 6259449675101082066271475)
                  ·
                    refine ⟨9389174512651623099407213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6259449675101082066271475 9389174512651623099407213)
                    ·
                      refine ⟨3520940442244358662277705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9389174512651623099407213 3520940442244358662277705)
                      ·
                        rfl

theorem cell23_6857007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 1, 1, 3].length) (baseStart_6857007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857007 prefixEnd_6857007 := by exact prefixLift 6857007
  have htrace : WordTrace (prefixWord ++ tailWord_6857007) baseStart_6857007 baseEnd_6857007 := by
    simpa [prefixWord, tailWord_6857007, baseEnd_6857007] using wordTrace_append hprefix tailTrace_6857007
  have hstable : (prefixWord ++ tailWord_6857007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857007).length < 2 ^ (prefixWord ++ tailWord_6857007).sum := by decide
  have hdescent : baseEnd_6857007 < baseStart_6857007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857040 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 1, 6]
def baseStart_6857040 : Nat := 118140960795 + 6857040 * 2 ^ 59
def prefixEnd_6857040 : Nat := 4983230072969 + 3 ^ 40 * 6857040 * 2
def baseEnd_6857040 : Nat := 1173652462368652344388351

theorem tailTrace_6857040 : CollatzResearch.WordTrace tailWord_6857040 prefixEnd_6857040 1173652462368652344388351 := by
  unfold tailWord_6857040
  simp only [CollatzResearch.WordTrace]
  refine ⟨125048397539061322020968287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166731196718748429361291049 125048397539061322020968287)
  ·
    refine ⟨187572596308591983031452431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125048397539061322020968287 187572596308591983031452431)
    ·
      refine ⟨281358894462887974547178647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187572596308591983031452431 281358894462887974547178647)
      ·
        refine ⟨422038341694331961820767971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281358894462887974547178647 422038341694331961820767971)
        ·
          refine ⟨633057512541497942731151957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422038341694331961820767971 633057512541497942731151957)
          ·
            refine ⟨7418642725095679016380687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 633057512541497942731151957 7418642725095679016380687)
            ·
              refine ⟨11127964087643518524571031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7418642725095679016380687 11127964087643518524571031)
              ·
                refine ⟨16691946131465277786856547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11127964087643518524571031 16691946131465277786856547)
                ·
                  refine ⟨25037919197197916680284821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16691946131465277786856547 25037919197197916680284821)
                  ·
                    refine ⟨1173652462368652344388351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25037919197197916680284821 1173652462368652344388351)
                    ·
                      rfl

theorem cell23_6857040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 6].length) (baseStart_6857040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857040 prefixEnd_6857040 := by exact prefixLift 6857040
  have htrace : WordTrace (prefixWord ++ tailWord_6857040) baseStart_6857040 baseEnd_6857040 := by
    simpa [prefixWord, tailWord_6857040, baseEnd_6857040] using wordTrace_append hprefix tailTrace_6857040
  have hstable : (prefixWord ++ tailWord_6857040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857040).length < 2 ^ (prefixWord ++ tailWord_6857040).sum := by decide
  have hdescent : baseEnd_6857040 < baseStart_6857040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857043 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 4]
def baseStart_6857043 : Nat := 118140960795 + 6857043 * 2 ^ 59
def prefixEnd_6857043 : Nat := 4983230072969 + 3 ^ 40 * 6857043 * 2
def baseEnd_6857043 : Nat := 3520958927547920521427539

theorem tailTrace_6857043 : CollatzResearch.WordTrace tailWord_6857043 prefixEnd_6857043 3520958927547920521427539 := by
  unfold tailWord_6857043
  simp only [CollatzResearch.WordTrace]
  refine ⟨250096904497111775554295783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166731269664741183702863855 250096904497111775554295783)
  ·
    refine ⟨375145356745667663331443675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250096904497111775554295783 375145356745667663331443675)
    ·
      refine ⟨562718035118501494997165513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375145356745667663331443675 562718035118501494997165513)
      ·
        refine ⟨422038526338876121247874135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562718035118501494997165513 422038526338876121247874135)
        ·
          refine ⟨633057789508314181871811203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422038526338876121247874135 633057789508314181871811203)
          ·
            refine ⟨949586684262471272807716805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633057789508314181871811203 949586684262471272807716805)
            ·
              refine ⟨178047503299213363651446901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 949586684262471272807716805 178047503299213363651446901)
              ·
                refine ⟨16691953434301252842323147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178047503299213363651446901 16691953434301252842323147)
                ·
                  refine ⟨25037930151451879263484721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16691953434301252842323147 25037930151451879263484721)
                  ·
                    refine ⟨18778447613588909447613541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25037930151451879263484721 18778447613588909447613541)
                    ·
                      refine ⟨3520958927547920521427539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18778447613588909447613541 3520958927547920521427539)
                      ·
                        rfl

theorem cell23_6857043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_6857043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857043 prefixEnd_6857043 := by exact prefixLift 6857043
  have htrace : WordTrace (prefixWord ++ tailWord_6857043) baseStart_6857043 baseEnd_6857043 := by
    simpa [prefixWord, tailWord_6857043, baseEnd_6857043] using wordTrace_append hprefix tailTrace_6857043
  have hstable : (prefixWord ++ tailWord_6857043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857043).length < 2 ^ (prefixWord ++ tailWord_6857043).sum := by decide
  have hdescent : baseEnd_6857043 < baseStart_6857043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857047 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 3, 2, 2]
def baseStart_6857047 : Nat := 118140960795 + 6857047 * 2 ^ 59
def prefixEnd_6857047 : Nat := 4983230072969 + 3 ^ 40 * 6857047 * 2
def baseEnd_6857047 : Nat := 3520960981470538505777521

theorem tailTrace_6857047 : CollatzResearch.WordTrace tailWord_6857047 prefixEnd_6857047 3520960981470538505777521 := by
  unfold tailWord_6857047
  simp only [CollatzResearch.WordTrace]
  refine ⟨250097050389097284237441395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166731366926064856158294263 250097050389097284237441395)
  ·
    refine ⟨375145575583645926356162093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250097050389097284237441395 375145575583645926356162093)
    ·
      refine ⟨140679590843867222383560785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375145575583645926356162093 140679590843867222383560785)
      ·
        refine ⟨105509693132900416787670589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140679590843867222383560785 105509693132900416787670589)
        ·
          refine ⟨39566134924837656295376471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105509693132900416787670589 39566134924837656295376471)
          ·
            refine ⟨59349202387256484443064707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39566134924837656295376471 59349202387256484443064707)
            ·
              refine ⟨89023803580884726664597061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59349202387256484443064707 89023803580884726664597061)
              ·
                refine ⟨16691963171415886249611949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89023803580884726664597061 16691963171415886249611949)
                ·
                  refine ⟨6259486189280957343604481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16691963171415886249611949 6259486189280957343604481)
                  ·
                    refine ⟨4694614641960718007703361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6259486189280957343604481 4694614641960718007703361)
                    ·
                      refine ⟨3520960981470538505777521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694614641960718007703361 3520960981470538505777521)
                      ·
                        rfl

theorem cell23_6857047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_6857047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857047 prefixEnd_6857047 := by exact prefixLift 6857047
  have htrace : WordTrace (prefixWord ++ tailWord_6857047) baseStart_6857047 baseEnd_6857047 := by
    simpa [prefixWord, tailWord_6857047, baseEnd_6857047] using wordTrace_append hprefix tailTrace_6857047
  have hstable : (prefixWord ++ tailWord_6857047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857047).length < 2 ^ (prefixWord ++ tailWord_6857047).sum := by decide
  have hdescent : baseEnd_6857047 < baseStart_6857047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857091 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 2, 4]
def baseStart_6857091 : Nat := 118140960795 + 6857091 * 2 ^ 59
def prefixEnd_6857091 : Nat := 4983230072969 + 3 ^ 40 * 6857091 * 2
def baseEnd_6857091 : Nat := 1173661191539778777875773

theorem tailTrace_6857091 : CollatzResearch.WordTrace tailWord_6857091 prefixEnd_6857091 1173661191539778777875773 := by
  unfold tailWord_6857091
  simp only [CollatzResearch.WordTrace]
  refine ⟨250098655200937879752043127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166732436800625253168028751 250098655200937879752043127)
  ·
    refine ⟨375147982801406819628064691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250098655200937879752043127 375147982801406819628064691)
    ·
      refine ⟨562721974202110229442097037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375147982801406819628064691 562721974202110229442097037)
      ·
        refine ⟨211020740325791336040786389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 562721974202110229442097037 211020740325791336040786389)
        ·
          refine ⟨4945798601385734438455931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 211020740325791336040786389 4945798601385734438455931)
          ·
            refine ⟨7418697902078601657683897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945798601385734438455931 7418697902078601657683897)
            ·
              refine ⟨5564023426558951243262923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7418697902078601657683897 5564023426558951243262923)
              ·
                refine ⟨8346035139838426864894385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564023426558951243262923 8346035139838426864894385)
                ·
                  refine ⟨6259526354878820148670789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8346035139838426864894385 6259526354878820148670789)
                  ·
                    refine ⟨1173661191539778777875773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6259526354878820148670789 1173661191539778777875773)
                    ·
                      rfl

theorem cell23_6857091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 2, 4].length) (baseStart_6857091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857091 prefixEnd_6857091 := by exact prefixLift 6857091
  have htrace : WordTrace (prefixWord ++ tailWord_6857091) baseStart_6857091 baseEnd_6857091 := by
    simpa [prefixWord, tailWord_6857091, baseEnd_6857091] using wordTrace_append hprefix tailTrace_6857091
  have hstable : (prefixWord ++ tailWord_6857091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857091).length < 2 ^ (prefixWord ++ tailWord_6857091).sum := by decide
  have hdescent : baseEnd_6857091 < baseStart_6857091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857150 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_6857150 : Nat := 118140960795 + 6857150 * 2 ^ 59
def prefixEnd_6857150 : Nat := 4983230072969 + 3 ^ 40 * 6857150 * 2
def baseEnd_6857150 : Nat := 3521013869977951602789547

theorem tailTrace_6857150 : CollatzResearch.WordTrace tailWord_6857150 prefixEnd_6857150 3521013869977951602789547 := by
  unfold tailWord_6857150
  simp only [CollatzResearch.WordTrace]
  refine ⟨31262600888465516603555113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166733871405149421885627269 31262600888465516603555113)
  ·
    refine ⟨23446950666349137452666335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31262600888465516603555113 23446950666349137452666335)
    ·
      refine ⟨35170425999523706178999503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23446950666349137452666335 35170425999523706178999503)
      ·
        refine ⟨52755638999285559268499255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35170425999523706178999503 52755638999285559268499255)
        ·
          refine ⟨79133458498928338902748883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52755638999285559268499255 79133458498928338902748883)
          ·
            refine ⟨118700187748392508354123325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79133458498928338902748883 118700187748392508354123325)
            ·
              refine ⟨44512570405647190632796247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118700187748392508354123325 44512570405647190632796247)
              ·
                refine ⟨66768855608470785949194371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44512570405647190632796247 66768855608470785949194371)
                ·
                  refine ⟨100153283412706178923791557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66768855608470785949194371 100153283412706178923791557)
                  ·
                    refine ⟨18778740639882408548210917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100153283412706178923791557 18778740639882408548210917)
                    ·
                      refine ⟨3521013869977951602789547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18778740639882408548210917 3521013869977951602789547)
                      ·
                        rfl

theorem cell23_6857150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_6857150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857150 prefixEnd_6857150 := by exact prefixLift 6857150
  have htrace : WordTrace (prefixWord ++ tailWord_6857150) baseStart_6857150 baseEnd_6857150 := by
    simpa [prefixWord, tailWord_6857150, baseEnd_6857150] using wordTrace_append hprefix tailTrace_6857150
  have hstable : (prefixWord ++ tailWord_6857150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857150).length < 2 ^ (prefixWord ++ tailWord_6857150).sum := by decide
  have hdescent : baseEnd_6857150 < baseStart_6857150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857160 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 7]
def baseStart_6857160 : Nat := 118140960795 + 6857160 * 2 ^ 59
def prefixEnd_6857160 : Nat := 4983230072969 + 3 ^ 40 * 6857160 * 2
def baseEnd_6857160 : Nat := 391224333864944062629389

theorem tailTrace_6857160 : CollatzResearch.WordTrace tailWord_6857160 prefixEnd_6857160 391224333864944062629389 := by
  unfold tailWord_6857160
  simp only [CollatzResearch.WordTrace]
  refine ⟨125050585918843952268152467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166734114558458603024203289 125050585918843952268152467)
  ·
    refine ⟨187575878878265928402228701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125050585918843952268152467 187575878878265928402228701)
    ·
      refine ⟨70340954579349723150835763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187575878878265928402228701 70340954579349723150835763)
      ·
        refine ⟨105511431869024584726253645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70340954579349723150835763 105511431869024584726253645)
        ·
          refine ⟨39566786950884219272345117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105511431869024584726253645 39566786950884219272345117)
          ·
            refine ⟨14837545106581582227129419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39566786950884219272345117 14837545106581582227129419)
            ·
              refine ⟨22256317659872373340694129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14837545106581582227129419 22256317659872373340694129)
              ·
                refine ⟨16692238244904280005520597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22256317659872373340694129 16692238244904280005520597)
                ·
                  refine ⟨391224333864944062629389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16692238244904280005520597 391224333864944062629389)
                  ·
                    rfl

theorem cell23_6857160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 7].length) (baseStart_6857160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857160 prefixEnd_6857160 := by exact prefixLift 6857160
  have htrace : WordTrace (prefixWord ++ tailWord_6857160) baseStart_6857160 baseEnd_6857160 := by
    simpa [prefixWord, tailWord_6857160, baseEnd_6857160] using wordTrace_append hprefix tailTrace_6857160
  have hstable : (prefixWord ++ tailWord_6857160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857160).length < 2 ^ (prefixWord ++ tailWord_6857160).sum := by decide
  have hdescent : baseEnd_6857160 < baseStart_6857160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857177 : List Nat := [1, 2, 1, 2, 4, 1, 4, 3, 5]
def baseStart_6857177 : Nat := 118140960795 + 6857177 * 2 ^ 59
def prefixEnd_6857177 : Nat := 4983230072969 + 3 ^ 40 * 6857177 * 2
def baseEnd_6857177 : Nat := 391225303772846999683547

theorem tailTrace_6857177 : CollatzResearch.WordTrace tailWord_6857177 prefixEnd_6857177 391225303772846999683547 := by
  unfold tailWord_6857177
  simp only [CollatzResearch.WordTrace]
  refine ⟨250101791878626316439673785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166734527919084210959782523 250101791878626316439673785)
  ·
    refine ⟨187576343908969737329755339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250101791878626316439673785 187576343908969737329755339)
    ·
      refine ⟨281364515863454605994633009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187576343908969737329755339 281364515863454605994633009)
      ·
        refine ⟨211023386897590954495974757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281364515863454605994633009 211023386897590954495974757)
        ·
          refine ⟨39566885043298303967995267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211023386897590954495974757 39566885043298303967995267)
          ·
            refine ⟨59350327564947455951992901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39566885043298303967995267 59350327564947455951992901)
            ·
              refine ⟨11128186418427647990998669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59350327564947455951992901 11128186418427647990998669)
              ·
                refine ⟨4173069906910367996624501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11128186418427647990998669 4173069906910367996624501)
                ·
                  refine ⟨391225303772846999683547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4173069906910367996624501 391225303772846999683547)
                  ·
                    rfl

theorem cell23_6857177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 5].length) (baseStart_6857177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857177 prefixEnd_6857177 := by exact prefixLift 6857177
  have htrace : WordTrace (prefixWord ++ tailWord_6857177) baseStart_6857177 baseEnd_6857177 := by
    simpa [prefixWord, tailWord_6857177, baseEnd_6857177] using wordTrace_append hprefix tailTrace_6857177
  have hstable : (prefixWord ++ tailWord_6857177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857177).length < 2 ^ (prefixWord ++ tailWord_6857177).sum := by decide
  have hdescent : baseEnd_6857177 < baseStart_6857177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857205 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_6857205 : Nat := 118140960795 + 6857205 * 2 ^ 59
def prefixEnd_6857205 : Nat := 4983230072969 + 3 ^ 40 * 6857205 * 2
def baseEnd_6857205 : Nat := 3521042111413948887601795

theorem tailTrace_6857205 : CollatzResearch.WordTrace tailWord_6857205 prefixEnd_6857205 3521042111413948887601795 := by
  unfold tailWord_6857205
  simp only [CollatzResearch.WordTrace]
  refine ⟨250102813122524877221693069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166735208748349918147795379 250102813122524877221693069)
  ·
    refine ⟨93788554920946828958134901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250102813122524877221693069 93788554920946828958134901)
    ·
      refine ⟨8792677023838765214825147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93788554920946828958134901 8792677023838765214825147)
      ·
        refine ⟨13189015535758147822237721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8792677023838765214825147 13189015535758147822237721)
        ·
          refine ⟨9891761651818610866678291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13189015535758147822237721 9891761651818610866678291)
          ·
            refine ⟨14837642477727916300017437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9891761651818610866678291 14837642477727916300017437)
            ·
              refine ⟨5564115929147968612506539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14837642477727916300017437 5564115929147968612506539)
              ·
                refine ⟨8346173893721952918759809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564115929147968612506539 8346173893721952918759809)
                ·
                  refine ⟨6259630420291464689069857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8346173893721952918759809 6259630420291464689069857)
                  ·
                    refine ⟨4694722815218598516802393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6259630420291464689069857 4694722815218598516802393)
                    ·
                      refine ⟨3521042111413948887601795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694722815218598516802393 3521042111413948887601795)
                      ·
                        rfl

theorem cell23_6857205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_6857205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857205 prefixEnd_6857205 := by exact prefixLift 6857205
  have htrace : WordTrace (prefixWord ++ tailWord_6857205) baseStart_6857205 baseEnd_6857205 := by
    simpa [prefixWord, tailWord_6857205, baseEnd_6857205] using wordTrace_append hprefix tailTrace_6857205
  have hstable : (prefixWord ++ tailWord_6857205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857205).length < 2 ^ (prefixWord ++ tailWord_6857205).sum := by decide
  have hdescent : baseEnd_6857205 < baseStart_6857205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857210 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_6857210 : Nat := 118140960795 + 6857210 * 2 ^ 59
def prefixEnd_6857210 : Nat := 4983230072969 + 3 ^ 40 * 6857210 * 2
def baseEnd_6857210 : Nat := 3521044678817221368039271

theorem tailTrace_6857210 : CollatzResearch.WordTrace tailWord_6857210 prefixEnd_6857210 3521044678817221368039271 := by
  unfold tailWord_6857210
  simp only [CollatzResearch.WordTrace]
  refine ⟨62525748871876690768906271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166735330325004508717083389 62525748871876690768906271)
  ·
    refine ⟨93788623307815036153359407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62525748871876690768906271 93788623307815036153359407)
    ·
      refine ⟨140682934961722554230039111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93788623307815036153359407 140682934961722554230039111)
      ·
        refine ⟨211024402442583831345058667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140682934961722554230039111 211024402442583831345058667)
        ·
          refine ⟨316536603663875747017588001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211024402442583831345058667 316536603663875747017588001)
          ·
            refine ⟨237402452747906810263191001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316536603663875747017588001 237402452747906810263191001)
            ·
              refine ⟨178051839560930107697393251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237402452747906810263191001 178051839560930107697393251)
              ·
                refine ⟨267077759341395161546089877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178051839560930107697393251 267077759341395161546089877)
                ·
                  refine ⟨12519269969127898197472963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 267077759341395161546089877 12519269969127898197472963)
                  ·
                    refine ⟨18778904953691847296209445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12519269969127898197472963 18778904953691847296209445)
                    ·
                      refine ⟨3521044678817221368039271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18778904953691847296209445 3521044678817221368039271)
                      ·
                        rfl

theorem cell23_6857210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_6857210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857210 prefixEnd_6857210 := by exact prefixLift 6857210
  have htrace : WordTrace (prefixWord ++ tailWord_6857210) baseStart_6857210 baseEnd_6857210 := by
    simpa [prefixWord, tailWord_6857210, baseEnd_6857210] using wordTrace_append hprefix tailTrace_6857210
  have hstable : (prefixWord ++ tailWord_6857210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857210).length < 2 ^ (prefixWord ++ tailWord_6857210).sum := by decide
  have hdescent : baseEnd_6857210 < baseStart_6857210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857304 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 2, 3, 2]
def baseStart_6857304 : Nat := 118140960795 + 6857304 * 2 ^ 59
def prefixEnd_6857304 : Nat := 4983230072969 + 3 ^ 40 * 6857304 * 2
def baseEnd_6857304 : Nat := 3521092945998744000263839

theorem tailTrace_6857304 : CollatzResearch.WordTrace tailWord_6857304 prefixEnd_6857304 3521092945998744000263839 := by
  unfold tailWord_6857304
  simp only [CollatzResearch.WordTrace]
  refine ⟨125053211974583108564773483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166737615966110811419697977 125053211974583108564773483)
  ·
    refine ⟨187579817961874662847160225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125053211974583108564773483 187579817961874662847160225)
    ·
      refine ⟨140684863471405997135370169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187579817961874662847160225 140684863471405997135370169)
      ·
        refine ⟨105513647603554497851527627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140684863471405997135370169 105513647603554497851527627)
        ·
          refine ⟨158270471405331746777291441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105513647603554497851527627 158270471405331746777291441)
          ·
            refine ⟨118702853553998810082968581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158270471405331746777291441 118702853553998810082968581)
            ·
              refine ⟨22256785041374776890556609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118702853553998810082968581 22256785041374776890556609)
              ·
                refine ⟨16692588781031082667917457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22256785041374776890556609 16692588781031082667917457)
                ·
                  refine ⟨12519441585773312000938093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16692588781031082667917457 12519441585773312000938093)
                  ·
                    refine ⟨4694790594664992000351785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12519441585773312000938093 4694790594664992000351785)
                    ·
                      refine ⟨3521092945998744000263839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694790594664992000351785 3521092945998744000263839)
                      ·
                        rfl

theorem cell23_6857304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_6857304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857304 prefixEnd_6857304 := by exact prefixLift 6857304
  have htrace : WordTrace (prefixWord ++ tailWord_6857304) baseStart_6857304 baseEnd_6857304 := by
    simpa [prefixWord, tailWord_6857304, baseEnd_6857304] using wordTrace_append hprefix tailTrace_6857304
  have hstable : (prefixWord ++ tailWord_6857304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857304).length < 2 ^ (prefixWord ++ tailWord_6857304).sum := by decide
  have hdescent : baseEnd_6857304 < baseStart_6857304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857340 : List Nat := [2, 2, 2, 1, 1, 2, 2, 11]
def baseStart_6857340 : Nat := 118140960795 + 6857340 * 2 ^ 59
def prefixEnd_6857340 : Nat := 4983230072969 + 3 ^ 40 * 6857340 * 2
def baseEnd_6857340 : Nat := 130411534492677994793099

theorem tailTrace_6857340 : CollatzResearch.WordTrace tailWord_6857340 prefixEnd_6857340 130411534492677994793099 := by
  unfold tailWord_6857340
  simp only [CollatzResearch.WordTrace]
  refine ⟨125053868488517897638928737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166738491318023863518571649 125053868488517897638928737)
  ·
    refine ⟨93790401366388423229196553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125053868488517897638928737 93790401366388423229196553)
    ·
      refine ⟨70342801024791317421897415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93790401366388423229196553 70342801024791317421897415)
      ·
        refine ⟨105514201537186976132846123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70342801024791317421897415 105514201537186976132846123)
        ·
          refine ⟨158271302305780464199269185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105514201537186976132846123 158271302305780464199269185)
          ·
            refine ⟨118703476729335348149451889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158271302305780464199269185 118703476729335348149451889)
            ·
              refine ⟨89027607547001511112088917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118703476729335348149451889 89027607547001511112088917)
              ·
                refine ⟨130411534492677994793099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 89027607547001511112088917 130411534492677994793099)
                ·
                  rfl

theorem cell23_6857340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 11].length) (baseStart_6857340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857340 prefixEnd_6857340 := by exact prefixLift 6857340
  have htrace : WordTrace (prefixWord ++ tailWord_6857340) baseStart_6857340 baseEnd_6857340 := by
    simpa [prefixWord, tailWord_6857340, baseEnd_6857340] using wordTrace_append hprefix tailTrace_6857340
  have hstable : (prefixWord ++ tailWord_6857340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857340).length < 2 ^ (prefixWord ++ tailWord_6857340).sum := by decide
  have hdescent : baseEnd_6857340 < baseStart_6857340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857347 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 4]
def baseStart_6857347 : Nat := 118140960795 + 6857347 * 2 ^ 59
def prefixEnd_6857347 : Nat := 4983230072969 + 3 ^ 40 * 6857347 * 2
def baseEnd_6857347 : Nat := 3521115025666887332026141

theorem tailTrace_6857347 : CollatzResearch.WordTrace tailWord_6857347 prefixEnd_6857347 3521115025666887332026141 := by
  unfold tailWord_6857347
  simp only [CollatzResearch.WordTrace]
  refine ⟨250107992288010435473362295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166738661525340290315574863 250107992288010435473362295)
  ·
    refine ⟨375161988432015653210043443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250107992288010435473362295 375161988432015653210043443)
    ·
      refine ⟨562742982648023479815065165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375161988432015653210043443 562742982648023479815065165)
      ·
        refine ⟨211028618493008804930649437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 562742982648023479815065165 211028618493008804930649437)
        ·
          refine ⟨79135731934878301848993539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211028618493008804930649437 79135731934878301848993539)
          ·
            refine ⟨118703597902317452773490309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79135731934878301848993539 118703597902317452773490309)
            ·
              refine ⟨22256924606684522395029433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118703597902317452773490309 22256924606684522395029433)
              ·
                refine ⟨16692693455013391796272075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22256924606684522395029433 16692693455013391796272075)
                ·
                  refine ⟨25039040182520087694408113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16692693455013391796272075 25039040182520087694408113)
                  ·
                    refine ⟨18779280136890065770806085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25039040182520087694408113 18779280136890065770806085)
                    ·
                      refine ⟨3521115025666887332026141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18779280136890065770806085 3521115025666887332026141)
                      ·
                        rfl

theorem cell23_6857347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_6857347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857347 prefixEnd_6857347 := by exact prefixLift 6857347
  have htrace : WordTrace (prefixWord ++ tailWord_6857347) baseStart_6857347 baseEnd_6857347 := by
    simpa [prefixWord, tailWord_6857347, baseEnd_6857347] using wordTrace_append hprefix tailTrace_6857347
  have hstable : (prefixWord ++ tailWord_6857347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857347).length < 2 ^ (prefixWord ++ tailWord_6857347).sum := by decide
  have hdescent : baseEnd_6857347 < baseStart_6857347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857360 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_6857360 : Nat := 118140960795 + 6857360 * 2 ^ 59
def prefixEnd_6857360 : Nat := 4983230072969 + 3 ^ 40 * 6857360 * 2
def baseEnd_6857360 : Nat := 3521121700915395781163581

theorem tailTrace_6857360 : CollatzResearch.WordTrace tailWord_6857360 prefixEnd_6857360 3521121700915395781163581 := by
  unfold tailWord_6857360
  simp only [CollatzResearch.WordTrace]
  refine ⟨125054233218481669346792767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166738977624642225795723689 125054233218481669346792767)
  ·
    refine ⟨187581349827722504020189151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125054233218481669346792767 187581349827722504020189151)
    ·
      refine ⟨281372024741583756030283727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187581349827722504020189151 281372024741583756030283727)
      ·
        refine ⟨422058037112375634045425591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281372024741583756030283727 422058037112375634045425591)
        ·
          refine ⟨633087055668563451068138387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422058037112375634045425591 633087055668563451068138387)
          ·
            refine ⟨949630583502845176602207581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633087055668563451068138387 949630583502845176602207581)
            ·
              refine ⟨356111468813566941225827843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 949630583502845176602207581 356111468813566941225827843)
              ·
                refine ⟨534167203220350411838741765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356111468813566941225827843 534167203220350411838741765)
                ·
                  refine ⟨100156350603815702219764081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534167203220350411838741765 100156350603815702219764081)
                  ·
                    refine ⟨75117262952861776664823061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100156350603815702219764081 75117262952861776664823061)
                    ·
                      refine ⟨3521121700915395781163581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75117262952861776664823061 3521121700915395781163581)
                      ·
                        rfl

theorem cell23_6857360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_6857360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857360 prefixEnd_6857360 := by exact prefixLift 6857360
  have htrace : WordTrace (prefixWord ++ tailWord_6857360) baseStart_6857360 baseEnd_6857360 := by
    simpa [prefixWord, tailWord_6857360, baseEnd_6857360] using wordTrace_append hprefix tailTrace_6857360
  have hstable : (prefixWord ++ tailWord_6857360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857360).length < 2 ^ (prefixWord ++ tailWord_6857360).sum := by decide
  have hdescent : baseEnd_6857360 < baseStart_6857360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857368 : List Nat := [2, 1, 2, 4, 1, 1, 1, 6, 1, 2, 2]
def baseStart_6857368 : Nat := 118140960795 + 6857368 * 2 ^ 59
def prefixEnd_6857368 : Nat := 4983230072969 + 3 ^ 40 * 6857368 * 2
def baseEnd_6857368 : Nat := 3521125808760631749863545

theorem tailTrace_6857368 : CollatzResearch.WordTrace tailWord_6857368 prefixEnd_6857368 3521125808760631749863545 := by
  unfold tailWord_6857368
  simp only [CollatzResearch.WordTrace]
  refine ⟨125054379110467178029938379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166739172147289570706584505 125054379110467178029938379)
  ·
    refine ⟨187581568665700767044907569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125054379110467178029938379 187581568665700767044907569)
    ·
      refine ⟨140686176499275575283680677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187581568665700767044907569 140686176499275575283680677)
      ·
        refine ⟨26378658093614170365690127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140686176499275575283680677 26378658093614170365690127)
        ·
          refine ⟨39567987140421255548535191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26378658093614170365690127 39567987140421255548535191)
          ·
            refine ⟨59351980710631883322802787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39567987140421255548535191 59351980710631883322802787)
            ·
              refine ⟨89027971065947824984204181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59351980710631883322802787 89027971065947824984204181)
              ·
                refine ⟨4173186143716304296134571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89027971065947824984204181 4173186143716304296134571)
                ·
                  refine ⟨6259779215574456444201857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173186143716304296134571 6259779215574456444201857)
                  ·
                    refine ⟨4694834411680842333151393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6259779215574456444201857 4694834411680842333151393)
                    ·
                      refine ⟨3521125808760631749863545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4694834411680842333151393 3521125808760631749863545)
                      ·
                        rfl

theorem cell23_6857368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_6857368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857368 prefixEnd_6857368 := by exact prefixLift 6857368
  have htrace : WordTrace (prefixWord ++ tailWord_6857368) baseStart_6857368 baseEnd_6857368 := by
    simpa [prefixWord, tailWord_6857368, baseEnd_6857368] using wordTrace_append hprefix tailTrace_6857368
  have hstable : (prefixWord ++ tailWord_6857368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857368).length < 2 ^ (prefixWord ++ tailWord_6857368).sum := by decide
  have hdescent : baseEnd_6857368 < baseStart_6857368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857464 : List Nat := [2, 1, 2, 1, 1, 2, 4, 5, 5]
def baseStart_6857464 : Nat := 118140960795 + 6857464 * 2 ^ 59
def prefixEnd_6857464 : Nat := 4983230072969 + 3 ^ 40 * 6857464 * 2
def baseEnd_6857464 : Nat := 391241678100384819362567

theorem tailTrace_6857464 : CollatzResearch.WordTrace tailWord_6857464 prefixEnd_6857464 391241678100384819362567 := by
  unfold tailWord_6857464
  simp only [CollatzResearch.WordTrace]
  refine ⟨125056129814293282227685723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166741506419057709636914297 125056129814293282227685723)
  ·
    refine ⟨187584194721439923341528585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125056129814293282227685723 187584194721439923341528585)
    ·
      refine ⟨140688146041079942506146439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187584194721439923341528585 140688146041079942506146439)
      ·
        refine ⟨211032219061619913759219659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140688146041079942506146439 211032219061619913759219659)
        ·
          refine ⟨316548328592429870638829489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211032219061619913759219659 316548328592429870638829489)
          ·
            refine ⟨237411246444322402979122117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316548328592429870638829489 237411246444322402979122117)
            ·
              refine ⟨44514608708310450558585397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237411246444322402979122117 44514608708310450558585397)
              ·
                refine ⟨4173244566404104739867381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44514608708310450558585397 4173244566404104739867381)
                ·
                  refine ⟨391241678100384819362567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4173244566404104739867381 391241678100384819362567)
                  ·
                    rfl

theorem cell23_6857464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 5].length) (baseStart_6857464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857464 prefixEnd_6857464 := by exact prefixLift 6857464
  have htrace : WordTrace (prefixWord ++ tailWord_6857464) baseStart_6857464 baseEnd_6857464 := by
    simpa [prefixWord, tailWord_6857464, baseEnd_6857464] using wordTrace_append hprefix tailTrace_6857464
  have hstable : (prefixWord ++ tailWord_6857464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857464).length < 2 ^ (prefixWord ++ tailWord_6857464).sum := by decide
  have hdescent : baseEnd_6857464 < baseStart_6857464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857481 : List Nat := [1, 2, 1, 1, 3, 2, 6, 2, 5]
def baseStart_6857481 : Nat := 118140960795 + 6857481 * 2 ^ 59
def prefixEnd_6857481 : Nat := 4983230072969 + 3 ^ 40 * 6857481 * 2
def baseEnd_6857481 : Nat := 391242648008287756416725

theorem tailTrace_6857481 : CollatzResearch.WordTrace tailWord_6857481 prefixEnd_6857481 391242648008287756416725 := by
  unfold tailWord_6857481
  simp only [CollatzResearch.WordTrace]
  refine ⟨250112879669524976358740297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166741919779683317572493531 250112879669524976358740297)
  ·
    refine ⟨187584659752143732269055223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250112879669524976358740297 187584659752143732269055223)
    ·
      refine ⟨281376989628215598403582835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187584659752143732269055223 281376989628215598403582835)
      ·
        refine ⟨422065484442323397605374253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281376989628215598403582835 422065484442323397605374253)
        ·
          refine ⟨158274556665871274102015345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422065484442323397605374253 158274556665871274102015345)
          ·
            refine ⟨118705917499403455576511509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158274556665871274102015345 118705917499403455576511509)
            ·
              refine ⟨5564339882784536980148977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118705917499403455576511509 5564339882784536980148977)
              ·
                refine ⟨4173254912088402735111733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5564339882784536980148977 4173254912088402735111733)
                ·
                  refine ⟨391242648008287756416725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4173254912088402735111733 391242648008287756416725)
                  ·
                    rfl

theorem cell23_6857481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 5].length) (baseStart_6857481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857481 prefixEnd_6857481 := by exact prefixLift 6857481
  have htrace : WordTrace (prefixWord ++ tailWord_6857481) baseStart_6857481 baseEnd_6857481 := by
    simpa [prefixWord, tailWord_6857481, baseEnd_6857481] using wordTrace_append hprefix tailTrace_6857481
  have hstable : (prefixWord ++ tailWord_6857481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857481).length < 2 ^ (prefixWord ++ tailWord_6857481).sum := by decide
  have hdescent : baseEnd_6857481 < baseStart_6857481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857487 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 5]
def baseStart_6857487 : Nat := 118140960795 + 6857487 * 2 ^ 59
def prefixEnd_6857487 : Nat := 4983230072969 + 3 ^ 40 * 6857487 * 2
def baseEnd_6857487 : Nat := 3521186912958516784275497

theorem tailTrace_6857487 : CollatzResearch.WordTrace tailWord_6857487 prefixEnd_6857487 3521186912958516784275497 := by
  unfold tailWord_6857487
  simp only [CollatzResearch.WordTrace]
  refine ⟨250113098507503239383458715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166742065671668826255639143 250113098507503239383458715)
  ·
    refine ⟨375169647761254859075188073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250113098507503239383458715 375169647761254859075188073)
    ·
      refine ⟨281377235820941144306391055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375169647761254859075188073 281377235820941144306391055)
      ·
        refine ⟨422065853731411716459586583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281377235820941144306391055 422065853731411716459586583)
        ·
          refine ⟨633098780597117574689379875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422065853731411716459586583 633098780597117574689379875)
          ·
            refine ⟨949648170895676362034069813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633098780597117574689379875 949648170895676362034069813)
            ·
              refine ⟨89029516021469658940694045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 949648170895676362034069813 89029516021469658940694045)
              ·
                refine ⟨33386068508051122102760267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89029516021469658940694045 33386068508051122102760267)
                ·
                  refine ⟨50079102762076683154140401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33386068508051122102760267 50079102762076683154140401)
                  ·
                    refine ⟨37559327071557512365605301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50079102762076683154140401 37559327071557512365605301)
                    ·
                      refine ⟨3521186912958516784275497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37559327071557512365605301 3521186912958516784275497)
                      ·
                        rfl

theorem cell23_6857487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_6857487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857487 prefixEnd_6857487 := by exact prefixLift 6857487
  have htrace : WordTrace (prefixWord ++ tailWord_6857487) baseStart_6857487 baseEnd_6857487 := by
    simpa [prefixWord, tailWord_6857487, baseEnd_6857487] using wordTrace_append hprefix tailTrace_6857487
  have hstable : (prefixWord ++ tailWord_6857487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857487).length < 2 ^ (prefixWord ++ tailWord_6857487).sum := by decide
  have hdescent : baseEnd_6857487 < baseStart_6857487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857527 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_6857527 : Nat := 118140960795 + 6857527 * 2 ^ 59
def prefixEnd_6857527 : Nat := 4983230072969 + 3 ^ 40 * 6857527 * 2
def baseEnd_6857527 : Nat := 3521207452184696627775313

theorem tailTrace_6857527 : CollatzResearch.WordTrace tailWord_6857527 prefixEnd_6857527 3521207452184696627775313 := by
  unfold tailWord_6857527
  simp only [CollatzResearch.WordTrace]
  refine ⟨250114557427358326214914835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166743038284905550809943223 250114557427358326214914835)
  ·
    refine ⟨375171836141037489322372253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250114557427358326214914835 375171836141037489322372253)
    ·
      refine ⟨140689438552889058495889595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375171836141037489322372253 140689438552889058495889595)
      ·
        refine ⟨211034157829333587743834393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140689438552889058495889595 211034157829333587743834393)
        ·
          refine ⟨158275618372000190807875795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211034157829333587743834393 158275618372000190807875795)
          ·
            refine ⟨237413427558000286211813693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158275618372000190807875795 237413427558000286211813693)
            ·
              refine ⟨89030035334250107329430135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237413427558000286211813693 89030035334250107329430135)
              ·
                refine ⟨133545053001375160994145203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89030035334250107329430135 133545053001375160994145203)
                ·
                  refine ⟨200317579502062741491217805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133545053001375160994145203 200317579502062741491217805)
                  ·
                    refine ⟨75119092313273528059206677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200317579502062741491217805 75119092313273528059206677)
                    ·
                      refine ⟨3521207452184696627775313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75119092313273528059206677 3521207452184696627775313)
                      ·
                        rfl

theorem cell23_6857527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_6857527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857527 prefixEnd_6857527 := by exact prefixLift 6857527
  have htrace : WordTrace (prefixWord ++ tailWord_6857527) baseStart_6857527 baseEnd_6857527 := by
    simpa [prefixWord, tailWord_6857527, baseEnd_6857527] using wordTrace_append hprefix tailTrace_6857527
  have hstable : (prefixWord ++ tailWord_6857527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857527).length < 2 ^ (prefixWord ++ tailWord_6857527).sum := by decide
  have hdescent : baseEnd_6857527 < baseStart_6857527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857575 : List Nat := [1, 1, 5, 1, 2, 4, 1, 3, 1, 4]
def baseStart_6857575 : Nat := 118140960795 + 6857575 * 2 ^ 59
def prefixEnd_6857575 : Nat := 4983230072969 + 3 ^ 40 * 6857575 * 2
def baseEnd_6857575 : Nat := 1173744033085370813325031

theorem tailTrace_6857575 : CollatzResearch.WordTrace tailWord_6857575 prefixEnd_6857575 1173744033085370813325031 := by
  unfold tailWord_6857575
  simp only [CollatzResearch.WordTrace]
  refine ⟨250116308131184430412662179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166744205420789620275108119 250116308131184430412662179)
  ·
    refine ⟨375174462196776645618993269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250116308131184430412662179 375174462196776645618993269)
    ·
      refine ⟨35172605830947810526780619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 375174462196776645618993269 35172605830947810526780619)
      ·
        refine ⟨52758908746421715790170929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35172605830947810526780619 52758908746421715790170929)
        ·
          refine ⟨39569181559816286842628197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52758908746421715790170929 39569181559816286842628197)
          ·
            refine ⟨7419221542465553782992787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39569181559816286842628197 7419221542465553782992787)
            ·
              refine ⟨11128832313698330674489181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419221542465553782992787 11128832313698330674489181)
              ·
                refine ⟨4173312117636874002933443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11128832313698330674489181 4173312117636874002933443)
                ·
                  refine ⟨6259968176455311004400165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173312117636874002933443 6259968176455311004400165)
                  ·
                    refine ⟨1173744033085370813325031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6259968176455311004400165 1173744033085370813325031)
                    ·
                      rfl

theorem cell23_6857575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_6857575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857575 prefixEnd_6857575 := by exact prefixLift 6857575
  have htrace : WordTrace (prefixWord ++ tailWord_6857575) baseStart_6857575 baseEnd_6857575 := by
    simpa [prefixWord, tailWord_6857575, baseEnd_6857575] using wordTrace_append hprefix tailTrace_6857575
  have hstable : (prefixWord ++ tailWord_6857575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857575).length < 2 ^ (prefixWord ++ tailWord_6857575).sum := by decide
  have hdescent : baseEnd_6857575 < baseStart_6857575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857604 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_6857604 : Nat := 118140960795 + 6857604 * 2 ^ 59
def prefixEnd_6857604 : Nat := 4983230072969 + 3 ^ 40 * 6857604 * 2
def baseEnd_6857604 : Nat := 3521246990195092826512459

theorem tailTrace_6857604 : CollatzResearch.WordTrace tailWord_6857604 prefixEnd_6857604 3521246990195092826512459 := by
  unfold tailWord_6857604
  simp only [CollatzResearch.WordTrace]
  refine ⟨125058682924039684182733933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166744910565386245576978577 125058682924039684182733933)
  ·
    refine ⟨46897006096514881568525225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125058682924039684182733933 46897006096514881568525225)
    ·
      refine ⟨35172754572386161176393919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46897006096514881568525225 35172754572386161176393919)
      ·
        refine ⟨52759131858579241764590879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35172754572386161176393919 52759131858579241764590879)
        ·
          refine ⟨79138697787868862646886319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52759131858579241764590879 79138697787868862646886319)
          ·
            refine ⟨118708046681803293970329479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79138697787868862646886319 118708046681803293970329479)
            ·
              refine ⟨178062070022704940955494219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118708046681803293970329479 178062070022704940955494219)
              ·
                refine ⟨267093105034057411433241329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178062070022704940955494219 267093105034057411433241329)
                ·
                  refine ⟨200319828775543058574930997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267093105034057411433241329 200319828775543058574930997)
                  ·
                    refine ⟨18779983947707161741399781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 200319828775543058574930997 18779983947707161741399781)
                    ·
                      refine ⟨3521246990195092826512459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18779983947707161741399781 3521246990195092826512459)
                      ·
                        rfl

theorem cell23_6857604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_6857604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857604 prefixEnd_6857604 := by exact prefixLift 6857604
  have htrace : WordTrace (prefixWord ++ tailWord_6857604) baseStart_6857604 baseEnd_6857604 := by
    simpa [prefixWord, tailWord_6857604, baseEnd_6857604] using wordTrace_append hprefix tailTrace_6857604
  have hstable : (prefixWord ++ tailWord_6857604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857604).length < 2 ^ (prefixWord ++ tailWord_6857604).sum := by decide
  have hdescent : baseEnd_6857604 < baseStart_6857604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857618 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_6857618 : Nat := 118140960795 + 6857618 * 2 ^ 59
def prefixEnd_6857618 : Nat := 4983230072969 + 3 ^ 40 * 6857618 * 2
def baseEnd_6857618 : Nat := 1173751392974751923912465

theorem tailTrace_6857618 : CollatzResearch.WordTrace tailWord_6857618 prefixEnd_6857618 1173751392974751923912465 := by
  unfold tailWord_6857618
  simp only [CollatzResearch.WordTrace]
  refine ⟨62529469117507162189119377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166745250980019099170985005 62529469117507162189119377)
  ·
    refine ⟨46897101838130371641839533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62529469117507162189119377 46897101838130371641839533)
    ·
      refine ⟨17586413189298889365689825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46897101838130371641839533 17586413189298889365689825)
      ·
        refine ⟨13189809891974167024267369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17586413189298889365689825 13189809891974167024267369)
        ·
          refine ⟨9892357418980625268200527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13189809891974167024267369 9892357418980625268200527)
          ·
            refine ⟨14838536128470937902300791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9892357418980625268200527 14838536128470937902300791)
            ·
              refine ⟨22257804192706406853451187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14838536128470937902300791 22257804192706406853451187)
              ·
                refine ⟨33386706289059610280176781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22257804192706406853451187 33386706289059610280176781)
                ·
                  refine ⟨12520014858397353855066293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33386706289059610280176781 12520014858397353855066293)
                  ·
                    refine ⟨1173751392974751923912465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12520014858397353855066293 1173751392974751923912465)
                    ·
                      rfl

theorem cell23_6857618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_6857618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857618 prefixEnd_6857618 := by exact prefixLift 6857618
  have htrace : WordTrace (prefixWord ++ tailWord_6857618) baseStart_6857618 baseEnd_6857618 := by
    simpa [prefixWord, tailWord_6857618, baseEnd_6857618] using wordTrace_append hprefix tailTrace_6857618
  have hstable : (prefixWord ++ tailWord_6857618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857618).length < 2 ^ (prefixWord ++ tailWord_6857618).sum := by decide
  have hdescent : baseEnd_6857618 < baseStart_6857618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857621 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_6857621 : Nat := 118140960795 + 6857621 * 2 ^ 59
def prefixEnd_6857621 : Nat := 4983230072969 + 3 ^ 40 * 6857621 * 2
def baseEnd_6857621 : Nat := 3521255719366219259999881

theorem tailTrace_6857621 : CollatzResearch.WordTrace tailWord_6857621 prefixEnd_6857621 3521255719366219259999881 := by
  unfold tailWord_6857621
  simp only [CollatzResearch.WordTrace]
  refine ⟨250117985889017780268836717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166745323926011853512557811 250117985889017780268836717)
  ·
    refine ⟨93794244708381667600813769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250117985889017780268836717 93794244708381667600813769)
    ·
      refine ⟨70345683531286250700610327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93794244708381667600813769 70345683531286250700610327)
      ·
        refine ⟨105518525296929376050915491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70345683531286250700610327 105518525296929376050915491)
        ·
          refine ⟨158277787945394064076373237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105518525296929376050915491 158277787945394064076373237)
          ·
            refine ⟨14838542619880693507159991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158277787945394064076373237 14838542619880693507159991)
            ·
              refine ⟨22257813929821040260739987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14838542619880693507159991 22257813929821040260739987)
              ·
                refine ⟨33386720894731560391109981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22257813929821040260739987 33386720894731560391109981)
                ·
                  refine ⟨12520020335524335146666243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33386720894731560391109981 12520020335524335146666243)
                  ·
                    refine ⟨18780030503286502719999365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12520020335524335146666243 18780030503286502719999365)
                    ·
                      refine ⟨3521255719366219259999881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18780030503286502719999365 3521255719366219259999881)
                      ·
                        rfl

theorem cell23_6857621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_6857621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857621 prefixEnd_6857621 := by exact prefixLift 6857621
  have htrace : WordTrace (prefixWord ++ tailWord_6857621) baseStart_6857621 baseEnd_6857621 := by
    simpa [prefixWord, tailWord_6857621, baseEnd_6857621] using wordTrace_append hprefix tailTrace_6857621
  have hstable : (prefixWord ++ tailWord_6857621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857621).length < 2 ^ (prefixWord ++ tailWord_6857621).sum := by decide
  have hdescent : baseEnd_6857621 < baseStart_6857621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857631 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 1, 6]
def baseStart_6857631 : Nat := 118140960795 + 6857631 * 2 ^ 59
def prefixEnd_6857631 : Nat := 4983230072969 + 3 ^ 40 * 6857631 * 2
def baseEnd_6857631 : Nat := 1173753618057588073624945

theorem tailTrace_6857631 : CollatzResearch.WordTrace tailWord_6857631 prefixEnd_6857631 1173753618057588073624945 := by
  unfold tailWord_6857631
  simp only [CollatzResearch.WordTrace]
  refine ⟨250118350618981551976700747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166745567079321034651133831 250118350618981551976700747)
  ·
    refine ⟨375177525928472327965051121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250118350618981551976700747 375177525928472327965051121)
    ·
      refine ⟨281383144446354245973788341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375177525928472327965051121 281383144446354245973788341)
      ·
        refine ⟨26379669791845710560042657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 281383144446354245973788341 26379669791845710560042657)
        ·
          refine ⟨19784752343884282920031993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26379669791845710560042657 19784752343884282920031993)
          ·
            refine ⟨14838564257913212190023995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19784752343884282920031993 14838564257913212190023995)
            ·
              refine ⟨22257846386869818285035993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14838564257913212190023995 22257846386869818285035993)
              ·
                refine ⟨16693384790152363713776995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22257846386869818285035993 16693384790152363713776995)
                ·
                  refine ⟨25040077185228545570665493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16693384790152363713776995 25040077185228545570665493)
                  ·
                    refine ⟨1173753618057588073624945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25040077185228545570665493 1173753618057588073624945)
                    ·
                      rfl

theorem cell23_6857631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_6857631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857631 prefixEnd_6857631 := by exact prefixLift 6857631
  have htrace : WordTrace (prefixWord ++ tailWord_6857631) baseStart_6857631 baseEnd_6857631 := by
    simpa [prefixWord, tailWord_6857631, baseEnd_6857631] using wordTrace_append hprefix tailTrace_6857631
  have hstable : (prefixWord ++ tailWord_6857631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857631).length < 2 ^ (prefixWord ++ tailWord_6857631).sum := by decide
  have hdescent : baseEnd_6857631 < baseStart_6857631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857649 : List Nat := [1, 2, 2, 4, 3, 2, 2, 2, 1, 1, 3]
def baseStart_6857649 : Nat := 118140960795 + 6857649 * 2 ^ 59
def prefixEnd_6857649 : Nat := 4983230072969 + 3 ^ 40 * 6857649 * 2
def baseEnd_6857649 : Nat := 3521270096824545150449753

theorem tailTrace_6857649 : CollatzResearch.WordTrace tailWord_6857649 prefixEnd_6857649 3521270096824545150449753 := by
  unfold tailWord_6857649
  simp only [CollatzResearch.WordTrace]
  refine ⟨250119007132916341050856001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166746004755277560700570667 250119007132916341050856001)
  ·
    refine ⟨187589255349687255788142001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250119007132916341050856001 187589255349687255788142001)
    ·
      refine ⟨140691941512265441841106501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187589255349687255788142001 140691941512265441841106501)
      ·
        refine ⟨26379739033549770345207469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140691941512265441841106501 26379739033549770345207469)
        ·
          refine ⟨9892402137581163879452801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26379739033549770345207469 9892402137581163879452801)
          ·
            refine ⟨7419301603185872909589601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9892402137581163879452801 7419301603185872909589601)
            ·
              refine ⟨5564476202389404682192201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7419301603185872909589601 5564476202389404682192201)
              ·
                refine ⟨4173357151792053511644151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5564476202389404682192201 4173357151792053511644151)
                ·
                  refine ⟨6260035727688080267466227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173357151792053511644151 6260035727688080267466227)
                  ·
                    refine ⟨9390053591532120401199341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6260035727688080267466227 9390053591532120401199341)
                    ·
                      refine ⟨3521270096824545150449753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9390053591532120401199341 3521270096824545150449753)
                      ·
                        rfl

theorem cell23_6857649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_6857649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857649 prefixEnd_6857649 := by exact prefixLift 6857649
  have htrace : WordTrace (prefixWord ++ tailWord_6857649) baseStart_6857649 baseEnd_6857649 := by
    simpa [prefixWord, tailWord_6857649, baseEnd_6857649] using wordTrace_append hprefix tailTrace_6857649
  have hstable : (prefixWord ++ tailWord_6857649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857649).length < 2 ^ (prefixWord ++ tailWord_6857649).sum := by decide
  have hdescent : baseEnd_6857649 < baseStart_6857649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857671 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_6857671 : Nat := 118140960795 + 6857671 * 2 ^ 59
def prefixEnd_6857671 : Nat := 4983230072969 + 3 ^ 40 * 6857671 * 2
def baseEnd_6857671 : Nat := 3521281393398944064374651

theorem tailTrace_6857671 : CollatzResearch.WordTrace tailWord_6857671 prefixEnd_6857671 3521281393398944064374651 := by
  unfold tailWord_6857671
  simp only [CollatzResearch.WordTrace]
  refine ⟨250119809538836638808156867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166746539692557759205437911 250119809538836638808156867)
  ·
    refine ⟨375179714308254958212235301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250119809538836638808156867 375179714308254958212235301)
    ·
      refine ⟨70346196432797804664794119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375179714308254958212235301 70346196432797804664794119)
      ·
        refine ⟨105519294649196706997191179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70346196432797804664794119 105519294649196706997191179)
        ·
          refine ⟨158278941973795060495786769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105519294649196706997191179 158278941973795060495786769)
          ·
            refine ⟨118709206480346295371840077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158278941973795060495786769 118709206480346295371840077)
            ·
              refine ⟨44515952430129860764440029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118709206480346295371840077 44515952430129860764440029)
              ·
                refine ⟨16693482161298697786665011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44515952430129860764440029 16693482161298697786665011)
                ·
                  refine ⟨25040223241948046679997517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16693482161298697786665011 25040223241948046679997517)
                  ·
                    refine ⟨9390083715730517504999069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25040223241948046679997517 9390083715730517504999069)
                    ·
                      refine ⟨3521281393398944064374651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9390083715730517504999069 3521281393398944064374651)
                      ·
                        rfl

theorem cell23_6857671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_6857671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857671 prefixEnd_6857671 := by exact prefixLift 6857671
  have htrace : WordTrace (prefixWord ++ tailWord_6857671) baseStart_6857671 baseEnd_6857671 := by
    simpa [prefixWord, tailWord_6857671, baseEnd_6857671] using wordTrace_append hprefix tailTrace_6857671
  have hstable : (prefixWord ++ tailWord_6857671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857671).length < 2 ^ (prefixWord ++ tailWord_6857671).sum := by decide
  have hdescent : baseEnd_6857671 < baseStart_6857671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857674 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_6857674 : Nat := 118140960795 + 6857674 * 2 ^ 59
def prefixEnd_6857674 : Nat := 4983230072969 + 3 ^ 40 * 6857674 * 2
def baseEnd_6857674 : Nat := 1173760977946969184212379

theorem tailTrace_6857674 : CollatzResearch.WordTrace tailWord_6857674 prefixEnd_6857674 1173760977946969184212379 := by
  unfold tailWord_6857674
  simp only [CollatzResearch.WordTrace]
  refine ⟨62529979739456442580129019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166746612638550513547010717 62529979739456442580129019)
  ·
    refine ⟨93794969609184663870193529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62529979739456442580129019 93794969609184663870193529)
    ·
      refine ⟨70346227206888497902645147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93794969609184663870193529 70346227206888497902645147)
      ·
        refine ⟨105519340810332746853967721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70346227206888497902645147 105519340810332746853967721)
        ·
          refine ⟨79139505607749560140475791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105519340810332746853967721 79139505607749560140475791)
          ·
            refine ⟨118709258411624340210713687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79139505607749560140475791 118709258411624340210713687)
            ·
              refine ⟨178063887617436510316070531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118709258411624340210713687 178063887617436510316070531)
              ·
                refine ⟨267095831426154765474105797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178063887617436510316070531 267095831426154765474105797)
                ·
                  refine ⟨50080468392404018526394837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 267095831426154765474105797 50080468392404018526394837)
                  ·
                    refine ⟨1173760977946969184212379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50080468392404018526394837 1173760977946969184212379)
                    ·
                      rfl

theorem cell23_6857674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_6857674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857674 prefixEnd_6857674 := by exact prefixLift 6857674
  have htrace : WordTrace (prefixWord ++ tailWord_6857674) baseStart_6857674 baseEnd_6857674 := by
    simpa [prefixWord, tailWord_6857674, baseEnd_6857674] using wordTrace_append hprefix tailTrace_6857674
  have hstable : (prefixWord ++ tailWord_6857674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857674).length < 2 ^ (prefixWord ++ tailWord_6857674).sum := by decide
  have hdescent : baseEnd_6857674 < baseStart_6857674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857716 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6857716 : Nat := 118140960795 + 6857716 * 2 ^ 59
def prefixEnd_6857716 : Nat := 4983230072969 + 3 ^ 40 * 6857716 * 2
def baseEnd_6857716 : Nat := 1173768166676132129437315

theorem tailTrace_6857716 : CollatzResearch.WordTrace tailWord_6857716 prefixEnd_6857716 1173768166676132129437315 := by
  unfold tailWord_6857716
  simp only [CollatzResearch.WordTrace]
  refine ⟨125060725411836805746772501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166747633882449074329030001 125060725411836805746772501)
  ·
    refine ⟨5862221503679850269379961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125060725411836805746772501 5862221503679850269379961)
    ·
      refine ⟨4396666127759887702034971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5862221503679850269379961 4396666127759887702034971)
      ·
        refine ⟨6594999191639831553052457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4396666127759887702034971 6594999191639831553052457)
        ·
          refine ⟨4946249393729873664789343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6594999191639831553052457 4946249393729873664789343)
          ·
            refine ⟨7419374090594810497184015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946249393729873664789343 7419374090594810497184015)
            ·
              refine ⟨11129061135892215745776023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419374090594810497184015 11129061135892215745776023)
              ·
                refine ⟨16693591703838323618664035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11129061135892215745776023 16693591703838323618664035)
                ·
                  refine ⟨25040387555757485427996053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16693591703838323618664035 25040387555757485427996053)
                  ·
                    refine ⟨1173768166676132129437315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25040387555757485427996053 1173768166676132129437315)
                    ·
                      rfl

theorem cell23_6857716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6857716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857716 prefixEnd_6857716 := by exact prefixLift 6857716
  have htrace : WordTrace (prefixWord ++ tailWord_6857716) baseStart_6857716 baseEnd_6857716 := by
    simpa [prefixWord, tailWord_6857716, baseEnd_6857716] using wordTrace_append hprefix tailTrace_6857716
  have hstable : (prefixWord ++ tailWord_6857716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857716).length < 2 ^ (prefixWord ++ tailWord_6857716).sum := by decide
  have hdescent : baseEnd_6857716 < baseStart_6857716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857744 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_6857744 : Nat := 118140960795 + 6857744 * 2 ^ 59
def prefixEnd_6857744 : Nat := 4983230072969 + 3 ^ 40 * 6857744 * 2
def baseEnd_6857744 : Nat := 3521318877486722278761815

theorem tailTrace_6857744 : CollatzResearch.WordTrace tailWord_6857744 prefixEnd_6857744 3521318877486722278761815 := by
  unfold tailWord_6857744
  simp only [CollatzResearch.WordTrace]
  refine ⟨125061236033786086137782143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166748314711714781517042857 125061236033786086137782143)
  ·
    refine ⟨187591854050679129206673215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125061236033786086137782143 187591854050679129206673215)
    ·
      refine ⟨281387781076018693810009823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187591854050679129206673215 281387781076018693810009823)
      ·
        refine ⟨422081671614028040715014735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281387781076018693810009823 422081671614028040715014735)
        ·
          refine ⟨633122507421042061072522103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422081671614028040715014735 633122507421042061072522103)
          ·
            refine ⟨949683761131563091608783155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633122507421042061072522103 949683761131563091608783155)
            ·
              refine ⟨1424525641697344637413174733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949683761131563091608783155 1424525641697344637413174733)
              ·
                refine ⟨534197115636504239029940525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1424525641697344637413174733 534197115636504239029940525)
                ·
                  refine ⟨200323918363689089636227697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534197115636504239029940525 200323918363689089636227697)
                  ·
                    refine ⟨150242938772766817227170773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200323918363689089636227697 150242938772766817227170773)
                    ·
                      refine ⟨3521318877486722278761815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150242938772766817227170773 3521318877486722278761815)
                      ·
                        rfl

theorem cell23_6857744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_6857744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857744 prefixEnd_6857744 := by exact prefixLift 6857744
  have htrace : WordTrace (prefixWord ++ tailWord_6857744) baseStart_6857744 baseEnd_6857744 := by
    simpa [prefixWord, tailWord_6857744, baseEnd_6857744] using wordTrace_append hprefix tailTrace_6857744
  have hstable : (prefixWord ++ tailWord_6857744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857744).length < 2 ^ (prefixWord ++ tailWord_6857744).sum := by decide
  have hdescent : baseEnd_6857744 < baseStart_6857744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857781 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_6857781 : Nat := 118140960795 + 6857781 * 2 ^ 59
def prefixEnd_6857781 : Nat := 4983230072969 + 3 ^ 40 * 6857781 * 2
def baseEnd_6857781 : Nat := 1173779292090312877999715

theorem tailTrace_6857781 : CollatzResearch.WordTrace tailWord_6857781 prefixEnd_6857781 1173779292090312877999715 := by
  unfold tailWord_6857781
  simp only [CollatzResearch.WordTrace]
  refine ⟨250123821568438127594661197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166749214378958751729774131 250123821568438127594661197)
  ·
    refine ⟨93796433088164297847997949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250123821568438127594661197 93796433088164297847997949)
    ·
      refine ⟨35173662408061611692999231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93796433088164297847997949 35173662408061611692999231)
      ·
        refine ⟨52760493612092417539498847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35173662408061611692999231 52760493612092417539498847)
        ·
          refine ⟨79140740418138626309248271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52760493612092417539498847 79140740418138626309248271)
          ·
            refine ⟨118711110627207939463872407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79140740418138626309248271 118711110627207939463872407)
            ·
              refine ⟨178066665940811909195808611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118711110627207939463872407 178066665940811909195808611)
              ·
                refine ⟨267099998911217863793712917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178066665940811909195808611 267099998911217863793712917)
                ·
                  refine ⟨12520312448963337365330293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 267099998911217863793712917 12520312448963337365330293)
                  ·
                    refine ⟨1173779292090312877999715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12520312448963337365330293 1173779292090312877999715)
                    ·
                      rfl

theorem cell23_6857781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_6857781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857781 prefixEnd_6857781 := by exact prefixLift 6857781
  have htrace : WordTrace (prefixWord ++ tailWord_6857781) baseStart_6857781 baseEnd_6857781 := by
    simpa [prefixWord, tailWord_6857781, baseEnd_6857781] using wordTrace_append hprefix tailTrace_6857781
  have hstable : (prefixWord ++ tailWord_6857781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857781).length < 2 ^ (prefixWord ++ tailWord_6857781).sum := by decide
  have hdescent : baseEnd_6857781 < baseStart_6857781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857828 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_6857828 : Nat := 118140960795 + 6857828 * 2 ^ 59
def prefixEnd_6857828 : Nat := 4983230072969 + 3 ^ 40 * 6857828 * 2
def baseEnd_6857828 : Nat := 1173787336620566650037143

theorem tailTrace_6857828 : CollatzResearch.WordTrace tailWord_6857828 prefixEnd_6857828 1173787336620566650037143 := by
  unfold tailWord_6857828
  simp only [CollatzResearch.WordTrace]
  refine ⟨125062767899633927310811069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166750357199511903081081425 125062767899633927310811069)
  ·
    refine ⟨46898537962362722741554151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125062767899633927310811069 46898537962362722741554151)
    ·
      refine ⟨70347806943544084112331227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46898537962362722741554151 70347806943544084112331227)
      ·
        refine ⟨105521710415316126168496841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70347806943544084112331227 105521710415316126168496841)
        ·
          refine ⟨79141282811487094626372631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105521710415316126168496841 79141282811487094626372631)
          ·
            refine ⟨118711924217230641939558947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79141282811487094626372631 118711924217230641939558947)
            ·
              refine ⟨178067886325845962909338421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118711924217230641939558947 178067886325845962909338421)
              ·
                refine ⟨16693864343048059022750477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178067886325845962909338421 16693864343048059022750477)
                ·
                  refine ⟨6260199128643022133531429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16693864343048059022750477 6260199128643022133531429)
                  ·
                    refine ⟨1173787336620566650037143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6260199128643022133531429 1173787336620566650037143)
                    ·
                      rfl

theorem cell23_6857828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_6857828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857828 prefixEnd_6857828 := by exact prefixLift 6857828
  have htrace : WordTrace (prefixWord ++ tailWord_6857828) baseStart_6857828 baseEnd_6857828 := by
    simpa [prefixWord, tailWord_6857828, baseEnd_6857828] using wordTrace_append hprefix tailTrace_6857828
  have hstable : (prefixWord ++ tailWord_6857828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857828).length < 2 ^ (prefixWord ++ tailWord_6857828).sum := by decide
  have hdescent : baseEnd_6857828 < baseStart_6857828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857905 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 1, 5]
def baseStart_6857905 : Nat := 118140960795 + 6857905 * 2 ^ 59
def prefixEnd_6857905 : Nat := 4983230072969 + 3 ^ 40 * 6857905 * 2
def baseEnd_6857905 : Nat := 1173800515957365382949525

theorem tailTrace_6857905 : CollatzResearch.WordTrace tailWord_6857905 prefixEnd_6857905 1173800515957365382949525 := by
  unfold tailWord_6857905
  simp only [CollatzResearch.WordTrace]
  refine ⟨250128344219988896772175169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166752229479992597848116779 250128344219988896772175169)
  ·
    refine ⟨187596258164991672579131377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250128344219988896772175169 187596258164991672579131377)
    ·
      refine ⟨140697193623743754434348533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187596258164991672579131377 140697193623743754434348533)
      ·
        refine ⟨13190361902225976978220175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140697193623743754434348533 13190361902225976978220175)
        ·
          refine ⟨19785542853338965467330263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13190361902225976978220175 19785542853338965467330263)
          ·
            refine ⟨29678314280008448200995395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19785542853338965467330263 29678314280008448200995395)
            ·
              refine ⟨44517471420012672301493093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29678314280008448200995395 44517471420012672301493093)
              ·
                refine ⟨8347025891252376056529955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44517471420012672301493093 8347025891252376056529955)
                ·
                  refine ⟨12520538836878564084794933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8347025891252376056529955 12520538836878564084794933)
                  ·
                    refine ⟨1173800515957365382949525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12520538836878564084794933 1173800515957365382949525)
                    ·
                      rfl

theorem cell23_6857905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_6857905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857905 prefixEnd_6857905 := by exact prefixLift 6857905
  have htrace : WordTrace (prefixWord ++ tailWord_6857905) baseStart_6857905 baseEnd_6857905 := by
    simpa [prefixWord, tailWord_6857905, baseEnd_6857905] using wordTrace_append hprefix tailTrace_6857905
  have hstable : (prefixWord ++ tailWord_6857905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857905).length < 2 ^ (prefixWord ++ tailWord_6857905).sum := by decide
  have hdescent : baseEnd_6857905 < baseStart_6857905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857928 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_6857928 : Nat := 118140960795 + 6857928 * 2 ^ 59
def prefixEnd_6857928 : Nat := 4983230072969 + 3 ^ 40 * 6857928 * 2
def baseEnd_6857928 : Nat := 3521413357927149558860969

theorem tailTrace_6857928 : CollatzResearch.WordTrace tailWord_6857928 prefixEnd_6857928 3521413357927149558860969 := by
  unfold tailWord_6857928
  simp only [CollatzResearch.WordTrace]
  refine ⟨125064591549452785850131219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166752788732603714466841625 125064591549452785850131219)
  ·
    refine ⟨187596887324179178775196829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125064591549452785850131219 187596887324179178775196829)
    ·
      refine ⟨70348832746567192040698811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187596887324179178775196829 70348832746567192040698811)
      ·
        refine ⟨105523249119850788061048217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70348832746567192040698811 105523249119850788061048217)
        ·
          refine ⟨79142436839888091045786163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105523249119850788061048217 79142436839888091045786163)
          ·
            refine ⟨118713655259832136568679245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79142436839888091045786163 118713655259832136568679245)
            ·
              refine ⟨44517620722437051213254717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118713655259832136568679245 44517620722437051213254717)
              ·
                refine ⟨16694107770913894204970519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44517620722437051213254717 16694107770913894204970519)
                ·
                  refine ⟨25041161656370841307455779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16694107770913894204970519 25041161656370841307455779)
                  ·
                    refine ⟨37561742484556261961183669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25041161656370841307455779 37561742484556261961183669)
                    ·
                      refine ⟨3521413357927149558860969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37561742484556261961183669 3521413357927149558860969)
                      ·
                        rfl

theorem cell23_6857928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_6857928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857928 prefixEnd_6857928 := by exact prefixLift 6857928
  have htrace : WordTrace (prefixWord ++ tailWord_6857928) baseStart_6857928 baseEnd_6857928 := by
    simpa [prefixWord, tailWord_6857928, baseEnd_6857928] using wordTrace_append hprefix tailTrace_6857928
  have hstable : (prefixWord ++ tailWord_6857928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857928).length < 2 ^ (prefixWord ++ tailWord_6857928).sum := by decide
  have hdescent : baseEnd_6857928 < baseStart_6857928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857938 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_6857938 : Nat := 118140960795 + 6857938 * 2 ^ 59
def prefixEnd_6857938 : Nat := 4983230072969 + 3 ^ 40 * 6857938 * 2
def baseEnd_6857938 : Nat := 3521418492733694519735923

theorem tailTrace_6857938 : CollatzResearch.WordTrace tailWord_6857938 prefixEnd_6857938 3521418492733694519735923 := by
  unfold tailWord_6857938
  simp only [CollatzResearch.WordTrace]
  refine ⟨62532386957217335852031617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166753031885912895605417645 62532386957217335852031617)
  ·
    refine ⟨46899290217913001889023713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62532386957217335852031617 46899290217913001889023713)
    ·
      refine ⟨35174467663434751416767785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46899290217913001889023713 35174467663434751416767785)
      ·
        refine ⟨26380850747576063562575839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35174467663434751416767785 26380850747576063562575839)
        ·
          refine ⟨39571276121364095343863759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26380850747576063562575839 39571276121364095343863759)
          ·
            refine ⟨59356914182046143015795639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39571276121364095343863759 59356914182046143015795639)
            ·
              refine ⟨89035371273069214523693459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59356914182046143015795639 89035371273069214523693459)
              ·
                refine ⟨133553056909603821785540189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89035371273069214523693459 133553056909603821785540189)
                ·
                  refine ⟨50082396341101433169577571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133553056909603821785540189 50082396341101433169577571)
                  ·
                    refine ⟨75123594511652149754366357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50082396341101433169577571 75123594511652149754366357)
                    ·
                      refine ⟨3521418492733694519735923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75123594511652149754366357 3521418492733694519735923)
                      ·
                        rfl

theorem cell23_6857938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_6857938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857938 prefixEnd_6857938 := by exact prefixLift 6857938
  have htrace : WordTrace (prefixWord ++ tailWord_6857938) baseStart_6857938 baseEnd_6857938 := by
    simpa [prefixWord, tailWord_6857938, baseEnd_6857938] using wordTrace_append hprefix tailTrace_6857938
  have hstable : (prefixWord ++ tailWord_6857938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857938).length < 2 ^ (prefixWord ++ tailWord_6857938).sum := by decide
  have hdescent : baseEnd_6857938 < baseStart_6857938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857952 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 2, 4]
def baseStart_6857952 : Nat := 118140960795 + 6857952 * 2 ^ 59
def prefixEnd_6857952 : Nat := 4983230072969 + 3 ^ 40 * 6857952 * 2
def baseEnd_6857952 : Nat := 1173808560487619154986953

theorem tailTrace_6857952 : CollatzResearch.WordTrace tailWord_6857952 prefixEnd_6857952 1173808560487619154986953 := by
  unfold tailWord_6857952
  simp only [CollatzResearch.WordTrace]
  refine ⟨125065029225409311899568055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166753372300545749199424073 125065029225409311899568055)
  ·
    refine ⟨187597543838113967849352083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125065029225409311899568055 187597543838113967849352083)
    ·
      refine ⟨281396315757170951774028125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187597543838113967849352083 281396315757170951774028125)
      ·
        refine ⟨105523618408939106915260547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281396315757170951774028125 105523618408939106915260547)
        ·
          refine ⟨158285427613408660372890821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105523618408939106915260547 158285427613408660372890821)
          ·
            refine ⟨29678517677514123819917029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158285427613408660372890821 29678517677514123819917029)
            ·
              refine ⟨5564722064533898216234443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29678517677514123819917029 5564722064533898216234443)
              ·
                refine ⟨8347083096800847324351665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564722064533898216234443 8347083096800847324351665)
                ·
                  refine ⟨6260312322600635493263749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8347083096800847324351665 6260312322600635493263749)
                  ·
                    refine ⟨1173808560487619154986953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6260312322600635493263749 1173808560487619154986953)
                    ·
                      rfl

theorem cell23_6857952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 2, 4].length) (baseStart_6857952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857952 prefixEnd_6857952 := by exact prefixLift 6857952
  have htrace : WordTrace (prefixWord ++ tailWord_6857952) baseStart_6857952 baseEnd_6857952 := by
    simpa [prefixWord, tailWord_6857952, baseEnd_6857952] using wordTrace_append hprefix tailTrace_6857952
  have hstable : (prefixWord ++ tailWord_6857952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857952).length < 2 ^ (prefixWord ++ tailWord_6857952).sum := by decide
  have hdescent : baseEnd_6857952 < baseStart_6857952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857959 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6857959 : Nat := 118140960795 + 6857959 * 2 ^ 59
def prefixEnd_6857959 : Nat := 4983230072969 + 3 ^ 40 * 6857959 * 2
def baseEnd_6857959 : Nat := 3521429275827438937573327

theorem tailTrace_6857959 : CollatzResearch.WordTrace tailWord_6857959 prefixEnd_6857959 3521429275827438937573327 := by
  unfold tailWord_6857959
  simp only [CollatzResearch.WordTrace]
  refine ⟨250130313761793263994640931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166753542507862175996427287 250130313761793263994640931)
  ·
    refine ⟨375195470642689895991961397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250130313761793263994640931 375195470642689895991961397)
    ·
      refine ⟨35174575372752177749246381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 375195470642689895991961397 35174575372752177749246381)
      ·
        refine ⟨13190465764782066655967393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35174575372752177749246381 13190465764782066655967393)
        ·
          refine ⟨9892849323586549991975545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13190465764782066655967393 9892849323586549991975545)
          ·
            refine ⟨7419636992689912493981659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9892849323586549991975545 7419636992689912493981659)
            ·
              refine ⟨11129455489034868740972489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419636992689912493981659 11129455489034868740972489)
              ·
                refine ⟨8347091616776151555729367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11129455489034868740972489 8347091616776151555729367)
                ·
                  refine ⟨12520637425164227333594051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8347091616776151555729367 12520637425164227333594051)
                  ·
                    refine ⟨18780956137746341000391077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12520637425164227333594051 18780956137746341000391077)
                    ·
                      refine ⟨3521429275827438937573327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18780956137746341000391077 3521429275827438937573327)
                      ·
                        rfl

theorem cell23_6857959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6857959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857959 prefixEnd_6857959 := by exact prefixLift 6857959
  have htrace : WordTrace (prefixWord ++ tailWord_6857959) baseStart_6857959 baseEnd_6857959 := by
    simpa [prefixWord, tailWord_6857959, baseEnd_6857959] using wordTrace_append hprefix tailTrace_6857959
  have hstable : (prefixWord ++ tailWord_6857959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857959).length < 2 ^ (prefixWord ++ tailWord_6857959).sum := by decide
  have hdescent : baseEnd_6857959 < baseStart_6857959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6857962 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_6857962 : Nat := 118140960795 + 6857962 * 2 ^ 59
def prefixEnd_6857962 : Nat := 4983230072969 + 3 ^ 40 * 6857962 * 2
def baseEnd_6857962 : Nat := 3521430816269402425835813

theorem tailTrace_6857962 : CollatzResearch.WordTrace tailWord_6857962 prefixEnd_6857962 3521430816269402425835813 := by
  unfold tailWord_6857962
  simp only [CollatzResearch.WordTrace]
  refine ⟨62532605795195598876750035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166753615453854930338000093 62532605795195598876750035)
  ·
    refine ⟨93798908692793398315125053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62532605795195598876750035 93798908692793398315125053)
    ·
      refine ⟨35174590759797524368171895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93798908692793398315125053 35174590759797524368171895)
      ·
        refine ⟨52761886139696286552257843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35174590759797524368171895 52761886139696286552257843)
        ·
          refine ⟨79142829209544429828386765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52761886139696286552257843 79142829209544429828386765)
          ·
            refine ⟨29678560953579161185645037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79142829209544429828386765 29678560953579161185645037)
            ·
              refine ⟨11129460357592185444616889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29678560953579161185645037 11129460357592185444616889)
              ·
                refine ⟨8347095268194139083462667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11129460357592185444616889 8347095268194139083462667)
                ·
                  refine ⟨12520642902291208625194001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8347095268194139083462667 12520642902291208625194001)
                  ·
                    refine ⟨9390482176718406468895501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12520642902291208625194001 9390482176718406468895501)
                    ·
                      refine ⟨3521430816269402425835813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9390482176718406468895501 3521430816269402425835813)
                      ·
                        rfl

theorem cell23_6857962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_6857962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6857962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6857962 prefixEnd_6857962 := by exact prefixLift 6857962
  have htrace : WordTrace (prefixWord ++ tailWord_6857962) baseStart_6857962 baseEnd_6857962 := by
    simpa [prefixWord, tailWord_6857962, baseEnd_6857962] using wordTrace_append hprefix tailTrace_6857962
  have hstable : (prefixWord ++ tailWord_6857962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6857962).length < 2 ^ (prefixWord ++ tailWord_6857962).sum := by decide
  have hdescent : baseEnd_6857962 < baseStart_6857962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6857962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858008 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 1, 8]
def baseStart_6858008 : Nat := 118140960795 + 6858008 * 2 ^ 59
def prefixEnd_6858008 : Nat := 4983230072969 + 3 ^ 40 * 6858008 * 2
def baseEnd_6858008 : Nat := 1173818145459836415286867

theorem tailTrace_6858008 : CollatzResearch.WordTrace tailWord_6858008 prefixEnd_6858008 1173818145459836415286867 := by
  unfold tailWord_6858008
  simp only [CollatzResearch.WordTrace]
  refine ⟨125066050469307872681587339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166754733959077163575449785 125066050469307872681587339)
  ·
    refine ⟨187599075703961809022381009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125066050469307872681587339 187599075703961809022381009)
    ·
      refine ⟨140699306777971356766785757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187599075703961809022381009 140699306777971356766785757)
      ·
        refine ⟨52762240041739258787544659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140699306777971356766785757 52762240041739258787544659)
        ·
          refine ⟨79143360062608888181316989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52762240041739258787544659 79143360062608888181316989)
          ·
            refine ⟨29678760023478333067993871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79143360062608888181316989 29678760023478333067993871)
            ·
              refine ⟨44518140035217499601990807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29678760023478333067993871 44518140035217499601990807)
              ·
                refine ⟨66777210052826249402986211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44518140035217499601990807 66777210052826249402986211)
                ·
                  refine ⟨100165815079239374104479317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66777210052826249402986211 100165815079239374104479317)
                  ·
                    refine ⟨1173818145459836415286867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100165815079239374104479317 1173818145459836415286867)
                    ·
                      rfl

theorem cell23_6858008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_6858008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858008 prefixEnd_6858008 := by exact prefixLift 6858008
  have htrace : WordTrace (prefixWord ++ tailWord_6858008) baseStart_6858008 baseEnd_6858008 := by
    simpa [prefixWord, tailWord_6858008, baseEnd_6858008] using wordTrace_append hprefix tailTrace_6858008
  have hstable : (prefixWord ++ tailWord_6858008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858008).length < 2 ^ (prefixWord ++ tailWord_6858008).sum := by decide
  have hdescent : baseEnd_6858008 < baseStart_6858008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858028 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_6858028 : Nat := 118140960795 + 6858028 * 2 ^ 59
def prefixEnd_6858028 : Nat := 4983230072969 + 3 ^ 40 * 6858028 * 2
def baseEnd_6858028 : Nat := 3521464705992599167610509

theorem tailTrace_6858028 : CollatzResearch.WordTrace tailWord_6858028 prefixEnd_6858028 3521464705992599167610509 := by
  unfold tailWord_6858028
  simp only [CollatzResearch.WordTrace]
  refine ⟨125066415199271644389451369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166755220265695525852601825 125066415199271644389451369)
  ·
    refine ⟨93799811399453733292088527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125066415199271644389451369 93799811399453733292088527)
    ·
      refine ⟨140699717099180599938132791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93799811399453733292088527 140699717099180599938132791)
      ·
        refine ⟨211049575648770899907199187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140699717099180599938132791 211049575648770899907199187)
        ·
          refine ⟨316574363473156349860798781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211049575648770899907199187 316574363473156349860798781)
          ·
            refine ⟨118715386302433631197799543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316574363473156349860798781 118715386302433631197799543)
            ·
              refine ⟨178073079453650446796699315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118715386302433631197799543 178073079453650446796699315)
              ·
                refine ⟨267109619180475670195048973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178073079453650446796699315 267109619180475670195048973)
                ·
                  refine ⟨100166107192678376323143365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267109619180475670195048973 100166107192678376323143365)
                  ·
                    refine ⟨18781145098627195560589381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100166107192678376323143365 18781145098627195560589381)
                    ·
                      refine ⟨3521464705992599167610509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18781145098627195560589381 3521464705992599167610509)
                      ·
                        rfl

theorem cell23_6858028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_6858028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858028 prefixEnd_6858028 := by exact prefixLift 6858028
  have htrace : WordTrace (prefixWord ++ tailWord_6858028) baseStart_6858028 baseEnd_6858028 := by
    simpa [prefixWord, tailWord_6858028, baseEnd_6858028] using wordTrace_append hprefix tailTrace_6858028
  have hstable : (prefixWord ++ tailWord_6858028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858028).length < 2 ^ (prefixWord ++ tailWord_6858028).sum := by decide
  have hdescent : baseEnd_6858028 < baseStart_6858028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858032 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 4, 2, 2]
def baseStart_6858032 : Nat := 118140960795 + 6858032 * 2 ^ 59
def prefixEnd_6858032 : Nat := 4983230072969 + 3 ^ 40 * 6858032 * 2
def baseEnd_6858032 : Nat := 3521466759915217151960491

theorem tailTrace_6858032 : CollatzResearch.WordTrace tailWord_6858032 prefixEnd_6858032 3521466759915217151960491 := by
  unfold tailWord_6858032
  simp only [CollatzResearch.WordTrace]
  refine ⟨125066488145264398731024175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166755317527019198308032233 125066488145264398731024175)
  ·
    refine ⟨187599732217896598096536263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125066488145264398731024175 187599732217896598096536263)
    ·
      refine ⟨281399598326844897144804395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187599732217896598096536263 281399598326844897144804395)
      ·
        refine ⟨422099397490267345717206593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281399598326844897144804395 422099397490267345717206593)
        ·
          refine ⟨316574548117700509287904945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422099397490267345717206593 316574548117700509287904945)
          ·
            refine ⟨237430911088275381965928709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316574548117700509287904945 237430911088275381965928709)
            ·
              refine ⟨44518295829051634118611633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237430911088275381965928709 44518295829051634118611633)
              ·
                refine ⟨33388721871788725588958725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44518295829051634118611633 33388721871788725588958725)
                ·
                  refine ⟨6260385350960386047929761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33388721871788725588958725 6260385350960386047929761)
                  ·
                    refine ⟨4695289013220289535947321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6260385350960386047929761 4695289013220289535947321)
                    ·
                      refine ⟨3521466759915217151960491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4695289013220289535947321 3521466759915217151960491)
                      ·
                        rfl

theorem cell23_6858032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4, 2, 2].length) (baseStart_6858032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858032 prefixEnd_6858032 := by exact prefixLift 6858032
  have htrace : WordTrace (prefixWord ++ tailWord_6858032) baseStart_6858032 baseEnd_6858032 := by
    simpa [prefixWord, tailWord_6858032, baseEnd_6858032] using wordTrace_append hprefix tailTrace_6858032
  have hstable : (prefixWord ++ tailWord_6858032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858032).length < 2 ^ (prefixWord ++ tailWord_6858032).sum := by decide
  have hdescent : baseEnd_6858032 < baseStart_6858032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858055 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 7]
def baseStart_6858055 : Nat := 118140960795 + 6858055 * 2 ^ 59
def prefixEnd_6858055 : Nat := 4983230072969 + 3 ^ 40 * 6858055 * 2
def baseEnd_6858055 : Nat := 391275396663363395774765

theorem tailTrace_6858055 : CollatzResearch.WordTrace tailWord_6858055 prefixEnd_6858055 391275396663363395774765 := by
  unfold tailWord_6858055
  simp only [CollatzResearch.WordTrace]
  refine ⟨250133815169445472390135619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166755876779630314926757079 250133815169445472390135619)
  ·
    refine ⟨375200722754168208585203429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250133815169445472390135619 375200722754168208585203429)
    ·
      refine ⟨70350135516406539109725643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375200722754168208585203429 70350135516406539109725643)
      ·
        refine ⟨105525203274609808664588465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70350135516406539109725643 105525203274609808664588465)
        ·
          refine ⟨79143902455957356498441349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105525203274609808664588465 79143902455957356498441349)
          ·
            refine ⟨14839481710492004343457753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79143902455957356498441349 14839481710492004343457753)
            ·
              refine ⟨11129611282869003257593315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14839481710492004343457753 11129611282869003257593315)
              ·
                refine ⟨16694416924303504886389973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11129611282869003257593315 16694416924303504886389973)
                ·
                  refine ⟨391275396663363395774765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16694416924303504886389973 391275396663363395774765)
                  ·
                    rfl

theorem cell23_6858055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 7].length) (baseStart_6858055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858055 prefixEnd_6858055 := by exact prefixLift 6858055
  have htrace : WordTrace (prefixWord ++ tailWord_6858055) baseStart_6858055 baseEnd_6858055 := by
    simpa [prefixWord, tailWord_6858055, baseEnd_6858055] using wordTrace_append hprefix tailTrace_6858055
  have hstable : (prefixWord ++ tailWord_6858055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858055).length < 2 ^ (prefixWord ++ tailWord_6858055).sum := by decide
  have hdescent : baseEnd_6858055 < baseStart_6858055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858065 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 2, 3, 3]
def baseStart_6858065 : Nat := 118140960795 + 6858065 * 2 ^ 59
def prefixEnd_6858065 : Nat := 4983230072969 + 3 ^ 40 * 6858065 * 2
def baseEnd_6858065 : Nat := 3521483704776815522847839

theorem tailTrace_6858065 : CollatzResearch.WordTrace tailWord_6858065 prefixEnd_6858065 3521483704776815522847839 := by
  unfold tailWord_6858065
  simp only [CollatzResearch.WordTrace]
  refine ⟨250134179899409244097999649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166756119932939496065333099 250134179899409244097999649)
  ·
    refine ⟨187600634924556933073499737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250134179899409244097999649 187600634924556933073499737)
    ·
      refine ⟨140700476193417699805124803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187600634924556933073499737 140700476193417699805124803)
      ·
        refine ⟨211050714290126549707687205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140700476193417699805124803 211050714290126549707687205)
        ·
          refine ⟨39572008929398728070191351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211050714290126549707687205 39572008929398728070191351)
          ·
            refine ⟨59358013394098092105287027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39572008929398728070191351 59358013394098092105287027)
            ·
              refine ⟨89037020091147138157930541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59358013394098092105287027 89037020091147138157930541)
              ·
                refine ⟨33388882534180176809223953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89037020091147138157930541 33388882534180176809223953)
                ·
                  refine ⟨25041661900635132606917965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33388882534180176809223953 25041661900635132606917965)
                  ·
                    refine ⟨9390623212738174727594237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25041661900635132606917965 9390623212738174727594237)
                    ·
                      refine ⟨3521483704776815522847839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9390623212738174727594237 3521483704776815522847839)
                      ·
                        rfl

theorem cell23_6858065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_6858065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858065 prefixEnd_6858065 := by exact prefixLift 6858065
  have htrace : WordTrace (prefixWord ++ tailWord_6858065) baseStart_6858065 baseEnd_6858065 := by
    simpa [prefixWord, tailWord_6858065, baseEnd_6858065] using wordTrace_append hprefix tailTrace_6858065
  have hstable : (prefixWord ++ tailWord_6858065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858065).length < 2 ^ (prefixWord ++ tailWord_6858065).sum := by decide
  have hdescent : baseEnd_6858065 < baseStart_6858065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858085 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_6858085 : Nat := 118140960795 + 6858085 * 2 ^ 59
def prefixEnd_6858085 : Nat := 4983230072969 + 3 ^ 40 * 6858085 * 2
def baseEnd_6858085 : Nat := 1173831324796635148199249

theorem tailTrace_6858085 : CollatzResearch.WordTrace tailWord_6858085 prefixEnd_6858085 1173831324796635148199249 := by
  unfold tailWord_6858085
  simp only [CollatzResearch.WordTrace]
  refine ⟨250134909359336787513727709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166756606239557858342485139 250134909359336787513727709)
  ·
    refine ⟨93800591009751295317647891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250134909359336787513727709 93800591009751295317647891)
    ·
      refine ⟨140700886514626942976471837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93800591009751295317647891 140700886514626942976471837)
      ·
        refine ⟨52762832442985103616176939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140700886514626942976471837 52762832442985103616176939)
        ·
          refine ⟨79144248664477655424265409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52762832442985103616176939 79144248664477655424265409)
          ·
            refine ⟨59358186498358241568199057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79144248664477655424265409 59358186498358241568199057)
            ·
              refine ⟨44518639873768681176149293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59358186498358241568199057 44518639873768681176149293)
              ·
                refine ⟨16694489952663255441055985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44518639873768681176149293 16694489952663255441055985)
                ·
                  refine ⟨12520867464497441580791989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16694489952663255441055985 12520867464497441580791989)
                  ·
                    refine ⟨1173831324796635148199249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12520867464497441580791989 1173831324796635148199249)
                    ·
                      rfl

theorem cell23_6858085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_6858085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858085 prefixEnd_6858085 := by exact prefixLift 6858085
  have htrace : WordTrace (prefixWord ++ tailWord_6858085) baseStart_6858085 baseEnd_6858085 := by
    simpa [prefixWord, tailWord_6858085, baseEnd_6858085] using wordTrace_append hprefix tailTrace_6858085
  have hstable : (prefixWord ++ tailWord_6858085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858085).length < 2 ^ (prefixWord ++ tailWord_6858085).sum := by decide
  have hdescent : baseEnd_6858085 < baseStart_6858085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858105 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 4]
def baseStart_6858105 : Nat := 118140960795 + 6858105 * 2 ^ 59
def prefixEnd_6858105 : Nat := 4983230072969 + 3 ^ 40 * 6858105 * 2
def baseEnd_6858105 : Nat := 3521504244002995366347655

theorem tailTrace_6858105 : CollatzResearch.WordTrace tailWord_6858105 prefixEnd_6858105 3521504244002995366347655 := by
  unfold tailWord_6858105
  simp only [CollatzResearch.WordTrace]
  refine ⟨250135638819264330929455769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166757092546176220619637179 250135638819264330929455769)
  ·
    refine ⟨187601729114448248197091827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250135638819264330929455769 187601729114448248197091827)
    ·
      refine ⟨281402593671672372295637741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187601729114448248197091827 281402593671672372295637741)
      ·
        refine ⟨105525972626877139610864153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281402593671672372295637741 105525972626877139610864153)
        ·
          refine ⟨79144479470157854708148115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105525972626877139610864153 79144479470157854708148115)
          ·
            refine ⟨118716719205236782062222173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79144479470157854708148115 118716719205236782062222173)
            ·
              refine ⟨44518769701963793273333315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118716719205236782062222173 44518769701963793273333315)
              ·
                refine ⟨66778154552945689909999973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44518769701963793273333315 66778154552945689909999973)
                ·
                  refine ⟨12520903978677316858124995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66778154552945689909999973 12520903978677316858124995)
                  ·
                    refine ⟨18781355968015975287187493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12520903978677316858124995 18781355968015975287187493)
                    ·
                      refine ⟨3521504244002995366347655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18781355968015975287187493 3521504244002995366347655)
                      ·
                        rfl

theorem cell23_6858105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_6858105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858105 prefixEnd_6858105 := by exact prefixLift 6858105
  have htrace : WordTrace (prefixWord ++ tailWord_6858105) baseStart_6858105 baseEnd_6858105 := by
    simpa [prefixWord, tailWord_6858105, baseEnd_6858105] using wordTrace_append hprefix tailTrace_6858105
  have hstable : (prefixWord ++ tailWord_6858105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858105).length < 2 ^ (prefixWord ++ tailWord_6858105).sum := by decide
  have hdescent : baseEnd_6858105 < baseStart_6858105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858209 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 1, 5]
def baseStart_6858209 : Nat := 118140960795 + 6858209 * 2 ^ 59
def prefixEnd_6858209 : Nat := 4983230072969 + 3 ^ 40 * 6858209 * 2
def baseEnd_6858209 : Nat := 1173852548663687653149059

theorem tailTrace_6858209 : CollatzResearch.WordTrace tailWord_6858209 prefixEnd_6858209 1173852548663687653149059 := by
  unfold tailWord_6858209
  simp only [CollatzResearch.WordTrace]
  refine ⟨250139432010887556691241681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166759621340591704460827787 250139432010887556691241681)
  ·
    refine ⟨187604574008165667518431261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250139432010887556691241681 187604574008165667518431261)
    ·
      refine ⟨70351715253062125319411723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187604574008165667518431261 70351715253062125319411723)
      ·
        refine ⟨105527572879593187979117585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70351715253062125319411723 105527572879593187979117585)
        ·
          refine ⟨79145679659694890984338189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105527572879593187979117585 79145679659694890984338189)
          ·
            refine ⟨29679629872385584119126821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79145679659694890984338189 29679629872385584119126821)
            ·
              refine ⟨5564930601072297022336279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29679629872385584119126821 5564930601072297022336279)
              ·
                refine ⟨8347395901608445533504419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564930601072297022336279 8347395901608445533504419)
                ·
                  refine ⟨12521093852412668300256629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8347395901608445533504419 12521093852412668300256629)
                  ·
                    refine ⟨1173852548663687653149059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12521093852412668300256629 1173852548663687653149059)
                    ·
                      rfl

theorem cell23_6858209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_6858209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858209 prefixEnd_6858209 := by exact prefixLift 6858209
  have htrace : WordTrace (prefixWord ++ tailWord_6858209) baseStart_6858209 baseEnd_6858209 := by
    simpa [prefixWord, tailWord_6858209, baseEnd_6858209] using wordTrace_append hprefix tailTrace_6858209
  have hstable : (prefixWord ++ tailWord_6858209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858209).length < 2 ^ (prefixWord ++ tailWord_6858209).sum := by decide
  have hdescent : baseEnd_6858209 < baseStart_6858209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858212 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 1, 8, 2]
def baseStart_6858212 : Nat := 118140960795 + 6858212 * 2 ^ 59
def prefixEnd_6858212 : Nat := 4983230072969 + 3 ^ 40 * 6858212 * 2
def baseEnd_6858212 : Nat := 3521559186433026447709663

theorem tailTrace_6858212 : CollatzResearch.WordTrace tailWord_6858212 prefixEnd_6858212 3521559186433026447709663 := by
  unfold tailWord_6858212
  simp only [CollatzResearch.WordTrace]
  refine ⟨125069770714938344101800445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166759694286584458802400593 125069770714938344101800445)
  ·
    refine ⟨46901164018101879038175167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125069770714938344101800445 46901164018101879038175167)
    ·
      refine ⟨70351746027152818557262751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46901164018101879038175167 70351746027152818557262751)
      ·
        refine ⟨105527619040729227835894127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70351746027152818557262751 105527619040729227835894127)
        ·
          refine ⟨158291428561093841753841191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105527619040729227835894127 158291428561093841753841191)
          ·
            refine ⟨237437142841640762630761787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158291428561093841753841191 237437142841640762630761787)
            ·
              refine ⟨356155714262461143946142681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237437142841640762630761787 356155714262461143946142681)
              ·
                refine ⟨267116785696845857959607011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356155714262461143946142681 267116785696845857959607011)
                ·
                  refine ⟨400675178545268786939410517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267116785696845857959607011 400675178545268786939410517)
                  ·
                    refine ⟨4695412248577368596946217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 400675178545268786939410517 4695412248577368596946217)
                    ·
                      refine ⟨3521559186433026447709663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4695412248577368596946217 3521559186433026447709663)
                      ·
                        rfl

theorem cell23_6858212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_6858212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858212 prefixEnd_6858212 := by exact prefixLift 6858212
  have htrace : WordTrace (prefixWord ++ tailWord_6858212) baseStart_6858212 baseEnd_6858212 := by
    simpa [prefixWord, tailWord_6858212, baseEnd_6858212] using wordTrace_append hprefix tailTrace_6858212
  have hstable : (prefixWord ++ tailWord_6858212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858212).length < 2 ^ (prefixWord ++ tailWord_6858212).sum := by decide
  have hdescent : baseEnd_6858212 < baseStart_6858212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858232 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_6858232 : Nat := 118140960795 + 6858232 * 2 ^ 59
def prefixEnd_6858232 : Nat := 4983230072969 + 3 ^ 40 * 6858232 * 2
def baseEnd_6858232 : Nat := 3521569456046116369459571

theorem tailTrace_6858232 : CollatzResearch.WordTrace tailWord_6858232 prefixEnd_6858232 3521569456046116369459571 := by
  unfold tailWord_6858232
  simp only [CollatzResearch.WordTrace]
  refine ⟨125070135444902115809664475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166760180593202821079552633 125070135444902115809664475)
  ·
    refine ⟨187605203167353173714496713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125070135444902115809664475 187605203167353173714496713)
    ·
      refine ⟨140703902375514880285872535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187605203167353173714496713 140703902375514880285872535)
      ·
        refine ⟨211055853563272320428808803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140703902375514880285872535 211055853563272320428808803)
        ·
          refine ⟨316583780344908480643213205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211055853563272320428808803 316583780344908480643213205)
          ·
            refine ⟨14839864703667585030150619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 316583780344908480643213205 14839864703667585030150619)
            ·
              refine ⟨22259797055501377545225929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14839864703667585030150619 22259797055501377545225929)
              ·
                refine ⟨16694847791626033158919447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22259797055501377545225929 16694847791626033158919447)
                ·
                  refine ⟨25042271687439049738379171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16694847791626033158919447 25042271687439049738379171)
                  ·
                    refine ⟨37563407531158574607568757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25042271687439049738379171 37563407531158574607568757)
                    ·
                      refine ⟨3521569456046116369459571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37563407531158574607568757 3521569456046116369459571)
                      ·
                        rfl

theorem cell23_6858232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_6858232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858232 prefixEnd_6858232 := by exact prefixLift 6858232
  have htrace : WordTrace (prefixWord ++ tailWord_6858232) baseStart_6858232 baseEnd_6858232 := by
    simpa [prefixWord, tailWord_6858232, baseEnd_6858232] using wordTrace_append hprefix tailTrace_6858232
  have hstable : (prefixWord ++ tailWord_6858232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858232).length < 2 ^ (prefixWord ++ tailWord_6858232).sum := by decide
  have hdescent : baseEnd_6858232 < baseStart_6858232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858249 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 1, 2, 3]
def baseStart_6858249 : Nat := 118140960795 + 6858249 * 2 ^ 59
def prefixEnd_6858249 : Nat := 4983230072969 + 3 ^ 40 * 6858249 * 2
def baseEnd_6858249 : Nat := 3521578185217242802946993

theorem tailTrace_6858249 : CollatzResearch.WordTrace tailWord_6858249 prefixEnd_6858249 3521578185217242802946993 := by
  unfold tailWord_6858249
  simp only [CollatzResearch.WordTrace]
  refine ⟨250140890930742643522697801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166760593953828429015131867 250140890930742643522697801)
  ·
    refine ⟨187605668198056982642023351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250140890930742643522697801 187605668198056982642023351)
    ·
      refine ⟨281408502297085473963035027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187605668198056982642023351 281408502297085473963035027)
      ·
        refine ⟨422112753445628210944552541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281408502297085473963035027 422112753445628210944552541)
        ·
          refine ⟨158292282542110579104207203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422112753445628210944552541 158292282542110579104207203)
          ·
            refine ⟨237438423813165868656310805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158292282542110579104207203 237438423813165868656310805)
            ·
              refine ⟨11129926116242150093264569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237438423813165868656310805 11129926116242150093264569)
              ·
                refine ⟨8347444587181612569948427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11129926116242150093264569 8347444587181612569948427)
                ·
                  refine ⟨12521166880772418854922641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8347444587181612569948427 12521166880772418854922641)
                  ·
                    refine ⟨9390875160579314141191981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12521166880772418854922641 9390875160579314141191981)
                    ·
                      refine ⟨3521578185217242802946993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9390875160579314141191981 3521578185217242802946993)
                      ·
                        rfl

theorem cell23_6858249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 2, 3].length) (baseStart_6858249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858249 prefixEnd_6858249 := by exact prefixLift 6858249
  have htrace : WordTrace (prefixWord ++ tailWord_6858249) baseStart_6858249 baseEnd_6858249 := by
    simpa [prefixWord, tailWord_6858249, baseEnd_6858249] using wordTrace_append hprefix tailTrace_6858249
  have hstable : (prefixWord ++ tailWord_6858249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858249).length < 2 ^ (prefixWord ++ tailWord_6858249).sum := by decide
  have hdescent : baseEnd_6858249 < baseStart_6858249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858252 : List Nat := [2, 2, 1, 2, 5, 1, 1, 9]
def baseStart_6858252 : Nat := 118140960795 + 6858252 * 2 ^ 59
def prefixEnd_6858252 : Nat := 4983230072969 + 3 ^ 40 * 6858252 * 2
def baseEnd_6858252 : Nat := 130428878728118751526277

theorem tailTrace_6858252 : CollatzResearch.WordTrace tailWord_6858252 prefixEnd_6858252 130428878728118751526277 := by
  unfold tailWord_6858252
  simp only [CollatzResearch.WordTrace]
  refine ⟨125070500174865887517528505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166760666899821183356704673 125070500174865887517528505)
  ·
    refine ⟨93802875131149415638146379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125070500174865887517528505 93802875131149415638146379)
    ·
      refine ⟨140704312696724123457219569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93802875131149415638146379 140704312696724123457219569)
      ·
        refine ⟨105528234522543092592914677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140704312696724123457219569 105528234522543092592914677)
        ·
          refine ⟨9893271986488414930585751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105528234522543092592914677 9893271986488414930585751)
          ·
            refine ⟨14839907979732622395878627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9893271986488414930585751 14839907979732622395878627)
            ·
              refine ⟨22259861969598933593817941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14839907979732622395878627 22259861969598933593817941)
              ·
                refine ⟨130428878728118751526277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22259861969598933593817941 130428878728118751526277)
                ·
                  rfl

theorem cell23_6858252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 9].length) (baseStart_6858252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858252 prefixEnd_6858252 := by exact prefixLift 6858252
  have htrace : WordTrace (prefixWord ++ tailWord_6858252) baseStart_6858252 baseEnd_6858252 := by
    simpa [prefixWord, tailWord_6858252, baseEnd_6858252] using wordTrace_append hprefix tailTrace_6858252
  have hstable : (prefixWord ++ tailWord_6858252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858252).length < 2 ^ (prefixWord ++ tailWord_6858252).sum := by decide
  have hdescent : baseEnd_6858252 < baseStart_6858252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858280 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_6858280 : Nat := 118140960795 + 6858280 * 2 ^ 59
def prefixEnd_6858280 : Nat := 4983230072969 + 3 ^ 40 * 6858280 * 2
def baseEnd_6858280 : Nat := 3521594103117532181659351

theorem tailTrace_6858280 : CollatzResearch.WordTrace tailWord_6858280 prefixEnd_6858280 3521594103117532181659351 := by
  unfold tailWord_6858280
  simp only [CollatzResearch.WordTrace]
  refine ⟨125071010796815167908538147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166761347729086890544717529 125071010796815167908538147)
  ·
    refine ⟨187606516195222751862807221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125071010796815167908538147 187606516195222751862807221)
    ·
      refine ⟨17588110893302132987138177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187606516195222751862807221 17588110893302132987138177)
      ·
        refine ⟨13191083169976599740353633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17588110893302132987138177 13191083169976599740353633)
        ·
          refine ⟨9893312377482449805265225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13191083169976599740353633 9893312377482449805265225)
          ·
            refine ⟨7419984283111837353948919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9893312377482449805265225 7419984283111837353948919)
            ·
              refine ⟨11129976424667756030923379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419984283111837353948919 11129976424667756030923379)
              ·
                refine ⟨16694964637001634046385069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11129976424667756030923379 16694964637001634046385069)
                ·
                  refine ⟨6260611738875612767394401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16694964637001634046385069 6260611738875612767394401)
                  ·
                    refine ⟨4695458804156709575545801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6260611738875612767394401 4695458804156709575545801)
                    ·
                      refine ⟨3521594103117532181659351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4695458804156709575545801 3521594103117532181659351)
                      ·
                        rfl

theorem cell23_6858280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_6858280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858280 prefixEnd_6858280 := by exact prefixLift 6858280
  have htrace : WordTrace (prefixWord ++ tailWord_6858280) baseStart_6858280 baseEnd_6858280 := by
    simpa [prefixWord, tailWord_6858280, baseEnd_6858280] using wordTrace_append hprefix tailTrace_6858280
  have hstable : (prefixWord ++ tailWord_6858280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858280).length < 2 ^ (prefixWord ++ tailWord_6858280).sum := by decide
  have hdescent : baseEnd_6858280 < baseStart_6858280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858282 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_6858282 : Nat := 118140960795 + 6858282 * 2 ^ 59
def prefixEnd_6858282 : Nat := 4983230072969 + 3 ^ 40 * 6858282 * 2
def baseEnd_6858282 : Nat := 1173865043359613724611447

theorem tailTrace_6858282 : CollatzResearch.WordTrace tailWord_6858282 prefixEnd_6858282 1173865043359613724611447 := by
  unfold tailWord_6858282
  simp only [CollatzResearch.WordTrace]
  refine ⟨62535523634905772539662275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166761396359748726772432733 62535523634905772539662275)
  ·
    refine ⟨93803285452358658809493413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62535523634905772539662275 93803285452358658809493413)
    ·
      refine ⟨17588116022317248526780015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93803285452358658809493413 17588116022317248526780015)
      ·
        refine ⟨26382174033475872790170023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17588116022317248526780015 26382174033475872790170023)
        ·
          refine ⟨39573261050213809185255035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26382174033475872790170023 39573261050213809185255035)
          ·
            refine ⟨59359891575320713777882553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39573261050213809185255035 59359891575320713777882553)
            ·
              refine ⟨44519918681490535333411915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59359891575320713777882553 44519918681490535333411915)
              ·
                refine ⟨66779878022235803000117873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44519918681490535333411915 66779878022235803000117873)
                ·
                  refine ⟨50084908516676852250088405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66779878022235803000117873 50084908516676852250088405)
                  ·
                    refine ⟨1173865043359613724611447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50084908516676852250088405 1173865043359613724611447)
                    ·
                      rfl

theorem cell23_6858282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_6858282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858282 prefixEnd_6858282 := by exact prefixLift 6858282
  have htrace : WordTrace (prefixWord ++ tailWord_6858282) baseStart_6858282 baseEnd_6858282 := by
    simpa [prefixWord, tailWord_6858282, baseEnd_6858282] using wordTrace_append hprefix tailTrace_6858282
  have hstable : (prefixWord ++ tailWord_6858282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858282).length < 2 ^ (prefixWord ++ tailWord_6858282).sum := by decide
  have hdescent : baseEnd_6858282 < baseStart_6858282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858289 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 3, 3, 2]
def baseStart_6858289 : Nat := 118140960795 + 6858289 * 2 ^ 59
def prefixEnd_6858289 : Nat := 4983230072969 + 3 ^ 40 * 6858289 * 2
def baseEnd_6858289 : Nat := 3521598724443422646446809

theorem tailTrace_6858289 : CollatzResearch.WordTrace tailWord_6858289 prefixEnd_6858289 3521598724443422646446809 := by
  unfold tailWord_6858289
  simp only [CollatzResearch.WordTrace]
  refine ⟨250142349850597730354153921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166761566567065153569435947 250142349850597730354153921)
  ·
    refine ⟨187606762387948297765615441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250142349850597730354153921 187606762387948297765615441)
    ·
      refine ⟨140705071790961223324211581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187606762387948297765615441 140705071790961223324211581)
      ·
        refine ⟨52764401921610458746579343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140705071790961223324211581 52764401921610458746579343)
        ·
          refine ⟨79146602882415688119869015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52764401921610458746579343 79146602882415688119869015)
          ·
            refine ⟨118719904323623532179803523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79146602882415688119869015 118719904323623532179803523)
            ·
              refine ⟨178079856485435298269705285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118719904323623532179803523 178079856485435298269705285)
              ·
                refine ⟨33389973091019118425569741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178079856485435298269705285 33389973091019118425569741)
                ·
                  refine ⟨12521239909132169409588653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33389973091019118425569741 12521239909132169409588653)
                  ·
                    refine ⟨4695464965924563528595745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12521239909132169409588653 4695464965924563528595745)
                    ·
                      refine ⟨3521598724443422646446809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4695464965924563528595745 3521598724443422646446809)
                      ·
                        rfl

theorem cell23_6858289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_6858289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858289 prefixEnd_6858289 := by exact prefixLift 6858289
  have htrace : WordTrace (prefixWord ++ tailWord_6858289) baseStart_6858289 baseEnd_6858289 := by
    simpa [prefixWord, tailWord_6858289, baseEnd_6858289] using wordTrace_append hprefix tailTrace_6858289
  have hstable : (prefixWord ++ tailWord_6858289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858289).length < 2 ^ (prefixWord ++ tailWord_6858289).sum := by decide
  have hdescent : baseEnd_6858289 < baseStart_6858289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858296 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 2, 1, 3]
def baseStart_6858296 : Nat := 118140960795 + 6858296 * 2 ^ 59
def prefixEnd_6858296 : Nat := 4983230072969 + 3 ^ 40 * 6858296 * 2
def baseEnd_6858296 : Nat := 3521602318808004119059277

theorem tailTrace_6858296 : CollatzResearch.WordTrace tailWord_6858296 prefixEnd_6858296 3521602318808004119059277 := by
  unfold tailWord_6858296
  simp only [CollatzResearch.WordTrace]
  refine ⟨125071302580786185274829371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166761736774381580366439161 125071302580786185274829371)
  ·
    refine ⟨187606953871179277912244057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125071302580786185274829371 187606953871179277912244057)
    ·
      refine ⟨140705215403384458434183043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187606953871179277912244057 140705215403384458434183043)
      ·
        refine ⟨211057823105076687651274565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140705215403384458434183043 211057823105076687651274565)
        ·
          refine ⟨39573341832201878934613981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211057823105076687651274565 39573341832201878934613981)
          ·
            refine ⟨14840003187075704600480243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39573341832201878934613981 14840003187075704600480243)
            ·
              refine ⟨22260004780613556900720365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14840003187075704600480243 22260004780613556900720365)
              ·
                refine ⟨8347501792730083837770137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22260004780613556900720365 8347501792730083837770137)
                ·
                  refine ⟨6260626344547562878327603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8347501792730083837770137 6260626344547562878327603)
                  ·
                    refine ⟨9390939516821344317491405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6260626344547562878327603 9390939516821344317491405)
                    ·
                      refine ⟨3521602318808004119059277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9390939516821344317491405 3521602318808004119059277)
                      ·
                        rfl

theorem cell23_6858296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_6858296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858296 prefixEnd_6858296 := by exact prefixLift 6858296
  have htrace : WordTrace (prefixWord ++ tailWord_6858296) baseStart_6858296 baseEnd_6858296 := by
    simpa [prefixWord, tailWord_6858296, baseEnd_6858296] using wordTrace_append hprefix tailTrace_6858296
  have hstable : (prefixWord ++ tailWord_6858296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858296).length < 2 ^ (prefixWord ++ tailWord_6858296).sum := by decide
  have hdescent : baseEnd_6858296 < baseStart_6858296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858409 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 6, 4, 2]
def baseStart_6858409 : Nat := 118140960795 + 6858409 * 2 ^ 59
def prefixEnd_6858409 : Nat := 4983230072969 + 3 ^ 40 * 6858409 * 2
def baseEnd_6858409 : Nat := 3521660342121962176946257

theorem tailTrace_6858409 : CollatzResearch.WordTrace tailWord_6858409 prefixEnd_6858409 3521660342121962176946257 := by
  unfold tailWord_6858409
  simp only [CollatzResearch.WordTrace]
  refine ⟨250146726610162990848522281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166764484406775327232348187 250146726610162990848522281)
  ·
    refine ⟨187610044957622243136391711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250146726610162990848522281 187610044957622243136391711)
    ·
      refine ⟨281415067436433364704587567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187610044957622243136391711 281415067436433364704587567)
      ·
        refine ⟨422122601154650047056881351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281415067436433364704587567 422122601154650047056881351)
        ·
          refine ⟨633183901731975070585322027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422122601154650047056881351 633183901731975070585322027)
          ·
            refine ⟨949775852597962605877983041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633183901731975070585322027 949775852597962605877983041)
            ·
              refine ⟨712331889448471954408487281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949775852597962605877983041 712331889448471954408487281)
              ·
                refine ⟨534248917086353965806365461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712331889448471954408487281 534248917086353965806365461)
                ·
                  refine ⟨25042917988422842147173381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 534248917086353965806365461 25042917988422842147173381)
                  ·
                    refine ⟨4695547122829282902595009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25042917988422842147173381 4695547122829282902595009)
                    ·
                      refine ⟨3521660342121962176946257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4695547122829282902595009 3521660342121962176946257)
                      ·
                        rfl

theorem cell23_6858409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 4, 2].length) (baseStart_6858409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858409 prefixEnd_6858409 := by exact prefixLift 6858409
  have htrace : WordTrace (prefixWord ++ tailWord_6858409) baseStart_6858409 baseEnd_6858409 := by
    simpa [prefixWord, tailWord_6858409, baseEnd_6858409] using wordTrace_append hprefix tailTrace_6858409
  have hstable : (prefixWord ++ tailWord_6858409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858409).length < 2 ^ (prefixWord ++ tailWord_6858409).sum := by decide
  have hdescent : baseEnd_6858409 < baseStart_6858409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858419 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 3, 4]
def baseStart_6858419 : Nat := 118140960795 + 6858419 * 2 ^ 59
def prefixEnd_6858419 : Nat := 4983230072969 + 3 ^ 40 * 6858419 * 2
def baseEnd_6858419 : Nat := 1173888492309502379273737

theorem tailTrace_6858419 : CollatzResearch.WordTrace tailWord_6858419 prefixEnd_6858419 1173888492309502379273737 := by
  unfold tailWord_6858419
  simp only [CollatzResearch.WordTrace]
  refine ⟨250147091340126762556386311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166764727560084508370924207 250147091340126762556386311)
  ·
    refine ⟨375220637010190143834579467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250147091340126762556386311 375220637010190143834579467)
    ·
      refine ⟨562830955515285215751869201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375220637010190143834579467 562830955515285215751869201)
      ·
        refine ⟨422123216636463911813901901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562830955515285215751869201 422123216636463911813901901)
        ·
          refine ⟨158296206238673966930213213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422123216636463911813901901 158296206238673966930213213)
          ·
            refine ⟨59361077339502737598829955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158296206238673966930213213 59361077339502737598829955)
            ·
              refine ⟨89041616009254106398244933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59361077339502737598829955 89041616009254106398244933)
              ·
                refine ⟨16695303001735144949670925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89041616009254106398244933 16695303001735144949670925)
                ·
                  refine ⟨6260738625650679356126597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16695303001735144949670925 6260738625650679356126597)
                  ·
                    refine ⟨1173888492309502379273737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6260738625650679356126597 1173888492309502379273737)
                    ·
                      rfl

theorem cell23_6858419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 4].length) (baseStart_6858419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858419 prefixEnd_6858419 := by exact prefixLift 6858419
  have htrace : WordTrace (prefixWord ++ tailWord_6858419) baseStart_6858419 baseEnd_6858419 := by
    simpa [prefixWord, tailWord_6858419, baseEnd_6858419] using wordTrace_append hprefix tailTrace_6858419
  have hstable : (prefixWord ++ tailWord_6858419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858419).length < 2 ^ (prefixWord ++ tailWord_6858419).sum := by decide
  have hdescent : baseEnd_6858419 < baseStart_6858419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858429 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_6858429 : Nat := 118140960795 + 6858429 * 2 ^ 59
def prefixEnd_6858429 : Nat := 4983230072969 + 3 ^ 40 * 6858429 * 2
def baseEnd_6858429 : Nat := 3521670611735052098696165

theorem tailTrace_6858429 : CollatzResearch.WordTrace tailWord_6858429 prefixEnd_6858429 3521670611735052098696165 := by
  unfold tailWord_6858429
  simp only [CollatzResearch.WordTrace]
  refine ⟨250147456070090534264250341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166764970713393689509500227 250147456070090534264250341)
  ·
    refine ⟨46902648013141975174546939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250147456070090534264250341 46902648013141975174546939)
    ·
      refine ⟨70353972019712962761820409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46902648013141975174546939 70353972019712962761820409)
      ·
        refine ⟨52765479014784722071365307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70353972019712962761820409 52765479014784722071365307)
        ·
          refine ⟨79148218522177083107047961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52765479014784722071365307 79148218522177083107047961)
          ·
            refine ⟨59361163891632812330285971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79148218522177083107047961 59361163891632812330285971)
            ·
              refine ⟨89041745837449218495428957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59361163891632812330285971 89041745837449218495428957)
              ·
                refine ⟨33390654689043456935785859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89041745837449218495428957 33390654689043456935785859)
                ·
                  refine ⟨50085982033565185403678789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33390654689043456935785859 50085982033565185403678789)
                  ·
                    refine ⟨9391121631293472263189773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50085982033565185403678789 9391121631293472263189773)
                    ·
                      refine ⟨3521670611735052098696165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9391121631293472263189773 3521670611735052098696165)
                      ·
                        rfl

theorem cell23_6858429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_6858429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858429 prefixEnd_6858429 := by exact prefixLift 6858429
  have htrace : WordTrace (prefixWord ++ tailWord_6858429) baseStart_6858429 baseEnd_6858429 := by
    simpa [prefixWord, tailWord_6858429, baseEnd_6858429] using wordTrace_append hprefix tailTrace_6858429
  have hstable : (prefixWord ++ tailWord_6858429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858429).length < 2 ^ (prefixWord ++ tailWord_6858429).sum := by decide
  have hdescent : baseEnd_6858429 < baseStart_6858429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858432 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 10]
def baseStart_6858432 : Nat := 118140960795 + 6858432 * 2 ^ 59
def prefixEnd_6858432 : Nat := 4983230072969 + 3 ^ 40 * 6858432 * 2
def baseEnd_6858432 : Nat := 391296905797446176328739

theorem tailTrace_6858432 : CollatzResearch.WordTrace tailWord_6858432 prefixEnd_6858432 391296905797446176328739 := by
  unfold tailWord_6858432
  simp only [CollatzResearch.WordTrace]
  refine ⟨125073782744539832888304775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166765043659386443851073033 125073782744539832888304775)
  ·
    refine ⟨187610674116809749332457163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125073782744539832888304775 187610674116809749332457163)
    ·
      refine ⟨281416011175214623998685745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187610674116809749332457163 281416011175214623998685745)
      ·
        refine ⟨211062008381410967999014309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281416011175214623998685745 211062008381410967999014309)
        ·
          refine ⟨39574126571514556499815183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211062008381410967999014309 39574126571514556499815183)
          ·
            refine ⟨59361189857271834749722775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39574126571514556499815183 59361189857271834749722775)
            ·
              refine ⟨89041784785907752124584163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59361189857271834749722775 89041784785907752124584163)
              ·
                refine ⟨133562677178861628186876245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89041784785907752124584163 133562677178861628186876245)
                ·
                  refine ⟨391296905797446176328739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 133562677178861628186876245 391296905797446176328739)
                  ·
                    rfl

theorem cell23_6858432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 10].length) (baseStart_6858432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858432 prefixEnd_6858432 := by exact prefixLift 6858432
  have htrace : WordTrace (prefixWord ++ tailWord_6858432) baseStart_6858432 baseEnd_6858432 := by
    simpa [prefixWord, tailWord_6858432, baseEnd_6858432] using wordTrace_append hprefix tailTrace_6858432
  have hstable : (prefixWord ++ tailWord_6858432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858432).length < 2 ^ (prefixWord ++ tailWord_6858432).sum := by decide
  have hdescent : baseEnd_6858432 < baseStart_6858432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858446 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_6858446 : Nat := 118140960795 + 6858446 * 2 ^ 59
def prefixEnd_6858446 : Nat := 4983230072969 + 3 ^ 40 * 6858446 * 2
def baseEnd_6858446 : Nat := 3521679340906178532183587

theorem tailTrace_6858446 : CollatzResearch.WordTrace tailWord_6858446 prefixEnd_6858446 3521679340906178532183587 := by
  unfold tailWord_6858446
  simp only [CollatzResearch.WordTrace]
  refine ⟨31268509513878618270952399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166765384074019297445079461 31268509513878618270952399)
  ·
    refine ⟨46902764270817927406428599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31268509513878618270952399 46902764270817927406428599)
    ·
      refine ⟨70354146406226891109642899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46902764270817927406428599 70354146406226891109642899)
      ·
        refine ⟨105531219609340336664464349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70354146406226891109642899 105531219609340336664464349)
        ·
          refine ⟨39574207353502626249174131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105531219609340336664464349 39574207353502626249174131)
          ·
            refine ⟨59361311030253939373761197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39574207353502626249174131 59361311030253939373761197)
            ·
              refine ⟨22260491636345227265160449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59361311030253939373761197 22260491636345227265160449)
              ·
                refine ⟨16695368727258920448870337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22260491636345227265160449 16695368727258920448870337)
                ·
                  refine ⟨12521526545444190336652753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16695368727258920448870337 12521526545444190336652753)
                  ·
                    refine ⟨9391144909083142752489565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12521526545444190336652753 9391144909083142752489565)
                    ·
                      refine ⟨3521679340906178532183587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9391144909083142752489565 3521679340906178532183587)
                      ·
                        rfl

theorem cell23_6858446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_6858446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858446 prefixEnd_6858446 := by exact prefixLift 6858446
  have htrace : WordTrace (prefixWord ++ tailWord_6858446) baseStart_6858446 baseEnd_6858446 := by
    simpa [prefixWord, tailWord_6858446, baseEnd_6858446] using wordTrace_append hprefix tailTrace_6858446
  have hstable : (prefixWord ++ tailWord_6858446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858446).length < 2 ^ (prefixWord ++ tailWord_6858446).sum := by decide
  have hdescent : baseEnd_6858446 < baseStart_6858446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858476 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 3]
def baseStart_6858476 : Nat := 118140960795 + 6858476 * 2 ^ 59
def prefixEnd_6858476 : Nat := 4983230072969 + 3 ^ 40 * 6858476 * 2
def baseEnd_6858476 : Nat := 3521694745325813414808449

theorem tailTrace_6858476 : CollatzResearch.WordTrace tailWord_6858476 prefixEnd_6858476 3521694745325813414808449 := by
  unfold tailWord_6858476
  simp only [CollatzResearch.WordTrace]
  refine ⟨125074585150460130645605641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166766113533946840860807521 125074585150460130645605641)
  ·
    refine ⟨93805938862845097984204231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125074585150460130645605641 93805938862845097984204231)
    ·
      refine ⟨140708908294267646976306347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93805938862845097984204231 140708908294267646976306347)
      ·
        refine ⟨211063362441401470464459521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140708908294267646976306347 211063362441401470464459521)
        ·
          refine ⟨158297521831051102848344641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211063362441401470464459521 158297521831051102848344641)
          ·
            refine ⟨118723141373288327136258481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158297521831051102848344641 118723141373288327136258481)
            ·
              refine ⟨89042356029966245352193861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118723141373288327136258481 89042356029966245352193861)
              ·
                refine ⟨16695441755618671003536349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89042356029966245352193861 16695441755618671003536349)
                ·
                  refine ⟨6260790658357001626326131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16695441755618671003536349 6260790658357001626326131)
                  ·
                    refine ⟨9391185987535502439489197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6260790658357001626326131 9391185987535502439489197)
                    ·
                      refine ⟨3521694745325813414808449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9391185987535502439489197 3521694745325813414808449)
                      ·
                        rfl

theorem cell23_6858476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_6858476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858476 prefixEnd_6858476 := by exact prefixLift 6858476
  have htrace : WordTrace (prefixWord ++ tailWord_6858476) baseStart_6858476 baseEnd_6858476 := by
    simpa [prefixWord, tailWord_6858476, baseEnd_6858476] using wordTrace_append hprefix tailTrace_6858476
  have hstable : (prefixWord ++ tailWord_6858476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858476).length < 2 ^ (prefixWord ++ tailWord_6858476).sum := by decide
  have hdescent : baseEnd_6858476 < baseStart_6858476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858479 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 3, 5]
def baseStart_6858479 : Nat := 118140960795 + 6858479 * 2 ^ 59
def prefixEnd_6858479 : Nat := 4983230072969 + 3 ^ 40 * 6858479 * 2
def baseEnd_6858479 : Nat := 1173898761922592301023645

theorem tailTrace_6858479 : CollatzResearch.WordTrace tailWord_6858479 prefixEnd_6858479 1173898761922592301023645 := by
  unfold tailWord_6858479
  simp only [CollatzResearch.WordTrace]
  refine ⟨250149279719909392803570491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166766186479939595202380327 250149279719909392803570491)
  ·
    refine ⟨375223919579864089205355737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250149279719909392803570491 375223919579864089205355737)
    ·
      refine ⟨281417939684898066904016803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375223919579864089205355737 281417939684898066904016803)
      ·
        refine ⟨422126909527347100356025205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281417939684898066904016803 422126909527347100356025205)
        ·
          refine ⟨39574397768188790658377363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 422126909527347100356025205 39574397768188790658377363)
          ·
            refine ⟨59361596652283185987566045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39574397768188790658377363 59361596652283185987566045)
            ·
              refine ⟨22260598744606194745337267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59361596652283185987566045 22260598744606194745337267)
              ·
                refine ⟨33390898116909292118005901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22260598744606194745337267 33390898116909292118005901)
                ·
                  refine ⟨12521586793840984544252213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33390898116909292118005901 12521586793840984544252213)
                  ·
                    refine ⟨1173898761922592301023645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12521586793840984544252213 1173898761922592301023645)
                    ·
                      rfl

theorem cell23_6858479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_6858479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858479 prefixEnd_6858479 := by exact prefixLift 6858479
  have htrace : WordTrace (prefixWord ++ tailWord_6858479) baseStart_6858479 baseEnd_6858479 := by
    simpa [prefixWord, tailWord_6858479, baseEnd_6858479] using wordTrace_append hprefix tailTrace_6858479
  have hstable : (prefixWord ++ tailWord_6858479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858479).length < 2 ^ (prefixWord ++ tailWord_6858479).sum := by decide
  have hdescent : baseEnd_6858479 < baseStart_6858479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858533 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 5, 2, 2]
def baseStart_6858533 : Nat := 118140960795 + 6858533 * 2 ^ 59
def prefixEnd_6858533 : Nat := 4983230072969 + 3 ^ 40 * 6858533 * 2
def baseEnd_6858533 : Nat := 3521724013723119691795687

theorem tailTrace_6858533 : CollatzResearch.WordTrace tailWord_6858533 prefixEnd_6858533 3521724013723119691795687 := by
  unfold tailWord_6858533
  simp only [CollatzResearch.WordTrace]
  refine ⟨250151249261713760026036253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166767499507809173350690835 250151249261713760026036253)
  ·
    refine ⟨93806718473142660009763595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250151249261713760026036253 93806718473142660009763595)
    ·
      refine ⟨140710077709713990014645393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93806718473142660009763595 140710077709713990014645393)
      ·
        refine ⟨105532558282285492510984045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140710077709713990014645393 105532558282285492510984045)
        ·
          refine ⟨39574709355857059691619017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105532558282285492510984045 39574709355857059691619017)
          ·
            refine ⟨29681032016892794768714263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39574709355857059691619017 29681032016892794768714263)
            ·
              refine ⟨44521548025339192153071395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29681032016892794768714263 44521548025339192153071395)
              ·
                refine ⟨66782322038008788229607093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44521548025339192153071395 66782322038008788229607093)
                ·
                  refine ⟨6260842691063323896525665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66782322038008788229607093 6260842691063323896525665)
                  ·
                    refine ⟨4695632018297492922394249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6260842691063323896525665 4695632018297492922394249)
                    ·
                      refine ⟨3521724013723119691795687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4695632018297492922394249 3521724013723119691795687)
                      ·
                        rfl

theorem cell23_6858533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_6858533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858533 prefixEnd_6858533 := by exact prefixLift 6858533
  have htrace : WordTrace (prefixWord ++ tailWord_6858533) baseStart_6858533 baseEnd_6858533 := by
    simpa [prefixWord, tailWord_6858533, baseEnd_6858533] using wordTrace_append hprefix tailTrace_6858533
  have hstable : (prefixWord ++ tailWord_6858533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858533).length < 2 ^ (prefixWord ++ tailWord_6858533).sum := by decide
  have hdescent : baseEnd_6858533 < baseStart_6858533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858546 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_6858546 : Nat := 118140960795 + 6858546 * 2 ^ 59
def prefixEnd_6858546 : Nat := 4983230072969 + 3 ^ 40 * 6858546 * 2
def baseEnd_6858546 : Nat := 3521730688971628140933127

theorem tailTrace_6858546 : CollatzResearch.WordTrace tailWord_6858546 prefixEnd_6858546 3521730688971628140933127 := by
  unfold tailWord_6858546
  simp only [CollatzResearch.WordTrace]
  refine ⟨62537930852666665811564873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166767815607111108830839661 62537930852666665811564873)
  ·
    refine ⟨46903448139499999358673655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62537930852666665811564873 46903448139499999358673655)
    ·
      refine ⟨70355172209249999038010483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46903448139499999358673655 70355172209249999038010483)
      ·
        refine ⟨105532758313874998557015725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70355172209249999038010483 105532758313874998557015725)
        ·
          refine ⟨39574784367703124458880897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105532758313874998557015725 39574784367703124458880897)
          ·
            refine ⟨29681088275777343344160673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39574784367703124458880897 29681088275777343344160673)
            ·
              refine ⟨22260816206833007508120505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29681088275777343344160673 22260816206833007508120505)
              ·
                refine ⟨16695612155124755631090379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22260816206833007508120505 16695612155124755631090379)
                ·
                  refine ⟨25043418232687133446635569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16695612155124755631090379 25043418232687133446635569)
                  ·
                    refine ⟨18782563674515350084976677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25043418232687133446635569 18782563674515350084976677)
                    ·
                      refine ⟨3521730688971628140933127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18782563674515350084976677 3521730688971628140933127)
                      ·
                        rfl

theorem cell23_6858546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_6858546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858546 prefixEnd_6858546 := by exact prefixLift 6858546
  have htrace : WordTrace (prefixWord ++ tailWord_6858546) baseStart_6858546 baseEnd_6858546 := by
    simpa [prefixWord, tailWord_6858546, baseEnd_6858546] using wordTrace_append hprefix tailTrace_6858546
  have hstable : (prefixWord ++ tailWord_6858546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858546).length < 2 ^ (prefixWord ++ tailWord_6858546).sum := by decide
  have hdescent : baseEnd_6858546 < baseStart_6858546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858550 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_6858550 : Nat := 118140960795 + 6858550 * 2 ^ 59
def prefixEnd_6858550 : Nat := 4983230072969 + 3 ^ 40 * 6858550 * 2
def baseEnd_6858550 : Nat := 3521732742894246125283109

theorem tailTrace_6858550 : CollatzResearch.WordTrace tailWord_6858550 prefixEnd_6858550 3521732742894246125283109 := by
  unfold tailWord_6858550
  simp only [CollatzResearch.WordTrace]
  refine ⟨15634491831415760745587819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166767912868434781286270069 15634491831415760745587819)
  ·
    refine ⟨23451737747123641118381729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15634491831415760745587819 23451737747123641118381729)
    ·
      refine ⟨17588803310342730838786297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23451737747123641118381729 17588803310342730838786297)
      ·
        refine ⟨13191602482757048129089723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17588803310342730838786297 13191602482757048129089723)
        ·
          refine ⟨19787403724135572193634585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13191602482757048129089723 19787403724135572193634585)
          ·
            refine ⟨14840552793101679145225939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19787403724135572193634585 14840552793101679145225939)
            ·
              refine ⟨22260829189652518717838909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14840552793101679145225939 22260829189652518717838909)
              ·
                refine ⟨8347810946119694519189591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22260829189652518717838909 8347810946119694519189591)
                ·
                  refine ⟨12521716419179541778784387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8347810946119694519189591 12521716419179541778784387)
                  ·
                    refine ⟨18782574628769312668176581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12521716419179541778784387 18782574628769312668176581)
                    ·
                      refine ⟨3521732742894246125283109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18782574628769312668176581 3521732742894246125283109)
                      ·
                        rfl

theorem cell23_6858550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_6858550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858550 prefixEnd_6858550 := by exact prefixLift 6858550
  have htrace : WordTrace (prefixWord ++ tailWord_6858550) baseStart_6858550 baseEnd_6858550 := by
    simpa [prefixWord, tailWord_6858550, baseEnd_6858550] using wordTrace_append hprefix tailTrace_6858550
  have hstable : (prefixWord ++ tailWord_6858550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858550).length < 2 ^ (prefixWord ++ tailWord_6858550).sum := by decide
  have hdescent : baseEnd_6858550 < baseStart_6858550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858634 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3]
def baseStart_6858634 : Nat := 118140960795 + 6858634 * 2 ^ 59
def prefixEnd_6858634 : Nat := 4983230072969 + 3 ^ 40 * 6858634 * 2
def baseEnd_6858634 : Nat := 3521775875269223796632723

theorem tailTrace_6858634 : CollatzResearch.WordTrace tailWord_6858634 prefixEnd_6858634 3521775875269223796632723 := by
  unfold tailWord_6858634
  simp only [CollatzResearch.WordTrace]
  refine ⟨62538733258586963568865739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166769955356231902850308637 62538733258586963568865739)
  ·
    refine ⟨93808099887880445353298609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62538733258586963568865739 93808099887880445353298609)
    ·
      refine ⟨70356074915910334014973957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93808099887880445353298609 70356074915910334014973957)
      ·
        refine ⟨13191764046733187627807617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70356074915910334014973957 13191764046733187627807617)
        ·
          refine ⟨9893823035049890720855713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13191764046733187627807617 9893823035049890720855713)
          ·
            refine ⟨7420367276287418040641785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9893823035049890720855713 7420367276287418040641785)
            ·
              refine ⟨5565275457215563530481339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7420367276287418040641785 5565275457215563530481339)
              ·
                refine ⟨8347913185823345295722009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565275457215563530481339 8347913185823345295722009)
                ·
                  refine ⟨6260934889367508971791507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8347913185823345295722009 6260934889367508971791507)
                  ·
                    refine ⟨9391402334051263457687261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6260934889367508971791507 9391402334051263457687261)
                    ·
                      refine ⟨3521775875269223796632723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9391402334051263457687261 3521775875269223796632723)
                      ·
                        rfl

theorem cell23_6858634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_6858634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858634 prefixEnd_6858634 := by exact prefixLift 6858634
  have htrace : WordTrace (prefixWord ++ tailWord_6858634) baseStart_6858634 baseEnd_6858634 := by
    simpa [prefixWord, tailWord_6858634, baseEnd_6858634] using wordTrace_append hprefix tailTrace_6858634
  have hstable : (prefixWord ++ tailWord_6858634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858634).length < 2 ^ (prefixWord ++ tailWord_6858634).sum := by decide
  have hdescent : baseEnd_6858634 < baseStart_6858634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858656 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 3]
def baseStart_6858656 : Nat := 118140960795 + 6858656 * 2 ^ 59
def prefixEnd_6858656 : Nat := 4983230072969 + 3 ^ 40 * 6858656 * 2
def baseEnd_6858656 : Nat := 3521787171843622710557621

theorem tailTrace_6858656 : CollatzResearch.WordTrace tailWord_6858656 prefixEnd_6858656 3521787171843622710557621 := by
  unfold tailWord_6858656
  simp only [CollatzResearch.WordTrace]
  refine ⟨125077867720134076016381911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166770490293512101355175881 125077867720134076016381911)
  ·
    refine ⟨187616801580201114024572867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125077867720134076016381911 187616801580201114024572867)
    ·
      refine ⟨281425202370301671036859301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187616801580201114024572867 281425202370301671036859301)
      ·
        refine ⟨52767225444431563319411119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281425202370301671036859301 52767225444431563319411119)
        ·
          refine ⟨79150838166647344979116679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52767225444431563319411119 79150838166647344979116679)
          ·
            refine ⟨118726257249971017468675019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79150838166647344979116679 118726257249971017468675019)
            ·
              refine ⟨178089385874956526203012529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118726257249971017468675019 178089385874956526203012529)
              ·
                refine ⟨133567039406217394652259397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178089385874956526203012529 133567039406217394652259397)
                ·
                  refine ⟨25043819888665761497298637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133567039406217394652259397 25043819888665761497298637)
                  ·
                    refine ⟨9391432458249660561486989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25043819888665761497298637 9391432458249660561486989)
                    ·
                      refine ⟨3521787171843622710557621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9391432458249660561486989 3521787171843622710557621)
                      ·
                        rfl

theorem cell23_6858656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_6858656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858656 prefixEnd_6858656 := by exact prefixLift 6858656
  have htrace : WordTrace (prefixWord ++ tailWord_6858656) baseStart_6858656 baseEnd_6858656 := by
    simpa [prefixWord, tailWord_6858656, baseEnd_6858656] using wordTrace_append hprefix tailTrace_6858656
  have hstable : (prefixWord ++ tailWord_6858656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858656).length < 2 ^ (prefixWord ++ tailWord_6858656).sum := by decide
  have hdescent : baseEnd_6858656 < baseStart_6858656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858710 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_6858710 : Nat := 118140960795 + 6858710 * 2 ^ 59
def prefixEnd_6858710 : Nat := 4983230072969 + 3 ^ 40 * 6858710 * 2
def baseEnd_6858710 : Nat := 1173938299932988499760791

theorem tailTrace_6858710 : CollatzResearch.WordTrace tailWord_6858710 prefixEnd_6858710 1173938299932988499760791 := by
  unfold tailWord_6858710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15634856561379532453451849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166771803321381679503486389 15634856561379532453451849)
  ·
    refine ⟨11726142421034649340088887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15634856561379532453451849 11726142421034649340088887)
    ·
      refine ⟨17589213631551974010133331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11726142421034649340088887 17589213631551974010133331)
      ·
        refine ⟨26383820447327961015199997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17589213631551974010133331 26383820447327961015199997)
        ·
          refine ⟨9893932667747985380699999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26383820447327961015199997 9893932667747985380699999)
          ·
            refine ⟨14840899001621978071049999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9893932667747985380699999 14840899001621978071049999)
            ·
              refine ⟨22261348502432967106574999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14840899001621978071049999 22261348502432967106574999)
              ·
                refine ⟨33392022753649450659862499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22261348502432967106574999 33392022753649450659862499)
                ·
                  refine ⟨50088034130474175989793749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33392022753649450659862499 50088034130474175989793749)
                  ·
                    refine ⟨1173938299932988499760791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50088034130474175989793749 1173938299932988499760791)
                    ·
                      rfl

theorem cell23_6858710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_6858710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858710 prefixEnd_6858710 := by exact prefixLift 6858710
  have htrace : WordTrace (prefixWord ++ tailWord_6858710) baseStart_6858710 baseEnd_6858710 := by
    simpa [prefixWord, tailWord_6858710, baseEnd_6858710] using wordTrace_append hprefix tailTrace_6858710
  have hstable : (prefixWord ++ tailWord_6858710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858710).length < 2 ^ (prefixWord ++ tailWord_6858710).sum := by decide
  have hdescent : baseEnd_6858710 < baseStart_6858710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858713 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 4]
def baseStart_6858713 : Nat := 118140960795 + 6858713 * 2 ^ 59
def prefixEnd_6858713 : Nat := 4983230072969 + 3 ^ 40 * 6858713 * 2
def baseEnd_6858713 : Nat := 3521816440240928987544859

theorem tailTrace_6858713 : CollatzResearch.WordTrace tailWord_6858713 prefixEnd_6858713 3521816440240928987544859 := by
  unfold tailWord_6858713
  simp only [CollatzResearch.WordTrace]
  refine ⟨250157814401061650767588793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166771876267374433845059195 250157814401061650767588793)
  ·
    refine ⟨187618360800796238075691595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250157814401061650767588793 187618360800796238075691595)
    ·
      refine ⟨281427541201194357113537393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187618360800796238075691595 281427541201194357113537393)
      ·
        refine ⟨211070655900895767835153045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281427541201194357113537393 211070655900895767835153045)
        ·
          refine ⟨9893936995354489117272799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 211070655900895767835153045 9893936995354489117272799)
          ·
            refine ⟨14840905493031733675909199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9893936995354489117272799 14840905493031733675909199)
            ·
              refine ⟨22261358239547600513863799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14840905493031733675909199 22261358239547600513863799)
              ·
                refine ⟨33392037359321400770795699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22261358239547600513863799 33392037359321400770795699)
                ·
                  refine ⟨50088056038982101156193549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33392037359321400770795699 50088056038982101156193549)
                  ·
                    refine ⟨18783021014618287933572581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50088056038982101156193549 18783021014618287933572581)
                    ·
                      refine ⟨3521816440240928987544859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18783021014618287933572581 3521816440240928987544859)
                      ·
                        rfl

theorem cell23_6858713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_6858713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858713 prefixEnd_6858713 := by exact prefixLift 6858713
  have htrace : WordTrace (prefixWord ++ tailWord_6858713) baseStart_6858713 baseEnd_6858713 := by
    simpa [prefixWord, tailWord_6858713, baseEnd_6858713] using wordTrace_append hprefix tailTrace_6858713
  have hstable : (prefixWord ++ tailWord_6858713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858713).length < 2 ^ (prefixWord ++ tailWord_6858713).sum := by decide
  have hdescent : baseEnd_6858713 < baseStart_6858713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858750 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6858750 : Nat := 118140960795 + 6858750 * 2 ^ 59
def prefixEnd_6858750 : Nat := 4983230072969 + 3 ^ 40 * 6858750 * 2
def baseEnd_6858750 : Nat := 3521835439025145342782189

theorem tailTrace_6858750 : CollatzResearch.WordTrace tailWord_6858750 prefixEnd_6858750 3521835439025145342782189 := by
  unfold tailWord_6858750
  simp only [CollatzResearch.WordTrace]
  refine ⟨31269895487740950760835713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166772775934618404057790469 31269895487740950760835713)
  ·
    refine ⟨23452421615805713070626785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31269895487740950760835713 23452421615805713070626785)
    ·
      refine ⟨17589316211854284802970089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23452421615805713070626785 17589316211854284802970089)
      ·
        refine ⟨13191987158890713602227567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17589316211854284802970089 13191987158890713602227567)
        ·
          refine ⟨19787980738336070403341351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13191987158890713602227567 19787980738336070403341351)
          ·
            refine ⟨29681971107504105605012027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19787980738336070403341351 29681971107504105605012027)
            ·
              refine ⟨44522956661256158407518041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29681971107504105605012027 44522956661256158407518041)
              ·
                refine ⟨33392217495942118805638531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44522956661256158407518041 33392217495942118805638531)
                ·
                  refine ⟨50088326243913178208457797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33392217495942118805638531 50088326243913178208457797)
                  ·
                    refine ⟨9391561170733720914085837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50088326243913178208457797 9391561170733720914085837)
                    ·
                      refine ⟨3521835439025145342782189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9391561170733720914085837 3521835439025145342782189)
                      ·
                        rfl

theorem cell23_6858750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6858750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858750 prefixEnd_6858750 := by exact prefixLift 6858750
  have htrace : WordTrace (prefixWord ++ tailWord_6858750) baseStart_6858750 baseEnd_6858750 := by
    simpa [prefixWord, tailWord_6858750, baseEnd_6858750] using wordTrace_append hprefix tailTrace_6858750
  have hstable : (prefixWord ++ tailWord_6858750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858750).length < 2 ^ (prefixWord ++ tailWord_6858750).sum := by decide
  have hdescent : baseEnd_6858750 < baseStart_6858750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858783 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 1, 5]
def baseStart_6858783 : Nat := 118140960795 + 6858783 * 2 ^ 59
def prefixEnd_6858783 : Nat := 4983230072969 + 3 ^ 40 * 6858783 * 2
def baseEnd_6858783 : Nat := 1173950794628914571223179

theorem tailTrace_6858783 : CollatzResearch.WordTrace tailWord_6858783 prefixEnd_6858783 1173950794628914571223179 := by
  unfold tailWord_6858783
  simp only [CollatzResearch.WordTrace]
  refine ⟨250160367510808052722637003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166773578340538701815091335 250160367510808052722637003)
  ·
    refine ⟨375240551266212079083955505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250160367510808052722637003 375240551266212079083955505)
    ·
      refine ⟨281430413449659059312966629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375240551266212079083955505 281430413449659059312966629)
      ·
        refine ⟨52768202521811073621181243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281430413449659059312966629 52768202521811073621181243)
        ·
          refine ⟨79152303782716610431771865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52768202521811073621181243 79152303782716610431771865)
          ·
            refine ⟨59364227837037457823828899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79152303782716610431771865 59364227837037457823828899)
            ·
              refine ⟨89046341755556186735743349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59364227837037457823828899 89046341755556186735743349)
              ·
                refine ⟨8348094539583392506475939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89046341755556186735743349 8348094539583392506475939)
                ·
                  refine ⟨12522141809375088759713909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8348094539583392506475939 12522141809375088759713909)
                  ·
                    refine ⟨1173950794628914571223179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12522141809375088759713909 1173950794628914571223179)
                    ·
                      rfl

theorem cell23_6858783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 5].length) (baseStart_6858783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858783 prefixEnd_6858783 := by exact prefixLift 6858783
  have htrace : WordTrace (prefixWord ++ tailWord_6858783) baseStart_6858783 baseEnd_6858783 := by
    simpa [prefixWord, tailWord_6858783, baseEnd_6858783] using wordTrace_append hprefix tailTrace_6858783
  have hstable : (prefixWord ++ tailWord_6858783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858783).length < 2 ^ (prefixWord ++ tailWord_6858783).sum := by decide
  have hdescent : baseEnd_6858783 < baseStart_6858783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858791 : List Nat := [1, 1, 7, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6858791 : Nat := 118140960795 + 6858791 * 2 ^ 59
def prefixEnd_6858791 : Nat := 4983230072969 + 3 ^ 40 * 6858791 * 2
def baseEnd_6858791 : Nat := 1173952163910659894123167

theorem tailTrace_6858791 : CollatzResearch.WordTrace tailWord_6858791 prefixEnd_6858791 1173952163910659894123167 := by
  unfold tailWord_6858791
  simp only [CollatzResearch.WordTrace]
  refine ⟨250160659294779070088928227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166773772863186046725952151 250160659294779070088928227)
  ·
    refine ⟨375240988942168605133392341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250160659294779070088928227 375240988942168605133392341)
    ·
      refine ⟨8794710678332076682813883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 375240988942168605133392341 8794710678332076682813883)
      ·
        refine ⟨13192066017498115024220825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8794710678332076682813883 13192066017498115024220825)
        ·
          refine ⟨9894049513123586268165619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13192066017498115024220825 9894049513123586268165619)
          ·
            refine ⟨14841074269685379402248429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9894049513123586268165619 14841074269685379402248429)
            ·
              refine ⟨5565402851132017275843161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14841074269685379402248429 5565402851132017275843161)
              ·
                refine ⟨4174052138349012956882371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5565402851132017275843161 4174052138349012956882371)
                ·
                  refine ⟨6261078207523519435323557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4174052138349012956882371 6261078207523519435323557)
                  ·
                    refine ⟨1173952163910659894123167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6261078207523519435323557 1173952163910659894123167)
                    ·
                      rfl

theorem cell23_6858791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6858791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858791 prefixEnd_6858791 := by exact prefixLift 6858791
  have htrace : WordTrace (prefixWord ++ tailWord_6858791) baseStart_6858791 baseEnd_6858791 := by
    simpa [prefixWord, tailWord_6858791, baseEnd_6858791] using wordTrace_append hprefix tailTrace_6858791
  have hstable : (prefixWord ++ tailWord_6858791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858791).length < 2 ^ (prefixWord ++ tailWord_6858791).sum := by decide
  have hdescent : baseEnd_6858791 < baseStart_6858791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858796 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_6858796 : Nat := 118140960795 + 6858796 * 2 ^ 59
def prefixEnd_6858796 : Nat := 4983230072969 + 3 ^ 40 * 6858796 * 2
def baseEnd_6858796 : Nat := 1173953019711750720935659

theorem tailTrace_6858796 : CollatzResearch.WordTrace tailWord_6858796 prefixEnd_6858796 1173953019711750720935659 := by
  unfold tailWord_6858796
  simp only [CollatzResearch.WordTrace]
  refine ⟨125080420829880477971430121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166773894439840637295240161 125080420829880477971430121)
  ·
    refine ⟨93810315622410358478572591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125080420829880477971430121 93810315622410358478572591)
    ·
      refine ⟨140715473433615537717858887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93810315622410358478572591 140715473433615537717858887)
      ·
        refine ⟨211073210150423306576788331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140715473433615537717858887 211073210150423306576788331)
        ·
          refine ⟨316609815225634959865182497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211073210150423306576788331 316609815225634959865182497)
          ·
            refine ⟨237457361419226219898886873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316609815225634959865182497 237457361419226219898886873)
            ·
              refine ⟨178093021064419664924165155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237457361419226219898886873 178093021064419664924165155)
              ·
                refine ⟨267139531596629497386247733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178093021064419664924165155 267139531596629497386247733)
                ·
                  refine ⟨25044331087184015379960725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 267139531596629497386247733 25044331087184015379960725)
                  ·
                    refine ⟨1173953019711750720935659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25044331087184015379960725 1173953019711750720935659)
                    ·
                      rfl

theorem cell23_6858796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_6858796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858796 prefixEnd_6858796 := by exact prefixLift 6858796
  have htrace : WordTrace (prefixWord ++ tailWord_6858796) baseStart_6858796 baseEnd_6858796 := by
    simpa [prefixWord, tailWord_6858796, baseEnd_6858796] using wordTrace_append hprefix tailTrace_6858796
  have hstable : (prefixWord ++ tailWord_6858796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858796).length < 2 ^ (prefixWord ++ tailWord_6858796).sum := by decide
  have hdescent : baseEnd_6858796 < baseStart_6858796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858804 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 6]
def baseStart_6858804 : Nat := 118140960795 + 6858804 * 2 ^ 59
def prefixEnd_6858804 : Nat := 4983230072969 + 3 ^ 40 * 6858804 * 2
def baseEnd_6858804 : Nat := 391318129664498681278549

theorem tailTrace_6858804 : CollatzResearch.WordTrace tailWord_6858804 prefixEnd_6858804 391318129664498681278549 := by
  unfold tailWord_6858804
  simp only [CollatzResearch.WordTrace]
  refine ⟨125080566721865986654575733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166774088962487982206100977 125080566721865986654575733)
  ·
    refine ⟨11726303130174936248866475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125080566721865986654575733 11726303130174936248866475)
    ·
      refine ⟨17589454695262404373299713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11726303130174936248866475 17589454695262404373299713)
      ·
        refine ⟨13192091021446803279974785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17589454695262404373299713 13192091021446803279974785)
        ·
          refine ⟨9894068266085102459981089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13192091021446803279974785 9894068266085102459981089)
          ·
            refine ⟨7420551199563826844985817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9894068266085102459981089 7420551199563826844985817)
            ·
              refine ⟨5565413399672870133739363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7420551199563826844985817 5565413399672870133739363)
              ·
                refine ⟨8348120099509305200609045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565413399672870133739363 8348120099509305200609045)
                ·
                  refine ⟨391318129664498681278549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8348120099509305200609045 391318129664498681278549)
                  ·
                    rfl

theorem cell23_6858804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_6858804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858804 prefixEnd_6858804 := by exact prefixLift 6858804
  have htrace : WordTrace (prefixWord ++ tailWord_6858804) baseStart_6858804 baseEnd_6858804 := by
    simpa [prefixWord, tailWord_6858804, baseEnd_6858804] using wordTrace_append hprefix tailTrace_6858804
  have hstable : (prefixWord ++ tailWord_6858804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858804).length < 2 ^ (prefixWord ++ tailWord_6858804).sum := by decide
  have hdescent : baseEnd_6858804 < baseStart_6858804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858813 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_6858813 : Nat := 118140960795 + 6858813 * 2 ^ 59
def prefixEnd_6858813 : Nat := 4983230072969 + 3 ^ 40 * 6858813 * 2
def baseEnd_6858813 : Nat := 1173955929435459532098133

theorem tailTrace_6858813 : CollatzResearch.WordTrace tailWord_6858813 prefixEnd_6858813 1173955929435459532098133 := by
  unfold tailWord_6858813
  simp only [CollatzResearch.WordTrace]
  refine ⟨250161461700699367846229093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166774307800466245230819395 250161461700699367846229093)
  ·
    refine ⟨46905274068881131471167955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250161461700699367846229093 46905274068881131471167955)
    ·
      refine ⟨70357911103321697206751933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46905274068881131471167955 70357911103321697206751933)
      ·
        refine ⟨26384216663745636452531975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70357911103321697206751933 26384216663745636452531975)
        ·
          refine ⟨39576324995618454678797963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26384216663745636452531975 39576324995618454678797963)
          ·
            refine ⟨59364487493427682018196945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39576324995618454678797963 59364487493427682018196945)
            ·
              refine ⟨44523365620070761513647709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59364487493427682018196945 44523365620070761513647709)
              ·
                refine ⟨16696262107526535567617891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44523365620070761513647709 16696262107526535567617891)
                ·
                  refine ⟨25044393161289803351426837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16696262107526535567617891 25044393161289803351426837)
                  ·
                    refine ⟨1173955929435459532098133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25044393161289803351426837 1173955929435459532098133)
                    ·
                      rfl

theorem cell23_6858813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_6858813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858813 prefixEnd_6858813 := by exact prefixLift 6858813
  have htrace : WordTrace (prefixWord ++ tailWord_6858813) baseStart_6858813 baseEnd_6858813 := by
    simpa [prefixWord, tailWord_6858813, baseEnd_6858813] using wordTrace_append hprefix tailTrace_6858813
  have hstable : (prefixWord ++ tailWord_6858813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858813).length < 2 ^ (prefixWord ++ tailWord_6858813).sum := by decide
  have hdescent : baseEnd_6858813 < baseStart_6858813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858817 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 1, 5]
def baseStart_6858817 : Nat := 118140960795 + 6858817 * 2 ^ 59
def prefixEnd_6858817 : Nat := 4983230072969 + 3 ^ 40 * 6858817 * 2
def baseEnd_6858817 : Nat := 1173956614076332193548127

theorem tailTrace_6858817 : CollatzResearch.WordTrace tailWord_6858817 prefixEnd_6858817 1173956614076332193548127 := by
  unfold tailWord_6858817
  simp only [CollatzResearch.WordTrace]
  refine ⟨250161607592684876529374705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166774405061789917686249803 250161607592684876529374705)
  ·
    refine ⟨187621205694513657397031029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250161607592684876529374705 187621205694513657397031029)
    ·
      refine ⟨17589488033860655380971659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187621205694513657397031029 17589488033860655380971659)
      ·
        refine ⟨26384232050790983071457489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17589488033860655380971659 26384232050790983071457489)
        ·
          refine ⟨19788174038093237303593117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26384232050790983071457489 19788174038093237303593117)
          ·
            refine ⟨7420565264284963988847419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19788174038093237303593117 7420565264284963988847419)
            ·
              refine ⟨11130847896427445983271129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7420565264284963988847419 11130847896427445983271129)
              ·
                refine ⟨8348135922320584487453347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11130847896427445983271129 8348135922320584487453347)
                ·
                  refine ⟨12522203883480876731180021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8348135922320584487453347 12522203883480876731180021)
                  ·
                    refine ⟨1173956614076332193548127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12522203883480876731180021 1173956614076332193548127)
                    ·
                      rfl

theorem cell23_6858817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_6858817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858817 prefixEnd_6858817 := by exact prefixLift 6858817
  have htrace : WordTrace (prefixWord ++ tailWord_6858817) baseStart_6858817 baseEnd_6858817 := by
    simpa [prefixWord, tailWord_6858817, baseEnd_6858817] using wordTrace_append hprefix tailTrace_6858817
  have hstable : (prefixWord ++ tailWord_6858817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858817).length < 2 ^ (prefixWord ++ tailWord_6858817).sum := by decide
  have hdescent : baseEnd_6858817 < baseStart_6858817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858837 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 1, 1, 4]
def baseStart_6858837 : Nat := 118140960795 + 6858837 * 2 ^ 59
def prefixEnd_6858837 : Nat := 4983230072969 + 3 ^ 40 * 6858837 * 2
def baseEnd_6858837 : Nat := 3521880111842086502394289

theorem tailTrace_6858837 : CollatzResearch.WordTrace tailWord_6858837 prefixEnd_6858837 3521880111842086502394289 := by
  unfold tailWord_6858837
  simp only [CollatzResearch.WordTrace]
  refine ⟨250162337052612419945102765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166774891368408279963401843 250162337052612419945102765)
  ·
    refine ⟨93810876394729657479413537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250162337052612419945102765 93810876394729657479413537)
    ·
      refine ⟨70358157296047243109560153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93810876394729657479413537 70358157296047243109560153)
      ·
        refine ⟨52768617972035432332170115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70358157296047243109560153 52768617972035432332170115)
        ·
          refine ⟨79152926958053148498255173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52768617972035432332170115 79152926958053148498255173)
          ·
            refine ⟨14841173804634965343422845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79152926958053148498255173 14841173804634965343422845)
            ·
              refine ⟨5565440176738112003783567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14841173804634965343422845 5565440176738112003783567)
              ·
                refine ⟨8348160265107168005675351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565440176738112003783567 8348160265107168005675351)
                ·
                  refine ⟨12522240397660752008513027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8348160265107168005675351 12522240397660752008513027)
                  ·
                    refine ⟨18783360596491128012769541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12522240397660752008513027 18783360596491128012769541)
                    ·
                      refine ⟨3521880111842086502394289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18783360596491128012769541 3521880111842086502394289)
                      ·
                        rfl

theorem cell23_6858837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_6858837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858837 prefixEnd_6858837 := by exact prefixLift 6858837
  have htrace : WordTrace (prefixWord ++ tailWord_6858837) baseStart_6858837 baseEnd_6858837 := by
    simpa [prefixWord, tailWord_6858837, baseEnd_6858837] using wordTrace_append hprefix tailTrace_6858837
  have hstable : (prefixWord ++ tailWord_6858837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858837).length < 2 ^ (prefixWord ++ tailWord_6858837).sum := by decide
  have hdescent : baseEnd_6858837 < baseStart_6858837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858840 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 1, 1, 5]
def baseStart_6858840 : Nat := 118140960795 + 6858840 * 2 ^ 59
def prefixEnd_6858840 : Nat := 4983230072969 + 3 ^ 40 * 6858840 * 2
def baseEnd_6858840 : Nat := 3521881652284049990656775

theorem tailTrace_6858840 : CollatzResearch.WordTrace tailWord_6858840 prefixEnd_6858840 3521881652284049990656775 := by
  unfold tailWord_6858840
  simp only [CollatzResearch.WordTrace]
  refine ⟨125081223235800775728730987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166774964314401034304974649 125081223235800775728730987)
  ·
    refine ⟨187621834853701163593096481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125081223235800775728730987 187621834853701163593096481)
    ·
      refine ⟨140716376140275872694822361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187621834853701163593096481 140716376140275872694822361)
      ·
        refine ⟨105537282105206904521116771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140716376140275872694822361 105537282105206904521116771)
        ·
          refine ⟨158305923157810356781675157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105537282105206904521116771 158305923157810356781675157)
          ·
            refine ⟨7420590148022360474141023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158305923157810356781675157 7420590148022360474141023)
            ·
              refine ⟨11130885222033540711211535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7420590148022360474141023 11130885222033540711211535)
              ·
                refine ⟨16696327833050311066817303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11130885222033540711211535 16696327833050311066817303)
                ·
                  refine ⟨25044491749575466600225955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16696327833050311066817303 25044491749575466600225955)
                  ·
                    refine ⟨37566737624363199900338933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25044491749575466600225955 37566737624363199900338933)
                    ·
                      refine ⟨3521881652284049990656775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37566737624363199900338933 3521881652284049990656775)
                      ·
                        rfl

theorem cell23_6858840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_6858840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858840 prefixEnd_6858840 := by exact prefixLift 6858840
  have htrace : WordTrace (prefixWord ++ tailWord_6858840) baseStart_6858840 baseEnd_6858840 := by
    simpa [prefixWord, tailWord_6858840, baseEnd_6858840] using wordTrace_append hprefix tailTrace_6858840
  have hstable : (prefixWord ++ tailWord_6858840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858840).length < 2 ^ (prefixWord ++ tailWord_6858840).sum := by decide
  have hdescent : baseEnd_6858840 < baseStart_6858840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6858993 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 2, 8]
def baseStart_6858993 : Nat := 118140960795 + 6858993 * 2 ^ 59
def prefixEnd_6858993 : Nat := 4983230072969 + 3 ^ 40 * 6858993 * 2
def baseEnd_6858993 : Nat := 1173986738274729297347857

theorem tailTrace_6858993 : CollatzResearch.WordTrace tailWord_6858993 prefixEnd_6858993 1173986738274729297347857 := by
  unfold tailWord_6858993
  simp only [CollatzResearch.WordTrace]
  refine ⟨250168026840047258587781633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166778684560031505725187755 250168026840047258587781633)
  ·
    refine ⟨187626020130035443940836225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250168026840047258587781633 187626020130035443940836225)
    ·
      refine ⟨140719515097526582955627169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187626020130035443940836225 140719515097526582955627169)
      ·
        refine ⟨105539636323144937216720377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140719515097526582955627169 105539636323144937216720377)
        ·
          refine ⟨79154727242358702912540283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105539636323144937216720377 79154727242358702912540283)
          ·
            refine ⟨118732090863538054368810425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79154727242358702912540283 118732090863538054368810425)
            ·
              refine ⟨89049068147653540776607819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118732090863538054368810425 89049068147653540776607819)
              ·
                refine ⟨133573602221480311164911729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89049068147653540776607819 133573602221480311164911729)
                ·
                  refine ⟨100180201666110233373683797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133573602221480311164911729 100180201666110233373683797)
                  ·
                    refine ⟨1173986738274729297347857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100180201666110233373683797 1173986738274729297347857)
                    ·
                      rfl

theorem cell23_6858993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_6858993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6858993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6858993 prefixEnd_6858993 := by exact prefixLift 6858993
  have htrace : WordTrace (prefixWord ++ tailWord_6858993) baseStart_6858993 baseEnd_6858993 := by
    simpa [prefixWord, tailWord_6858993, baseEnd_6858993] using wordTrace_append hprefix tailTrace_6858993
  have hstable : (prefixWord ++ tailWord_6858993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6858993).length < 2 ^ (prefixWord ++ tailWord_6858993).sum := by decide
  have hdescent : baseEnd_6858993 < baseStart_6858993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6858993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859023 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 8]
def baseStart_6859023 : Nat := 118140960795 + 6859023 * 2 ^ 59
def prefixEnd_6859023 : Nat := 4983230072969 + 3 ^ 40 * 6859023 * 2
def baseEnd_6859023 : Nat := 391330624360424752740937

theorem tailTrace_6859023 : CollatzResearch.WordTrace tailWord_6859023 prefixEnd_6859023 391330624360424752740937 := by
  unfold tailWord_6859023
  simp only [CollatzResearch.WordTrace]
  refine ⟨250169121029938573711373723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166779414019959049140915815 250169121029938573711373723)
  ·
    refine ⟨375253681544907860567060585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250169121029938573711373723 375253681544907860567060585)
    ·
      refine ⟨281440261158680895425295439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375253681544907860567060585 281440261158680895425295439)
      ·
        refine ⟨422160391738021343137943159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281440261158680895425295439 422160391738021343137943159)
        ·
          refine ⟨633240587607032014706914739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422160391738021343137943159 633240587607032014706914739)
          ·
            refine ⟨949860881410548022060372109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633240587607032014706914739 949860881410548022060372109)
            ·
              refine ⟨356197830528955508272639541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 949860881410548022060372109 356197830528955508272639541)
              ·
                refine ⟨33393546612089578900559957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 356197830528955508272639541 33393546612089578900559957)
                ·
                  refine ⟨391330624360424752740937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33393546612089578900559957 391330624360424752740937)
                  ·
                    rfl

theorem cell23_6859023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 8].length) (baseStart_6859023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859023 prefixEnd_6859023 := by exact prefixLift 6859023
  have htrace : WordTrace (prefixWord ++ tailWord_6859023) baseStart_6859023 baseEnd_6859023 := by
    simpa [prefixWord, tailWord_6859023, baseEnd_6859023] using wordTrace_append hprefix tailTrace_6859023
  have hstable : (prefixWord ++ tailWord_6859023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859023).length < 2 ^ (prefixWord ++ tailWord_6859023).sum := by decide
  have hdescent : baseEnd_6859023 < baseStart_6859023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859034 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2]
def baseStart_6859034 : Nat := 118140960795 + 6859034 * 2 ^ 59
def prefixEnd_6859034 : Nat := 4983230072969 + 3 ^ 40 * 6859034 * 2
def baseEnd_6859034 : Nat := 3521981267531022231630883

theorem tailTrace_6859034 : CollatzResearch.WordTrace tailWord_6859034 prefixEnd_6859034 3521981267531022231630883 := by
  unfold tailWord_6859034
  simp only [CollatzResearch.WordTrace]
  refine ⟨62542380558224680647506039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166779681488599148393349437 62542380558224680647506039)
  ·
    refine ⟨93813570837337020971259059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62542380558224680647506039 93813570837337020971259059)
    ·
      refine ⟨140720356256005531456888589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93813570837337020971259059 140720356256005531456888589)
      ·
        refine ⟨52770133596002074296333221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140720356256005531456888589 52770133596002074296333221)
        ·
          refine ⟨9894400049250388930562479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52770133596002074296333221 9894400049250388930562479)
          ·
            refine ⟨14841600073875583395843719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9894400049250388930562479 14841600073875583395843719)
            ·
              refine ⟨22262400110813375093765579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14841600073875583395843719 22262400110813375093765579)
              ·
                refine ⟨33393600166220062640648369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22262400110813375093765579 33393600166220062640648369)
                ·
                  refine ⟨25045200124665046980486277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33393600166220062640648369 25045200124665046980486277)
                  ·
                    refine ⟨4695975023374696308841177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25045200124665046980486277 4695975023374696308841177)
                    ·
                      refine ⟨3521981267531022231630883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4695975023374696308841177 3521981267531022231630883)
                      ·
                        rfl

theorem cell23_6859034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_6859034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859034 prefixEnd_6859034 := by exact prefixLift 6859034
  have htrace : WordTrace (prefixWord ++ tailWord_6859034) baseStart_6859034 baseEnd_6859034 := by
    simpa [prefixWord, tailWord_6859034, baseEnd_6859034] using wordTrace_append hprefix tailTrace_6859034
  have hstable : (prefixWord ++ tailWord_6859034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859034).length < 2 ^ (prefixWord ++ tailWord_6859034).sum := by decide
  have hdescent : baseEnd_6859034 < baseStart_6859034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859084 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 3, 1, 3]
def baseStart_6859084 : Nat := 118140960795 + 6859084 * 2 ^ 59
def prefixEnd_6859084 : Nat := 4983230072969 + 3 ^ 40 * 6859084 * 2
def baseEnd_6859084 : Nat := 3522006941563747036005653

theorem tailTrace_6859084 : CollatzResearch.WordTrace tailWord_6859084 prefixEnd_6859084 3522006941563747036005653 := by
  unfold tailWord_6859084
  simp only [CollatzResearch.WordTrace]
  refine ⟨125085672941358790564672153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166780897255145054086229537 125085672941358790564672153)
  ·
    refine ⟨93814254706019092923504115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125085672941358790564672153 93814254706019092923504115)
    ·
      refine ⟨140721382059028639385256173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93814254706019092923504115 140721382059028639385256173)
      ·
        refine ⟨52770518272135739769471065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140721382059028639385256173 52770518272135739769471065)
        ·
          refine ⟨39577888704101804827103299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52770518272135739769471065 39577888704101804827103299)
          ·
            refine ⟨59366833056152707240654949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39577888704101804827103299 59366833056152707240654949)
            ·
              refine ⟨11131281198028632607622803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59366833056152707240654949 11131281198028632607622803)
              ·
                refine ⟨16696921797042948911434205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11131281198028632607622803 16696921797042948911434205)
                ·
                  refine ⟨6261345673891105841787827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16696921797042948911434205 6261345673891105841787827)
                  ·
                    refine ⟨9392018510836658762681741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6261345673891105841787827 9392018510836658762681741)
                    ·
                      refine ⟨3522006941563747036005653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9392018510836658762681741 3522006941563747036005653)
                      ·
                        rfl

theorem cell23_6859084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_6859084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859084 prefixEnd_6859084 := by exact prefixLift 6859084
  have htrace : WordTrace (prefixWord ++ tailWord_6859084) baseStart_6859084 baseEnd_6859084 := by
    simpa [prefixWord, tailWord_6859084, baseEnd_6859084] using wordTrace_append hprefix tailTrace_6859084
  have hstable : (prefixWord ++ tailWord_6859084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859084).length < 2 ^ (prefixWord ++ tailWord_6859084).sum := by decide
  have hdescent : baseEnd_6859084 < baseStart_6859084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859104 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 1, 5]
def baseStart_6859104 : Nat := 118140960795 + 6859104 * 2 ^ 59
def prefixEnd_6859104 : Nat := 4983230072969 + 3 ^ 40 * 6859104 * 2
def baseEnd_6859104 : Nat := 1174005737058945652585187

theorem tailTrace_6859104 : CollatzResearch.WordTrace tailWord_6859104 prefixEnd_6859104 1174005737058945652585187 := by
  unfold tailWord_6859104
  simp only [CollatzResearch.WordTrace]
  refine ⟨125086037671322562272536183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166781383561763416363381577 125086037671322562272536183)
  ·
    refine ⟨187629056506983843408804275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125086037671322562272536183 187629056506983843408804275)
    ·
      refine ⟨281443584760475765113206413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187629056506983843408804275 281443584760475765113206413)
      ·
        refine ⟨105541344285178411917452405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281443584760475765113206413 105541344285178411917452405)
        ·
          refine ⟨9894501026735476117261163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105541344285178411917452405 9894501026735476117261163)
          ·
            refine ⟨14841751540103214175891745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9894501026735476117261163 14841751540103214175891745)
            ·
              refine ⟨11131313655077410631918809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14841751540103214175891745 11131313655077410631918809)
              ·
                refine ⟨8348485241308057973939107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11131313655077410631918809 8348485241308057973939107)
                ·
                  refine ⟨12522727861962086960908661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8348485241308057973939107 12522727861962086960908661)
                  ·
                    refine ⟨1174005737058945652585187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12522727861962086960908661 1174005737058945652585187)
                    ·
                      rfl

theorem cell23_6859104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 5].length) (baseStart_6859104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859104 prefixEnd_6859104 := by exact prefixLift 6859104
  have htrace : WordTrace (prefixWord ++ tailWord_6859104) baseStart_6859104 baseEnd_6859104 := by
    simpa [prefixWord, tailWord_6859104, baseEnd_6859104] using wordTrace_append hprefix tailTrace_6859104
  have hstable : (prefixWord ++ tailWord_6859104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859104).length < 2 ^ (prefixWord ++ tailWord_6859104).sum := by decide
  have hdescent : baseEnd_6859104 < baseStart_6859104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859107 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 2, 6, 2]
def baseStart_6859107 : Nat := 118140960795 + 6859107 * 2 ^ 59
def prefixEnd_6859107 : Nat := 4983230072969 + 3 ^ 40 * 6859107 * 2
def baseEnd_6859107 : Nat := 3522018751618800446018047

theorem tailTrace_6859107 : CollatzResearch.WordTrace tailWord_6859107 prefixEnd_6859107 3522018751618800446018047 := by
  unfold tailWord_6859107
  simp only [CollatzResearch.WordTrace]
  refine ⟨250172184761634256057431575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166781456507756170704954383 250172184761634256057431575)
  ·
    refine ⟨375258277142451384086147363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250172184761634256057431575 375258277142451384086147363)
    ·
      refine ⟨562887415713677076129221045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375258277142451384086147363 562887415713677076129221045)
      ·
        refine ⟨52770695223157225887114473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 562887415713677076129221045 52770695223157225887114473)
        ·
          refine ⟨39578021417367919415335855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52770695223157225887114473 39578021417367919415335855)
          ·
            refine ⟨59367032126051879123003783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39578021417367919415335855 59367032126051879123003783)
            ·
              refine ⟨89050548189077818684505675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59367032126051879123003783 89050548189077818684505675)
              ·
                refine ⟨133575822283616728026758513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89050548189077818684505675 133575822283616728026758513)
                ·
                  refine ⟨100181866712712546020068885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133575822283616728026758513 100181866712712546020068885)
                  ·
                    refine ⟨4696025002158400594690729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100181866712712546020068885 4696025002158400594690729)
                    ·
                      refine ⟨3522018751618800446018047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696025002158400594690729 3522018751618800446018047)
                      ·
                        rfl

theorem cell23_6859107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_6859107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859107 prefixEnd_6859107 := by exact prefixLift 6859107
  have htrace : WordTrace (prefixWord ++ tailWord_6859107) baseStart_6859107 baseEnd_6859107 := by
    simpa [prefixWord, tailWord_6859107, baseEnd_6859107] using wordTrace_append hprefix tailTrace_6859107
  have hstable : (prefixWord ++ tailWord_6859107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859107).length < 2 ^ (prefixWord ++ tailWord_6859107).sum := by decide
  have hdescent : baseEnd_6859107 < baseStart_6859107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859117 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_6859117 : Nat := 118140960795 + 6859117 * 2 ^ 59
def prefixEnd_6859117 : Nat := 4983230072969 + 3 ^ 40 * 6859117 * 2
def baseEnd_6859117 : Nat := 1174007962141781802297667

theorem tailTrace_6859117 : CollatzResearch.WordTrace tailWord_6859117 prefixEnd_6859117 1174007962141781802297667 := by
  unfold tailWord_6859117
  simp only [CollatzResearch.WordTrace]
  refine ⟨250172549491598027765295605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166781699661065351843530403 250172549491598027765295605)
  ·
    refine ⟨23453676514837315102996463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250172549491598027765295605 23453676514837315102996463)
    ·
      refine ⟨35180514772255972654494695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23453676514837315102996463 35180514772255972654494695)
      ·
        refine ⟨52770772158383958981742043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35180514772255972654494695 52770772158383958981742043)
        ·
          refine ⟨79156158237575938472613065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52770772158383958981742043 79156158237575938472613065)
          ·
            refine ⟨59367118678181953854459799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79156158237575938472613065 59367118678181953854459799)
            ·
              refine ⟨89050678017272930781689699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59367118678181953854459799 89050678017272930781689699)
              ·
                refine ⟨133576017025909396172534549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89050678017272930781689699 133576017025909396172534549)
                ·
                  refine ⟨6261375798089502945587557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133576017025909396172534549 6261375798089502945587557)
                  ·
                    refine ⟨1174007962141781802297667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6261375798089502945587557 1174007962141781802297667)
                    ·
                      rfl

theorem cell23_6859117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_6859117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859117 prefixEnd_6859117 := by exact prefixLift 6859117
  have htrace : WordTrace (prefixWord ++ tailWord_6859117) baseStart_6859117 baseEnd_6859117 := by
    simpa [prefixWord, tailWord_6859117, baseEnd_6859117] using wordTrace_append hprefix tailTrace_6859117
  have hstable : (prefixWord ++ tailWord_6859117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859117).length < 2 ^ (prefixWord ++ tailWord_6859117).sum := by decide
  have hdescent : baseEnd_6859117 < baseStart_6859117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859137 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_6859137 : Nat := 118140960795 + 6859137 * 2 ^ 59
def prefixEnd_6859137 : Nat := 4983230072969 + 3 ^ 40 * 6859137 * 2
def baseEnd_6859137 : Nat := 3522034156038435328642909

theorem tailTrace_6859137 : CollatzResearch.WordTrace tailWord_6859137 prefixEnd_6859137 3522034156038435328642909 := by
  unfold tailWord_6859137
  simp only [CollatzResearch.WordTrace]
  refine ⟨250173278951525571181023665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166782185967683714120682443 250173278951525571181023665)
  ·
    refine ⟨187629959213644178385767749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250173278951525571181023665 187629959213644178385767749)
    ·
      refine ⟨35180617352558283447331453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187629959213644178385767749 35180617352558283447331453)
      ·
        refine ⟨13192731507209356292749295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35180617352558283447331453 13192731507209356292749295)
        ·
          refine ⟨19789097260814034439123943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13192731507209356292749295 19789097260814034439123943)
          ·
            refine ⟨29683645891221051658685915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19789097260814034439123943 29683645891221051658685915)
            ·
              refine ⟨44525468836831577488028873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29683645891221051658685915 44525468836831577488028873)
              ·
                refine ⟨33394101627623683116021655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44525468836831577488028873 33394101627623683116021655)
                ·
                  refine ⟨50091152441435524674032483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33394101627623683116021655 50091152441435524674032483)
                  ·
                    refine ⟨75136728662153287011048725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50091152441435524674032483 75136728662153287011048725)
                    ·
                      refine ⟨3522034156038435328642909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75136728662153287011048725 3522034156038435328642909)
                      ·
                        rfl

theorem cell23_6859137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_6859137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859137 prefixEnd_6859137 := by exact prefixLift 6859137
  have htrace : WordTrace (prefixWord ++ tailWord_6859137) baseStart_6859137 baseEnd_6859137 := by
    simpa [prefixWord, tailWord_6859137, baseEnd_6859137] using wordTrace_append hprefix tailTrace_6859137
  have hstable : (prefixWord ++ tailWord_6859137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859137).length < 2 ^ (prefixWord ++ tailWord_6859137).sum := by decide
  have hdescent : baseEnd_6859137 < baseStart_6859137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859157 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_6859157 : Nat := 118140960795 + 6859157 * 2 ^ 59
def prefixEnd_6859157 : Nat := 4983230072969 + 3 ^ 40 * 6859157 * 2
def baseEnd_6859157 : Nat := 3522044425651525250392817

theorem tailTrace_6859157 : CollatzResearch.WordTrace tailWord_6859157 prefixEnd_6859157 3522044425651525250392817 := by
  unfold tailWord_6859157
  simp only [CollatzResearch.WordTrace]
  refine ⟨250174008411453114596751725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166782672274302076397834483 250174008411453114596751725)
  ·
    refine ⟨93815253154294917973781897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250174008411453114596751725 93815253154294917973781897)
    ·
      refine ⟨70361439865721188480336423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93815253154294917973781897 70361439865721188480336423)
      ·
        refine ⟨105542159798581782720504635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70361439865721188480336423 105542159798581782720504635)
        ·
          refine ⟨158313239697872674080756953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105542159798581782720504635 158313239697872674080756953)
          ·
            refine ⟨118734929773404505560567715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158313239697872674080756953 118734929773404505560567715)
            ·
              refine ⟨178102394660106758340851573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118734929773404505560567715 178102394660106758340851573)
              ·
                refine ⟨16697099499385008594454835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178102394660106758340851573 16697099499385008594454835)
                ·
                  refine ⟨25045649249077512891682253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16697099499385008594454835 25045649249077512891682253)
                  ·
                    refine ⟨9392118468404067334380845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25045649249077512891682253 9392118468404067334380845)
                    ·
                      refine ⟨3522044425651525250392817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9392118468404067334380845 3522044425651525250392817)
                      ·
                        rfl

theorem cell23_6859157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_6859157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859157 prefixEnd_6859157 := by exact prefixLift 6859157
  have htrace : WordTrace (prefixWord ++ tailWord_6859157) baseStart_6859157 baseEnd_6859157 := by
    simpa [prefixWord, tailWord_6859157, baseEnd_6859157] using wordTrace_append hprefix tailTrace_6859157
  have hstable : (prefixWord ++ tailWord_6859157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859157).length < 2 ^ (prefixWord ++ tailWord_6859157).sum := by decide
  have hdescent : baseEnd_6859157 < baseStart_6859157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859191 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 2, 1, 3]
def baseStart_6859191 : Nat := 118140960795 + 6859191 * 2 ^ 59
def prefixEnd_6859191 : Nat := 4983230072969 + 3 ^ 40 * 6859191 * 2
def baseEnd_6859191 : Nat := 3522061883993778117367661

theorem tailTrace_6859191 : CollatzResearch.WordTrace tailWord_6859191 prefixEnd_6859191 3522061883993778117367661 := by
  unfold tailWord_6859191
  simp only [CollatzResearch.WordTrace]
  refine ⟨250175248493329938403489427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166783498995553292268992951 250175248493329938403489427)
  ·
    refine ⟨375262872739994907605234141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250175248493329938403489427 375262872739994907605234141)
    ·
      refine ⟨140723577277498090351962803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375262872739994907605234141 140723577277498090351962803)
      ·
        refine ⟨211085365916247135527944205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140723577277498090351962803 211085365916247135527944205)
        ·
          refine ⟨79157012218592675822979077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211085365916247135527944205 79157012218592675822979077)
          ·
            refine ⟨14841939790986126716808577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79157012218592675822979077 14841939790986126716808577)
            ·
              refine ⟨11131454843239595037606433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14841939790986126716808577 11131454843239595037606433)
              ·
                refine ⟨8348591132429696278204825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11131454843239595037606433 8348591132429696278204825)
                ·
                  refine ⟨6261443349322272208653619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8348591132429696278204825 6261443349322272208653619)
                  ·
                    refine ⟨9392165023983408312980429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6261443349322272208653619 9392165023983408312980429)
                    ·
                      refine ⟨3522061883993778117367661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9392165023983408312980429 3522061883993778117367661)
                      ·
                        rfl

theorem cell23_6859191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_6859191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859191 prefixEnd_6859191 := by exact prefixLift 6859191
  have htrace : WordTrace (prefixWord ++ tailWord_6859191) baseStart_6859191 baseEnd_6859191 := by
    simpa [prefixWord, tailWord_6859191, baseEnd_6859191] using wordTrace_append hprefix tailTrace_6859191
  have hstable : (prefixWord ++ tailWord_6859191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859191).length < 2 ^ (prefixWord ++ tailWord_6859191).sum := by decide
  have hdescent : baseEnd_6859191 < baseStart_6859191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859197 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_6859197 : Nat := 118140960795 + 6859197 * 2 ^ 59
def prefixEnd_6859197 : Nat := 4983230072969 + 3 ^ 40 * 6859197 * 2
def baseEnd_6859197 : Nat := 3522064964877705093892633

theorem tailTrace_6859197 : CollatzResearch.WordTrace tailWord_6859197 prefixEnd_6859197 3522064964877705093892633 := by
  unfold tailWord_6859197
  simp only [CollatzResearch.WordTrace]
  refine ⟨250175467331308201428207845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166783644887538800952138563 250175467331308201428207845)
  ·
    refine ⟨46907900124620287767788971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250175467331308201428207845 46907900124620287767788971)
    ·
      refine ⟨70361850186930431651683457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46907900124620287767788971 70361850186930431651683457)
      ·
        refine ⟨52771387640197823738762593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70361850186930431651683457 52771387640197823738762593)
        ·
          refine ⟨39578540730148367804071945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52771387640197823738762593 39578540730148367804071945)
          ·
            refine ⟨29683905547611275853053959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39578540730148367804071945 29683905547611275853053959)
            ·
              refine ⟨44525858321416913779580939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29683905547611275853053959 44525858321416913779580939)
              ·
                refine ⟨66788787482125370669371409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44525858321416913779580939 66788787482125370669371409)
                ·
                  refine ⟨50091590611594028002028557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66788787482125370669371409 50091590611594028002028557)
                  ·
                    refine ⟨18784346479347760500760709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50091590611594028002028557 18784346479347760500760709)
                    ·
                      refine ⟨3522064964877705093892633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18784346479347760500760709 3522064964877705093892633)
                      ·
                        rfl

theorem cell23_6859197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_6859197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859197 prefixEnd_6859197 := by exact prefixLift 6859197
  have htrace : WordTrace (prefixWord ++ tailWord_6859197) baseStart_6859197 baseEnd_6859197 := by
    simpa [prefixWord, tailWord_6859197, baseEnd_6859197] using wordTrace_append hprefix tailTrace_6859197
  have hstable : (prefixWord ++ tailWord_6859197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859197).length < 2 ^ (prefixWord ++ tailWord_6859197).sum := by decide
  have hdescent : baseEnd_6859197 < baseStart_6859197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859207 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 2, 6]
def baseStart_6859207 : Nat := 118140960795 + 6859207 * 2 ^ 59
def prefixEnd_6859207 : Nat := 4983230072969 + 3 ^ 40 * 6859207 * 2
def baseEnd_6859207 : Nat := 1174023366561416684922529

theorem tailTrace_6859207 : CollatzResearch.WordTrace tailWord_6859207 prefixEnd_6859207 1174023366561416684922529 := by
  unfold tailWord_6859207
  simp only [CollatzResearch.WordTrace]
  refine ⟨250175832061271973136071875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166783888040847982090714583 250175832061271973136071875)
  ·
    refine ⟨375263748091907959704107813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250175832061271973136071875 375263748091907959704107813)
    ·
      refine ⟨70361952767232742444520215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375263748091907959704107813 70361952767232742444520215)
      ·
        refine ⟨105542929150849113666780323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70361952767232742444520215 105542929150849113666780323)
        ·
          refine ⟨158314393726273670500170485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105542929150849113666780323 158314393726273670500170485)
          ·
            refine ⟨14841974411838156609390983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158314393726273670500170485 14841974411838156609390983)
            ·
              refine ⟨22262961617757234914086475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14841974411838156609390983 22262961617757234914086475)
              ·
                refine ⟨33394442426635852371129713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22262961617757234914086475 33394442426635852371129713)
                ·
                  refine ⟨25045831819976889278347285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33394442426635852371129713 25045831819976889278347285)
                  ·
                    refine ⟨1174023366561416684922529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25045831819976889278347285 1174023366561416684922529)
                    ·
                      rfl

theorem cell23_6859207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_6859207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859207 prefixEnd_6859207 := by exact prefixLift 6859207
  have htrace : WordTrace (prefixWord ++ tailWord_6859207) baseStart_6859207 baseEnd_6859207 := by
    simpa [prefixWord, tailWord_6859207, baseEnd_6859207] using wordTrace_append hprefix tailTrace_6859207
  have hstable : (prefixWord ++ tailWord_6859207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859207).length < 2 ^ (prefixWord ++ tailWord_6859207).sum := by decide
  have hdescent : baseEnd_6859207 < baseStart_6859207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859235 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 1, 3, 2]
def baseStart_6859235 : Nat := 118140960795 + 6859235 * 2 ^ 59
def prefixEnd_6859235 : Nat := 4983230072969 + 3 ^ 40 * 6859235 * 2
def baseEnd_6859235 : Nat := 3522084477142575945217459

theorem tailTrace_6859235 : CollatzResearch.WordTrace tailWord_6859235 prefixEnd_6859235 3522084477142575945217459 := by
  unfold tailWord_6859235
  simp only [CollatzResearch.WordTrace]
  refine ⟨250176853305170533918091159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166784568870113689278727439 250176853305170533918091159)
  ·
    refine ⟨375265279957755800877136739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250176853305170533918091159 375265279957755800877136739)
    ·
      refine ⟨562897919936633701315705109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375265279957755800877136739 562897919936633701315705109)
      ·
        refine ⟨26385839997029704749173677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 562897919936633701315705109 26385839997029704749173677)
        ·
          refine ⟨9894689998886139280940129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26385839997029704749173677 9894689998886139280940129)
          ·
            refine ⟨7421017499164604460705097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9894689998886139280940129 7421017499164604460705097)
            ·
              refine ⟨5565763124373453345528823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7421017499164604460705097 5565763124373453345528823)
              ·
                refine ⟨8348644686560180018293235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565763124373453345528823 8348644686560180018293235)
                ·
                  refine ⟨12522967029840270027439853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8348644686560180018293235 12522967029840270027439853)
                  ·
                    refine ⟨4696112636190101260289945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12522967029840270027439853 4696112636190101260289945)
                    ·
                      refine ⟨3522084477142575945217459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696112636190101260289945 3522084477142575945217459)
                      ·
                        rfl

theorem cell23_6859235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_6859235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859235 prefixEnd_6859235 := by exact prefixLift 6859235
  have htrace : WordTrace (prefixWord ++ tailWord_6859235) baseStart_6859235 baseEnd_6859235 := by
    simpa [prefixWord, tailWord_6859235, baseEnd_6859235] using wordTrace_append hprefix tailTrace_6859235
  have hstable : (prefixWord ++ tailWord_6859235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859235).length < 2 ^ (prefixWord ++ tailWord_6859235).sum := by decide
  have hdescent : baseEnd_6859235 < baseStart_6859235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859254 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_6859254 : Nat := 118140960795 + 6859254 * 2 ^ 59
def prefixEnd_6859254 : Nat := 4983230072969 + 3 ^ 40 * 6859254 * 2
def baseEnd_6859254 : Nat := 391343803697223485653319

theorem tailTrace_6859254 : CollatzResearch.WordTrace tailWord_6859254 prefixEnd_6859254 391343803697223485653319 := by
  unfold tailWord_6859254
  simp only [CollatzResearch.WordTrace]
  refine ⟨15636096643256356260189551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166785030861401133442021877 15636096643256356260189551)
  ·
    refine ⟨23454144964884534390284327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15636096643256356260189551 23454144964884534390284327)
    ·
      refine ⟨35181217447326801585426491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23454144964884534390284327 35181217447326801585426491)
      ·
        refine ⟨52771826170990202378139737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35181217447326801585426491 52771826170990202378139737)
        ·
          refine ⟨39578869628242651783604803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52771826170990202378139737 39578869628242651783604803)
          ·
            refine ⟨59368304442363977675407205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39578869628242651783604803 59368304442363977675407205)
            ·
              refine ⟨11131557082943245814138851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59368304442363977675407205 11131557082943245814138851)
              ·
                refine ⟨16697335624414868721208277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11131557082943245814138851 16697335624414868721208277)
                ·
                  refine ⟨391343803697223485653319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16697335624414868721208277 391343803697223485653319)
                  ·
                    rfl

theorem cell23_6859254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_6859254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859254 prefixEnd_6859254 := by exact prefixLift 6859254
  have htrace : WordTrace (prefixWord ++ tailWord_6859254) baseStart_6859254 baseEnd_6859254 := by
    simpa [prefixWord, tailWord_6859254, baseEnd_6859254] using wordTrace_append hprefix tailTrace_6859254
  have hstable : (prefixWord ++ tailWord_6859254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859254).length < 2 ^ (prefixWord ++ tailWord_6859254).sum := by decide
  have hdescent : baseEnd_6859254 < baseStart_6859254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859265 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_6859265 : Nat := 118140960795 + 6859265 * 2 ^ 59
def prefixEnd_6859265 : Nat := 4983230072969 + 3 ^ 40 * 6859265 * 2
def baseEnd_6859265 : Nat := 3522099881562210827842321

theorem tailTrace_6859265 : CollatzResearch.WordTrace tailWord_6859265 prefixEnd_6859265 3522099881562210827842321 := by
  unfold tailWord_6859265
  simp only [CollatzResearch.WordTrace]
  refine ⟨250177947495061849041683249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166785298330041232694455499 250177947495061849041683249)
  ·
    refine ⟨187633460621296386781262437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250177947495061849041683249 187633460621296386781262437)
    ·
      refine ⟨35181273866493072521486707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187633460621296386781262437 35181273866493072521486707)
      ·
        refine ⟨52771910799739608782230061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35181273866493072521486707 52771910799739608782230061)
        ·
          refine ⟨19789466549902353293336273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52771910799739608782230061 19789466549902353293336273)
          ·
            refine ⟨14842099912426764970002205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19789466549902353293336273 14842099912426764970002205)
            ·
              refine ⟨5565787467160036863750827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14842099912426764970002205 5565787467160036863750827)
              ·
                refine ⟨8348681200740055295626241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565787467160036863750827 8348681200740055295626241)
                ·
                  refine ⟨6261510900555041471719681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8348681200740055295626241 6261510900555041471719681)
                  ·
                    refine ⟨4696133175416281103789761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6261510900555041471719681 4696133175416281103789761)
                    ·
                      refine ⟨3522099881562210827842321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696133175416281103789761 3522099881562210827842321)
                      ·
                        rfl

theorem cell23_6859265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_6859265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859265 prefixEnd_6859265 := by exact prefixLift 6859265
  have htrace : WordTrace (prefixWord ++ tailWord_6859265) baseStart_6859265 baseEnd_6859265 := by
    simpa [prefixWord, tailWord_6859265, baseEnd_6859265] using wordTrace_append hprefix tailTrace_6859265
  have hstable : (prefixWord ++ tailWord_6859265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859265).length < 2 ^ (prefixWord ++ tailWord_6859265).sum := by decide
  have hdescent : baseEnd_6859265 < baseStart_6859265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859316 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_6859316 : Nat := 118140960795 + 6859316 * 2 ^ 59
def prefixEnd_6859316 : Nat := 4983230072969 + 3 ^ 40 * 6859316 * 2
def baseEnd_6859316 : Nat := 3522126069075590128304587

theorem tailTrace_6859316 : CollatzResearch.WordTrace tailWord_6859316 prefixEnd_6859316 3522126069075590128304587 := by
  unfold tailWord_6859316
  simp only [CollatzResearch.WordTrace]
  refine ⟨125089903808938542375894901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166786538411918056501193201 125089903808938542375894901)
  ·
    refine ⟨11727178482087988347740147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125089903808938542375894901 11727178482087988347740147)
    ·
      refine ⟨17590767723131982521610221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11727178482087988347740147 17590767723131982521610221)
      ·
        refine ⟨6596537896174493445603833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17590767723131982521610221 6596537896174493445603833)
        ·
          refine ⟨4947403422130870084202875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6596537896174493445603833 4947403422130870084202875)
          ·
            refine ⟨7421105133196305126304313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4947403422130870084202875 7421105133196305126304313)
            ·
              refine ⟨5565828849897228844728235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7421105133196305126304313 5565828849897228844728235)
              ·
                refine ⟨8348743274845843267092353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565828849897228844728235 8348743274845843267092353)
                ·
                  refine ⟨6261557456134382450319265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8348743274845843267092353 6261557456134382450319265)
                  ·
                    refine ⟨4696168092100786837739449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6261557456134382450319265 4696168092100786837739449)
                    ·
                      refine ⟨3522126069075590128304587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696168092100786837739449 3522126069075590128304587)
                      ·
                        rfl

theorem cell23_6859316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_6859316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859316 prefixEnd_6859316 := by exact prefixLift 6859316
  have htrace : WordTrace (prefixWord ++ tailWord_6859316) baseStart_6859316 baseEnd_6859316 := by
    simpa [prefixWord, tailWord_6859316, baseEnd_6859316] using wordTrace_append hprefix tailTrace_6859316
  have hstable : (prefixWord ++ tailWord_6859316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859316).length < 2 ^ (prefixWord ++ tailWord_6859316).sum := by decide
  have hdescent : baseEnd_6859316 < baseStart_6859316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859417 : List Nat := [1, 2, 1, 2, 1, 2, 14]
def baseStart_6859417 : Nat := 118140960795 + 6859417 * 2 ^ 59
def prefixEnd_6859417 : Nat := 4983230072969 + 3 ^ 40 * 6859417 * 2
def baseEnd_6859417 : Nat := 43483678155823385594341

theorem tailTrace_6859417 : CollatzResearch.WordTrace tailWord_6859417 prefixEnd_6859417 43483678155823385594341 := by
  unfold tailWord_6859417
  simp only [CollatzResearch.WordTrace]
  refine ⟨250183491390511179001216505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166788994260340786000811003 250183491390511179001216505)
  ·
    refine ⟨187637618542883384250912379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250183491390511179001216505 187637618542883384250912379)
    ·
      refine ⟨281456427814325076376368569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187637618542883384250912379 281456427814325076376368569)
      ·
        refine ⟨211092320860743807282276427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281456427814325076376368569 211092320860743807282276427)
        ·
          refine ⟨316638481291115710923414641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211092320860743807282276427 316638481291115710923414641)
          ·
            refine ⟨237478860968336783192560981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316638481291115710923414641 237478860968336783192560981)
            ·
              refine ⟨43483678155823385594341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 237478860968336783192560981 43483678155823385594341)
              ·
                rfl

theorem cell23_6859417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 14].length) (baseStart_6859417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859417 prefixEnd_6859417 := by exact prefixLift 6859417
  have htrace : WordTrace (prefixWord ++ tailWord_6859417) baseStart_6859417 baseEnd_6859417 := by
    simpa [prefixWord, tailWord_6859417, baseEnd_6859417] using wordTrace_append hprefix tailTrace_6859417
  have hstable : (prefixWord ++ tailWord_6859417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859417).length < 2 ^ (prefixWord ++ tailWord_6859417).sum := by decide
  have hdescent : baseEnd_6859417 < baseStart_6859417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859438 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_6859438 : Nat := 118140960795 + 6859438 * 2 ^ 59
def prefixEnd_6859438 : Nat := 4983230072969 + 3 ^ 40 * 6859438 * 2
def baseEnd_6859438 : Nat := 1174062904571812883659675

theorem tailTrace_6859438 : CollatzResearch.WordTrace tailWord_6859438 prefixEnd_6859438 1174062904571812883659675 := by
  unfold tailWord_6859438
  simp only [CollatzResearch.WordTrace]
  refine ⟨31273032165429387448466371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166789504882290066391820645 31273032165429387448466371)
  ·
    refine ⟨46909548248144081172699557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31273032165429387448466371 46909548248144081172699557)
    ·
      refine ⟨8795540296527015219881167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46909548248144081172699557 8795540296527015219881167)
      ·
        refine ⟨13193310444790522829821751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8795540296527015219881167 13193310444790522829821751)
        ·
          refine ⟨19789965667185784244732627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13193310444790522829821751 19789965667185784244732627)
          ·
            refine ⟨29684948500778676367098941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19789965667185784244732627 29684948500778676367098941)
            ·
              refine ⟨11131855687792003637662103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29684948500778676367098941 11131855687792003637662103)
              ·
                refine ⟨16697783531688005456493155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11131855687792003637662103 16697783531688005456493155)
                ·
                  refine ⟨25046675297532008184739733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16697783531688005456493155 25046675297532008184739733)
                  ·
                    refine ⟨1174062904571812883659675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25046675297532008184739733 1174062904571812883659675)
                    ·
                      rfl

theorem cell23_6859438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_6859438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859438 prefixEnd_6859438 := by exact prefixLift 6859438
  have htrace : WordTrace (prefixWord ++ tailWord_6859438) baseStart_6859438 baseEnd_6859438 := by
    simpa [prefixWord, tailWord_6859438, baseEnd_6859438] using wordTrace_append hprefix tailTrace_6859438
  have hstable : (prefixWord ++ tailWord_6859438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859438).length < 2 ^ (prefixWord ++ tailWord_6859438).sum := by decide
  have hdescent : baseEnd_6859438 < baseStart_6859438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859445 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_6859445 : Nat := 118140960795 + 6859445 * 2 ^ 59
def prefixEnd_6859445 : Nat := 4983230072969 + 3 ^ 40 * 6859445 * 2
def baseEnd_6859445 : Nat := 3522192308080020123591493

theorem tailTrace_6859445 : CollatzResearch.WordTrace tailWord_6859445 prefixEnd_6859445 3522192308080020123591493 := by
  unfold tailWord_6859445
  simp only [CollatzResearch.WordTrace]
  refine ⟨250184512634409739783235789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166789675089606493188823859 250184512634409739783235789)
  ·
    refine ⟨93819192237903652418713421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250184512634409739783235789 93819192237903652418713421)
    ·
      refine ⟨35182197089213869657017533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93819192237903652418713421 35182197089213869657017533)
      ·
        refine ⟨13193323908455201121381575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35182197089213869657017533 13193323908455201121381575)
        ·
          refine ⟨19789985862682801682072363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13193323908455201121381575 19789985862682801682072363)
          ·
            refine ⟨29684978794024202523108545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19789985862682801682072363 29684978794024202523108545)
            ·
              refine ⟨22263734095518151892331409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29684978794024202523108545 22263734095518151892331409)
              ·
                refine ⟨16697800571638613919248557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22263734095518151892331409 16697800571638613919248557)
                ·
                  refine ⟨6261675214364480219718209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16697800571638613919248557 6261675214364480219718209)
                  ·
                    refine ⟨4696256410773360164788657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6261675214364480219718209 4696256410773360164788657)
                    ·
                      refine ⟨3522192308080020123591493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696256410773360164788657 3522192308080020123591493)
                      ·
                        rfl

theorem cell23_6859445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_6859445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859445 prefixEnd_6859445 := by exact prefixLift 6859445
  have htrace : WordTrace (prefixWord ++ tailWord_6859445) baseStart_6859445 baseEnd_6859445 := by
    simpa [prefixWord, tailWord_6859445, baseEnd_6859445] using wordTrace_append hprefix tailTrace_6859445
  have hstable : (prefixWord ++ tailWord_6859445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859445).length < 2 ^ (prefixWord ++ tailWord_6859445).sum := by decide
  have hdescent : baseEnd_6859445 < baseStart_6859445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859471 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 7, 3, 2]
def baseStart_6859471 : Nat := 118140960795 + 6859471 * 2 ^ 59
def prefixEnd_6859471 : Nat := 4983230072969 + 3 ^ 40 * 6859471 * 2
def baseEnd_6859471 : Nat := 3522205658577037021866373

theorem tailTrace_6859471 : CollatzResearch.WordTrace tailWord_6859471 prefixEnd_6859471 3522205658577037021866373 := by
  unfold tailWord_6859471
  simp only [CollatzResearch.WordTrace]
  refine ⟨250185460932315546223682267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166790307288210364149121511 250185460932315546223682267)
  ·
    refine ⟨375278191398473319335523401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250185460932315546223682267 375278191398473319335523401)
    ·
      refine ⟨281458643548854989501642551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375278191398473319335523401 281458643548854989501642551)
      ·
        refine ⟨422187965323282484252463827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281458643548854989501642551 422187965323282484252463827)
        ·
          refine ⟨633281947984923726378695741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422187965323282484252463827 633281947984923726378695741)
          ·
            refine ⟨237480730494346397392010903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 633281947984923726378695741 237480730494346397392010903)
            ·
              refine ⟨356221095741519596088016355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237480730494346397392010903 356221095741519596088016355)
              ·
                refine ⟨534331643612279394132024533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356221095741519596088016355 534331643612279394132024533)
                ·
                  refine ⟨12523397897162798299969325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 534331643612279394132024533 12523397897162798299969325)
                  ·
                    refine ⟨4696274211436049362488497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12523397897162798299969325 4696274211436049362488497)
                    ·
                      refine ⟨3522205658577037021866373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696274211436049362488497 3522205658577037021866373)
                      ·
                        rfl

theorem cell23_6859471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 3, 2].length) (baseStart_6859471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859471 prefixEnd_6859471 := by exact prefixLift 6859471
  have htrace : WordTrace (prefixWord ++ tailWord_6859471) baseStart_6859471 baseEnd_6859471 := by
    simpa [prefixWord, tailWord_6859471, baseEnd_6859471] using wordTrace_append hprefix tailTrace_6859471
  have hstable : (prefixWord ++ tailWord_6859471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859471).length < 2 ^ (prefixWord ++ tailWord_6859471).sum := by decide
  have hdescent : baseEnd_6859471 < baseStart_6859471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859504 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 5]
def baseStart_6859504 : Nat := 118140960795 + 6859504 * 2 ^ 59
def prefixEnd_6859504 : Nat := 4983230072969 + 3 ^ 40 * 6859504 * 2
def baseEnd_6859504 : Nat := 3522222603438635392753721

theorem tailTrace_6859504 : CollatzResearch.WordTrace tailWord_6859504 prefixEnd_6859504 3522222603438635392753721 := by
  unfold tailWord_6859504
  simp only [CollatzResearch.WordTrace]
  refine ⟨125093332270597996429816783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166791109694130661906422377 125093332270597996429816783)
  ·
    refine ⟨187639998405896994644725175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125093332270597996429816783 187639998405896994644725175)
    ·
      refine ⟨281459997608845491967087763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187639998405896994644725175 281459997608845491967087763)
      ·
        refine ⟨422189996413268237950631645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281459997608845491967087763 422189996413268237950631645)
        ·
          refine ⟨158321248654975589231486867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422189996413268237950631645 158321248654975589231486867)
          ·
            refine ⟨237481872982463383847230301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158321248654975589231486867 237481872982463383847230301)
            ·
              refine ⟨89055702368423768942711363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237481872982463383847230301 89055702368423768942711363)
              ·
                refine ⟨133583553552635653414067045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89055702368423768942711363 133583553552635653414067045)
                ·
                  refine ⟨25046916291119185015137571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133583553552635653414067045 25046916291119185015137571)
                  ·
                    refine ⟨37570374436678777522706357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25046916291119185015137571 37570374436678777522706357)
                    ·
                      refine ⟨3522222603438635392753721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37570374436678777522706357 3522222603438635392753721)
                      ·
                        rfl

theorem cell23_6859504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_6859504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859504 prefixEnd_6859504 := by exact prefixLift 6859504
  have htrace : WordTrace (prefixWord ++ tailWord_6859504) baseStart_6859504 baseEnd_6859504 := by
    simpa [prefixWord, tailWord_6859504, baseEnd_6859504] using wordTrace_append hprefix tailTrace_6859504
  have hstable : (prefixWord ++ tailWord_6859504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859504).length < 2 ^ (prefixWord ++ tailWord_6859504).sum := by decide
  have hdescent : baseEnd_6859504 < baseStart_6859504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859535 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 2, 2, 2]
def baseStart_6859535 : Nat := 118140960795 + 6859535 * 2 ^ 59
def prefixEnd_6859535 : Nat := 4983230072969 + 3 ^ 40 * 6859535 * 2
def baseEnd_6859535 : Nat := 3522238521338924771466079

theorem tailTrace_6859535 : CollatzResearch.WordTrace tailWord_6859535 prefixEnd_6859535 3522238521338924771466079 := by
  unfold tailWord_6859535
  simp only [CollatzResearch.WordTrace]
  refine ⟨250187795204083685154012059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166791863469389123436008039 250187795204083685154012059)
  ·
    refine ⟨375281692806125527731018089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250187795204083685154012059 375281692806125527731018089)
    ·
      refine ⟨281461269604594145798263567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375281692806125527731018089 281461269604594145798263567)
      ·
        refine ⟨422191904406891218697395351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281461269604594145798263567 422191904406891218697395351)
        ·
          refine ⟨633287856610336828046093027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422191904406891218697395351 633287856610336828046093027)
          ·
            refine ⟨949931784915505242069139541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633287856610336828046093027 949931784915505242069139541)
            ·
              refine ⟨11132013104478577055497729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 949931784915505242069139541 11132013104478577055497729)
              ·
                refine ⟨8349009828358932791623297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11132013104478577055497729 8349009828358932791623297)
                ·
                  refine ⟨6261757371269199593717473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8349009828358932791623297 6261757371269199593717473)
                  ·
                    refine ⟨4696318028451899695288105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6261757371269199593717473 4696318028451899695288105)
                    ·
                      refine ⟨3522238521338924771466079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696318028451899695288105 3522238521338924771466079)
                      ·
                        rfl

theorem cell23_6859535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 2, 2].length) (baseStart_6859535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859535 prefixEnd_6859535 := by exact prefixLift 6859535
  have htrace : WordTrace (prefixWord ++ tailWord_6859535) baseStart_6859535 baseEnd_6859535 := by
    simpa [prefixWord, tailWord_6859535, baseEnd_6859535] using wordTrace_append hprefix tailTrace_6859535
  have hstable : (prefixWord ++ tailWord_6859535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859535).length < 2 ^ (prefixWord ++ tailWord_6859535).sum := by decide
  have hdescent : baseEnd_6859535 < baseStart_6859535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859544 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_6859544 : Nat := 118140960795 + 6859544 * 2 ^ 59
def prefixEnd_6859544 : Nat := 4983230072969 + 3 ^ 40 * 6859544 * 2
def baseEnd_6859544 : Nat := 3522243142664815236253537

theorem tailTrace_6859544 : CollatzResearch.WordTrace tailWord_6859544 prefixEnd_6859544 3522243142664815236253537 := by
  unfold tailWord_6859544
  simp only [CollatzResearch.WordTrace]
  refine ⟨125094061730525539845544843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166792082307367386460726457 125094061730525539845544843)
  ·
    refine ⟨187641092595788309768317265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125094061730525539845544843 187641092595788309768317265)
    ·
      refine ⟨140730819446841232326237949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187641092595788309768317265 140730819446841232326237949)
      ·
        refine ⟨52774057292565462122339231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140730819446841232326237949 52774057292565462122339231)
        ·
          refine ⟨79161085938848193183508847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52774057292565462122339231 79161085938848193183508847)
          ·
            refine ⟨118741628908272289775263271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79161085938848193183508847 118741628908272289775263271)
            ·
              refine ⟨178112443362408434662894907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118741628908272289775263271 178112443362408434662894907)
              ·
                refine ⟨267168665043612651994342361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178112443362408434662894907 267168665043612651994342361)
                ·
                  refine ⟨200376498782709488995756771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267168665043612651994342361 200376498782709488995756771)
                  ·
                    refine ⟨300564748174064233493635157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200376498782709488995756771 300564748174064233493635157)
                    ·
                      refine ⟨3522243142664815236253537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 300564748174064233493635157 3522243142664815236253537)
                      ·
                        rfl

theorem cell23_6859544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_6859544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859544 prefixEnd_6859544 := by exact prefixLift 6859544
  have htrace : WordTrace (prefixWord ++ tailWord_6859544) baseStart_6859544 baseEnd_6859544 := by
    simpa [prefixWord, tailWord_6859544, baseEnd_6859544] using wordTrace_append hprefix tailTrace_6859544
  have hstable : (prefixWord ++ tailWord_6859544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859544).length < 2 ^ (prefixWord ++ tailWord_6859544).sum := by decide
  have hdescent : baseEnd_6859544 < baseStart_6859544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859551 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 3]
def baseStart_6859551 : Nat := 118140960795 + 6859551 * 2 ^ 59
def prefixEnd_6859551 : Nat := 4983230072969 + 3 ^ 40 * 6859551 * 2
def baseEnd_6859551 : Nat := 3522246737029396708866005

theorem tailTrace_6859551 : CollatzResearch.WordTrace tailWord_6859551 prefixEnd_6859551 3522246737029396708866005 := by
  unfold tailWord_6859551
  simp only [CollatzResearch.WordTrace]
  refine ⟨250188378772025719886594507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166792252514683813257729671 250188378772025719886594507)
  ·
    refine ⟨375282568158038579829891761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250188378772025719886594507 375282568158038579829891761)
    ·
      refine ⟨281461926118528934872418821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375282568158038579829891761 281461926118528934872418821)
      ·
        refine ⟨52774111147224175288578529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281461926118528934872418821 52774111147224175288578529)
        ·
          refine ⟨39580583360418131466433897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52774111147224175288578529 39580583360418131466433897)
          ·
            refine ⟨29685437520313598599825423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39580583360418131466433897 29685437520313598599825423)
            ·
              refine ⟨44528156280470397899738135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29685437520313598599825423 44528156280470397899738135)
              ·
                refine ⟨66792234420705596849607203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44528156280470397899738135 66792234420705596849607203)
                ·
                  refine ⟨100188351631058395274410805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66792234420705596849607203 100188351631058395274410805)
                  ·
                    refine ⟨9392657965411724556976013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100188351631058395274410805 9392657965411724556976013)
                    ·
                      refine ⟨3522246737029396708866005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9392657965411724556976013 3522246737029396708866005)
                      ·
                        rfl

theorem cell23_6859551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_6859551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859551 prefixEnd_6859551 := by exact prefixLift 6859551
  have htrace : WordTrace (prefixWord ++ tailWord_6859551) baseStart_6859551 baseEnd_6859551 := by
    simpa [prefixWord, tailWord_6859551, baseEnd_6859551] using wordTrace_append hprefix tailTrace_6859551
  have hstable : (prefixWord ++ tailWord_6859551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859551).length < 2 ^ (prefixWord ++ tailWord_6859551).sum := by decide
  have hdescent : baseEnd_6859551 < baseStart_6859551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859571 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 1, 7]
def baseStart_6859571 : Nat := 118140960795 + 6859571 * 2 ^ 59
def prefixEnd_6859571 : Nat := 4983230072969 + 3 ^ 40 * 6859571 * 2
def baseEnd_6859571 : Nat := 1174085668880828876871971

theorem tailTrace_6859571 : CollatzResearch.WordTrace tailWord_6859571 prefixEnd_6859571 1174085668880828876871971 := by
  unfold tailWord_6859571
  simp only [CollatzResearch.WordTrace]
  refine ⟨250189108231953263302322567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166792738821302175534881711 250189108231953263302322567)
  ·
    refine ⟨375283662347929894953483851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250189108231953263302322567 375283662347929894953483851)
    ·
      refine ⟨562925493521894842430225777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375283662347929894953483851 562925493521894842430225777)
      ·
        refine ⟨422194120141421131822669333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562925493521894842430225777 422194120141421131822669333)
        ·
          refine ⟨19790349381629115554187625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 422194120141421131822669333 19790349381629115554187625)
          ·
            refine ⟨14842762036221836665640719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19790349381629115554187625 14842762036221836665640719)
            ·
              refine ⟨22264143054332754998461079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14842762036221836665640719 22264143054332754998461079)
              ·
                refine ⟨33396214581499132497691619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22264143054332754998461079 33396214581499132497691619)
                ·
                  refine ⟨50094321872248698746537429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33396214581499132497691619 50094321872248698746537429)
                  ·
                    refine ⟨1174085668880828876871971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50094321872248698746537429 1174085668880828876871971)
                    ·
                      rfl

theorem cell23_6859571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 7].length) (baseStart_6859571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859571 prefixEnd_6859571 := by exact prefixLift 6859571
  have htrace : WordTrace (prefixWord ++ tailWord_6859571) baseStart_6859571 baseEnd_6859571 := by
    simpa [prefixWord, tailWord_6859571, baseEnd_6859571] using wordTrace_append hprefix tailTrace_6859571
  have hstable : (prefixWord ++ tailWord_6859571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859571).length < 2 ^ (prefixWord ++ tailWord_6859571).sum := by decide
  have hdescent : baseEnd_6859571 < baseStart_6859571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859584 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 1, 10]
def baseStart_6859584 : Nat := 118140960795 + 6859584 * 2 ^ 59
def prefixEnd_6859584 : Nat := 4983230072969 + 3 ^ 40 * 6859584 * 2
def baseEnd_6859584 : Nat := 1174087893963665026584451

theorem tailTrace_6859584 : CollatzResearch.WordTrace tailWord_6859584 prefixEnd_6859584 1174087893963665026584451 := by
  unfold tailWord_6859584
  simp only [CollatzResearch.WordTrace]
  refine ⟨125094791190453083261272903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166793054920604111015030537 125094791190453083261272903)
  ·
    refine ⟨187642186785679624891909355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125094791190453083261272903 187642186785679624891909355)
    ·
      refine ⟨281463280178519437337864033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187642186785679624891909355 281463280178519437337864033)
      ·
        refine ⟨211097460133889578003398025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281463280178519437337864033 211097460133889578003398025)
        ·
          refine ⟨158323095100417183502548519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211097460133889578003398025 158323095100417183502548519)
          ·
            refine ⟨237484642650625775253822779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158323095100417183502548519 237484642650625775253822779)
            ·
              refine ⟨356226963975938662880734169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237484642650625775253822779 356226963975938662880734169)
              ·
                refine ⟨267170222981953997160550627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356226963975938662880734169 267170222981953997160550627)
                ·
                  refine ⟨400755334472930995740825941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267170222981953997160550627 400755334472930995740825941)
                  ·
                    refine ⟨1174087893963665026584451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 400755334472930995740825941 1174087893963665026584451)
                    ·
                      rfl

theorem cell23_6859584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_6859584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859584 prefixEnd_6859584 := by exact prefixLift 6859584
  have htrace : WordTrace (prefixWord ++ tailWord_6859584) baseStart_6859584 baseEnd_6859584 := by
    simpa [prefixWord, tailWord_6859584, baseEnd_6859584] using wordTrace_append hprefix tailTrace_6859584
  have hstable : (prefixWord ++ tailWord_6859584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859584).length < 2 ^ (prefixWord ++ tailWord_6859584).sum := by decide
  have hdescent : baseEnd_6859584 < baseStart_6859584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859591 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_6859591 : Nat := 118140960795 + 6859591 * 2 ^ 59
def prefixEnd_6859591 : Nat := 4983230072969 + 3 ^ 40 * 6859591 * 2
def baseEnd_6859591 : Nat := 3522267276255576552365821

theorem tailTrace_6859591 : CollatzResearch.WordTrace tailWord_6859591 prefixEnd_6859591 3522267276255576552365821 := by
  unfold tailWord_6859591
  simp only [CollatzResearch.WordTrace]
  refine ⟨250189837691880806718050627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166793225127920537812033751 250189837691880806718050627)
  ·
    refine ⟨375284756537821210077075941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250189837691880806718050627 375284756537821210077075941)
    ·
      refine ⟨70365891850841476889451739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375284756537821210077075941 70365891850841476889451739)
      ·
        refine ⟨105548837776262215334177609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70365891850841476889451739 105548837776262215334177609)
        ·
          refine ⟨79161628332196661500633207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105548837776262215334177609 79161628332196661500633207)
          ·
            refine ⟨118742442498294992250949811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79161628332196661500633207 118742442498294992250949811)
            ·
              refine ⟨178113663747442488376424717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118742442498294992250949811 178113663747442488376424717)
              ·
                refine ⟨66792623905290933141159269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178113663747442488376424717 66792623905290933141159269)
                ·
                  refine ⟨12523616982242049963967363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66792623905290933141159269 12523616982242049963967363)
                  ·
                    refine ⟨18785425473363074945951045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12523616982242049963967363 18785425473363074945951045)
                    ·
                      refine ⟨3522267276255576552365821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18785425473363074945951045 3522267276255576552365821)
                      ·
                        rfl

theorem cell23_6859591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_6859591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859591 prefixEnd_6859591 := by exact prefixLift 6859591
  have htrace : WordTrace (prefixWord ++ tailWord_6859591) baseStart_6859591 baseEnd_6859591 := by
    simpa [prefixWord, tailWord_6859591, baseEnd_6859591] using wordTrace_append hprefix tailTrace_6859591
  have hstable : (prefixWord ++ tailWord_6859591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859591).length < 2 ^ (prefixWord ++ tailWord_6859591).sum := by decide
  have hdescent : baseEnd_6859591 < baseStart_6859591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859628 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 3]
def baseStart_6859628 : Nat := 118140960795 + 6859628 * 2 ^ 59
def prefixEnd_6859628 : Nat := 4983230072969 + 3 ^ 40 * 6859628 * 2
def baseEnd_6859628 : Nat := 3522286275039792907603151

theorem tailTrace_6859628 : CollatzResearch.WordTrace tailWord_6859628 prefixEnd_6859628 3522286275039792907603151 := by
  unfold tailWord_6859628
  simp only [CollatzResearch.WordTrace]
  refine ⟨125095593596373381018573769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166794124795164508024765025 125095593596373381018573769)
  ·
    refine ⟨93821695197280035763930327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125095593596373381018573769 93821695197280035763930327)
    ·
      refine ⟨140732542795920053645895491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93821695197280035763930327 140732542795920053645895491)
      ·
        refine ⟨211098814193880080468843237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140732542795920053645895491 211098814193880080468843237)
        ·
          refine ⟨39581027661352515087908107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211098814193880080468843237 39581027661352515087908107)
          ·
            refine ⟨59371541492028772631862161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39581027661352515087908107 59371541492028772631862161)
            ·
              refine ⟨44528656119021579473896621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59371541492028772631862161 44528656119021579473896621)
              ·
                refine ⟨16698246044633092302711233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44528656119021579473896621 16698246044633092302711233)
                ·
                  refine ⟨12523684533474819227033425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16698246044633092302711233 12523684533474819227033425)
                  ·
                    refine ⟨9392763400106114420275069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12523684533474819227033425 9392763400106114420275069)
                    ·
                      refine ⟨3522286275039792907603151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9392763400106114420275069 3522286275039792907603151)
                      ·
                        rfl

theorem cell23_6859628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_6859628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859628 prefixEnd_6859628 := by exact prefixLift 6859628
  have htrace : WordTrace (prefixWord ++ tailWord_6859628) baseStart_6859628 baseEnd_6859628 := by
    simpa [prefixWord, tailWord_6859628, baseEnd_6859628] using wordTrace_append hprefix tailTrace_6859628
  have hstable : (prefixWord ++ tailWord_6859628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859628).length < 2 ^ (prefixWord ++ tailWord_6859628).sum := by decide
  have hdescent : baseEnd_6859628 < baseStart_6859628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859635 : List Nat := [1, 1, 1, 2, 2, 1, 7, 3, 1, 4]
def baseStart_6859635 : Nat := 118140960795 + 6859635 * 2 ^ 59
def prefixEnd_6859635 : Nat := 4983230072969 + 3 ^ 40 * 6859635 * 2
def baseEnd_6859635 : Nat := 1174096623134791460071873

theorem tailTrace_6859635 : CollatzResearch.WordTrace tailWord_6859635 prefixEnd_6859635 1174096623134791460071873 := by
  unfold tailWord_6859635
  simp only [CollatzResearch.WordTrace]
  refine ⟨250191442503721402232652359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166794295002480934821768239 250191442503721402232652359)
  ·
    refine ⟨375287163755582103348978539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250191442503721402232652359 375287163755582103348978539)
    ·
      refine ⟨562930745633373155023467809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375287163755582103348978539 562930745633373155023467809)
      ·
        refine ⟨422198059225029866267600857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562930745633373155023467809 422198059225029866267600857)
        ·
          refine ⟨316648544418772399700700643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422198059225029866267600857 316648544418772399700700643)
          ·
            refine ⟨474972816628158599551050965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316648544418772399700700643 474972816628158599551050965)
            ·
              refine ⟨11132175389722467176977757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 474972816628158599551050965 11132175389722467176977757)
              ·
                refine ⟨4174565771145925191366659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11132175389722467176977757 4174565771145925191366659)
                ·
                  refine ⟨6261848656718887787049989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4174565771145925191366659 6261848656718887787049989)
                  ·
                    refine ⟨1174096623134791460071873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6261848656718887787049989 1174096623134791460071873)
                    ·
                      rfl

theorem cell23_6859635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 1, 4].length) (baseStart_6859635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859635 prefixEnd_6859635 := by exact prefixLift 6859635
  have htrace : WordTrace (prefixWord ++ tailWord_6859635) baseStart_6859635 baseEnd_6859635 := by
    simpa [prefixWord, tailWord_6859635, baseEnd_6859635] using wordTrace_append hprefix tailTrace_6859635
  have hstable : (prefixWord ++ tailWord_6859635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859635).length < 2 ^ (prefixWord ++ tailWord_6859635).sum := by decide
  have hdescent : baseEnd_6859635 < baseStart_6859635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859691 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 1, 6]
def baseStart_6859691 : Nat := 118140960795 + 6859691 * 2 ^ 59
def prefixEnd_6859691 : Nat := 4983230072969 + 3 ^ 40 * 6859691 * 2
def baseEnd_6859691 : Nat := 1174106208107008720371787

theorem tailTrace_6859691 : CollatzResearch.WordTrace tailWord_6859691 prefixEnd_6859691 1174106208107008720371787 := by
  unfold tailWord_6859691
  simp only [CollatzResearch.WordTrace]
  refine ⟨250193484991518523796690927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166795656661012349197793951 250193484991518523796690927)
  ·
    refine ⟨375290227487277785695036391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250193484991518523796690927 375290227487277785695036391)
    ·
      refine ⟨562935341230916678542554587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375290227487277785695036391 562935341230916678542554587)
      ·
        refine ⟨844403011846375017813831881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562935341230916678542554587 844403011846375017813831881)
        ·
          refine ⟨633302258884781263360373911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 844403011846375017813831881 633302258884781263360373911)
          ·
            refine ⟨949953388327171895040560867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633302258884781263360373911 949953388327171895040560867)
            ·
              refine ⟨1424930082490757842560841301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949953388327171895040560867 1424930082490757842560841301)
              ·
                refine ⟨16698399404188568467509859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1424930082490757842560841301 16698399404188568467509859)
                ·
                  refine ⟨25047599106282852701264789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16698399404188568467509859 25047599106282852701264789)
                  ·
                    refine ⟨1174106208107008720371787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25047599106282852701264789 1174106208107008720371787)
                    ·
                      rfl

theorem cell23_6859691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 6].length) (baseStart_6859691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859691 prefixEnd_6859691 := by exact prefixLift 6859691
  have htrace : WordTrace (prefixWord ++ tailWord_6859691) baseStart_6859691 baseEnd_6859691 := by
    simpa [prefixWord, tailWord_6859691, baseEnd_6859691] using wordTrace_append hprefix tailTrace_6859691
  have hstable : (prefixWord ++ tailWord_6859691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859691).length < 2 ^ (prefixWord ++ tailWord_6859691).sum := by decide
  have hdescent : baseEnd_6859691 < baseStart_6859691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859709 : List Nat := [1, 4, 1, 2, 4, 1, 1, 4, 1, 1, 3]
def baseStart_6859709 : Nat := 118140960795 + 6859709 * 2 ^ 59
def prefixEnd_6859709 : Nat := 4983230072969 + 3 ^ 40 * 6859709 * 2
def baseEnd_6859709 : Nat := 3522327866972807090690279

theorem tailTrace_6859709 : CollatzResearch.WordTrace tailWord_6859709 prefixEnd_6859709 3522327866972807090690279 := by
  unfold tailWord_6859709
  simp only [CollatzResearch.WordTrace]
  refine ⟨250194141505453312870846181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166796094336968875247230787 250194141505453312870846181)
  ·
    refine ⟨46911401532272496163283659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250194141505453312870846181 46911401532272496163283659)
    ·
      refine ⟨70367102298408744244925489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46911401532272496163283659 70367102298408744244925489)
      ·
        refine ⟨52775326723806558183694117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70367102298408744244925489 52775326723806558183694117)
        ·
          refine ⟨9895373760713729659442647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52775326723806558183694117 9895373760713729659442647)
          ·
            refine ⟨14843060641070594489163971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9895373760713729659442647 14843060641070594489163971)
            ·
              refine ⟨22264590961605891733745957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14843060641070594489163971 22264590961605891733745957)
              ·
                refine ⟨4174610805301104700077367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22264590961605891733745957 4174610805301104700077367)
                ·
                  refine ⟨6261916207951657050116051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4174610805301104700077367 6261916207951657050116051)
                  ·
                    refine ⟨9392874311927485575174077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6261916207951657050116051 9392874311927485575174077)
                    ·
                      refine ⟨3522327866972807090690279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9392874311927485575174077 3522327866972807090690279)
                      ·
                        rfl

theorem cell23_6859709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_6859709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859709 prefixEnd_6859709 := by exact prefixLift 6859709
  have htrace : WordTrace (prefixWord ++ tailWord_6859709) baseStart_6859709 baseEnd_6859709 := by
    simpa [prefixWord, tailWord_6859709, baseEnd_6859709] using wordTrace_append hprefix tailTrace_6859709
  have hstable : (prefixWord ++ tailWord_6859709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859709).length < 2 ^ (prefixWord ++ tailWord_6859709).sum := by decide
  have hdescent : baseEnd_6859709 < baseStart_6859709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859711 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 6]
def baseStart_6859711 : Nat := 118140960795 + 6859711 * 2 ^ 59
def prefixEnd_6859711 : Nat := 4983230072969 + 3 ^ 40 * 6859711 * 2
def baseEnd_6859711 : Nat := 3522328893934116082865269

theorem tailTrace_6859711 : CollatzResearch.WordTrace tailWord_6859711 prefixEnd_6859711 3522328893934116082865269 := by
  unfold tailWord_6859711
  simp only [CollatzResearch.WordTrace]
  refine ⟨250194214451446067212418987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166796142967630711474945991 250194214451446067212418987)
  ·
    refine ⟨375291321677169100818628481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250194214451446067212418987 375291321677169100818628481)
    ·
      refine ⟨281468491257876825613971361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375291321677169100818628481 281468491257876825613971361)
      ·
        refine ⟨211101368443407619210478521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281468491257876825613971361 211101368443407619210478521)
        ·
          refine ⟨158326026332555714407858891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211101368443407619210478521 158326026332555714407858891)
          ·
            refine ⟨237489039498833571611788337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158326026332555714407858891 237489039498833571611788337)
            ·
              refine ⟨178116779624125178708841253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237489039498833571611788337 178116779624125178708841253)
              ·
                refine ⟨33396896179523471007907735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178116779624125178708841253 33396896179523471007907735)
                ·
                  refine ⟨50095344269285206511861603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33396896179523471007907735 50095344269285206511861603)
                  ·
                    refine ⟨75143016403927809767792405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50095344269285206511861603 75143016403927809767792405)
                    ·
                      refine ⟨3522328893934116082865269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75143016403927809767792405 3522328893934116082865269)
                      ·
                        rfl

theorem cell23_6859711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_6859711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859711 prefixEnd_6859711 := by exact prefixLift 6859711
  have htrace : WordTrace (prefixWord ++ tailWord_6859711) baseStart_6859711 baseEnd_6859711 := by
    simpa [prefixWord, tailWord_6859711, baseEnd_6859711] using wordTrace_append hprefix tailTrace_6859711
  have hstable : (prefixWord ++ tailWord_6859711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859711).length < 2 ^ (prefixWord ++ tailWord_6859711).sum := by decide
  have hdescent : baseEnd_6859711 < baseStart_6859711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859732 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_6859732 : Nat := 118140960795 + 6859732 * 2 ^ 59
def prefixEnd_6859732 : Nat := 4983230072969 + 3 ^ 40 * 6859732 * 2
def baseEnd_6859732 : Nat := 3522339677027860500702673

theorem tailTrace_6859732 : CollatzResearch.WordTrace tailWord_6859732 prefixEnd_6859732 3522339677027860500702673 := by
  unfold tailWord_6859732
  simp only [CollatzResearch.WordTrace]
  refine ⟨125097490192184993899466725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166796653589579991865955633 125097490192184993899466725)
  ·
    refine ⟨23455779411034686356150011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125097490192184993899466725 23455779411034686356150011)
    ·
      refine ⟨35183669116552029534225017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23455779411034686356150011 35183669116552029534225017)
      ·
        refine ⟨26387751837414022150668763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35183669116552029534225017 26387751837414022150668763)
        ·
          refine ⟨39581627756121033226003145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26387751837414022150668763 39581627756121033226003145)
          ·
            refine ⟨29686220817090774919502359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39581627756121033226003145 29686220817090774919502359)
            ·
              refine ⟨44529331225636162379253539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29686220817090774919502359 44529331225636162379253539)
              ·
                refine ⟨66793996838454243568880309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44529331225636162379253539 66793996838454243568880309)
                ·
                  refine ⟨6261937203605085334582529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66793996838454243568880309 6261937203605085334582529)
                  ·
                    refine ⟨4696452902703814000936897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6261937203605085334582529 4696452902703814000936897)
                    ·
                      refine ⟨3522339677027860500702673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696452902703814000936897 3522339677027860500702673)
                      ·
                        rfl

theorem cell23_6859732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_6859732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859732 prefixEnd_6859732 := by exact prefixLift 6859732
  have htrace : WordTrace (prefixWord ++ tailWord_6859732) baseStart_6859732 baseEnd_6859732 := by
    simpa [prefixWord, tailWord_6859732, baseEnd_6859732] using wordTrace_append hprefix tailTrace_6859732
  have hstable : (prefixWord ++ tailWord_6859732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859732).length < 2 ^ (prefixWord ++ tailWord_6859732).sum := by decide
  have hdescent : baseEnd_6859732 < baseStart_6859732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859748 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_6859748 : Nat := 118140960795 + 6859748 * 2 ^ 59
def prefixEnd_6859748 : Nat := 4983230072969 + 3 ^ 40 * 6859748 * 2
def baseEnd_6859748 : Nat := 3522347892718332438102599

theorem tailTrace_6859748 : CollatzResearch.WordTrace tailWord_6859748 prefixEnd_6859748 3522347892718332438102599 := by
  unfold tailWord_6859748
  simp only [CollatzResearch.WordTrace]
  refine ⟨125097781976156011265757949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166797042634874681687677265 125097781976156011265757949)
  ·
    refine ⟨46911668241058504224659231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125097781976156011265757949 46911668241058504224659231)
    ·
      refine ⟨70367502361587756336988847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46911668241058504224659231 70367502361587756336988847)
      ·
        refine ⟨105551253542381634505483271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70367502361587756336988847 105551253542381634505483271)
        ·
          refine ⟨158326880313572451758224907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105551253542381634505483271 158326880313572451758224907)
          ·
            refine ⟨237490320470358677637337361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158326880313572451758224907 237490320470358677637337361)
            ·
              refine ⟨178117740352769008228003021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237490320470358677637337361 178117740352769008228003021)
              ·
                refine ⟨66794152632288378085501133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178117740352769008228003021 66794152632288378085501133)
                ·
                  refine ⟨25047807237108141782062925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66794152632288378085501133 25047807237108141782062925)
                  ·
                    refine ⟨9392927713915553168273597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25047807237108141782062925 9392927713915553168273597)
                    ·
                      refine ⟨3522347892718332438102599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9392927713915553168273597 3522347892718332438102599)
                      ·
                        rfl

theorem cell23_6859748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_6859748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859748 prefixEnd_6859748 := by exact prefixLift 6859748
  have htrace : WordTrace (prefixWord ++ tailWord_6859748) baseStart_6859748 baseEnd_6859748 := by
    simpa [prefixWord, tailWord_6859748, baseEnd_6859748] using wordTrace_append hprefix tailTrace_6859748
  have hstable : (prefixWord ++ tailWord_6859748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859748).length < 2 ^ (prefixWord ++ tailWord_6859748).sum := by decide
  have hdescent : baseEnd_6859748 < baseStart_6859748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859752 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_6859752 : Nat := 118140960795 + 6859752 * 2 ^ 59
def prefixEnd_6859752 : Nat := 4983230072969 + 3 ^ 40 * 6859752 * 2
def baseEnd_6859752 : Nat := 3522349946640950422452581

theorem tailTrace_6859752 : CollatzResearch.WordTrace tailWord_6859752 prefixEnd_6859752 3522349946640950422452581 := by
  unfold tailWord_6859752
  simp only [CollatzResearch.WordTrace]
  refine ⟨125097854922148765607330755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166797139896198354143107673 125097854922148765607330755)
  ·
    refine ⟨187646782383223148410996133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125097854922148765607330755 187646782383223148410996133)
    ·
      refine ⟨35183771696854340327061775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187646782383223148410996133 35183771696854340327061775)
      ·
        refine ⟨52775657545281510490592663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35183771696854340327061775 52775657545281510490592663)
        ·
          refine ⟨79163486317922265735888995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52775657545281510490592663 79163486317922265735888995)
          ·
            refine ⟨118745229476883398603833493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79163486317922265735888995 118745229476883398603833493)
            ·
              refine ⟨5566182631728909309554695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118745229476883398603833493 5566182631728909309554695)
              ·
                refine ⟨8349273947593363964332043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566182631728909309554695 8349273947593363964332043)
                ·
                  refine ⟨12523910921390045946498065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8349273947593363964332043 12523910921390045946498065)
                  ·
                    refine ⟨9392933191042534459873549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12523910921390045946498065 9392933191042534459873549)
                    ·
                      refine ⟨3522349946640950422452581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9392933191042534459873549 3522349946640950422452581)
                      ·
                        rfl

theorem cell23_6859752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_6859752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859752 prefixEnd_6859752 := by exact prefixLift 6859752
  have htrace : WordTrace (prefixWord ++ tailWord_6859752) baseStart_6859752 baseEnd_6859752 := by
    simpa [prefixWord, tailWord_6859752, baseEnd_6859752] using wordTrace_append hprefix tailTrace_6859752
  have hstable : (prefixWord ++ tailWord_6859752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859752).length < 2 ^ (prefixWord ++ tailWord_6859752).sum := by decide
  have hdescent : baseEnd_6859752 < baseStart_6859752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859766 : List Nat := [5, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_6859766 : Nat := 118140960795 + 6859766 * 2 ^ 59
def prefixEnd_6859766 : Nat := 4983230072969 + 3 ^ 40 * 6859766 * 2
def baseEnd_6859766 : Nat := 3522357135370113367677517

theorem tailTrace_6859766 : CollatzResearch.WordTrace tailWord_6859766 prefixEnd_6859766 3522357135370113367677517 := by
  unfold tailWord_6859766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15637263779140425725354447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166797480310831207737114101 15637263779140425725354447)
  ·
    refine ⟨23455895668710638588031671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15637263779140425725354447 23455895668710638588031671)
    ·
      refine ⟨35183843503065957882047507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23455895668710638588031671 35183843503065957882047507)
      ·
        refine ⟨52775765254598936823071261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35183843503065957882047507 52775765254598936823071261)
        ·
          refine ⟨19790911970474601308651723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52775765254598936823071261 19790911970474601308651723)
          ·
            refine ⟨29686367955711901962977585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19790911970474601308651723 29686367955711901962977585)
            ·
              refine ⟨22264775966783926472233189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29686367955711901962977585 22264775966783926472233189)
              ·
                refine ⟨4174645493771986213543723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22264775966783926472233189 4174645493771986213543723)
                ·
                  refine ⟨6261968240657979320315585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4174645493771986213543723 6261968240657979320315585)
                  ·
                    refine ⟨4696476180493484490236689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6261968240657979320315585 4696476180493484490236689)
                    ·
                      refine ⟨3522357135370113367677517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696476180493484490236689 3522357135370113367677517)
                      ·
                        rfl

theorem cell23_6859766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_6859766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859766 prefixEnd_6859766 := by exact prefixLift 6859766
  have htrace : WordTrace (prefixWord ++ tailWord_6859766) baseStart_6859766 baseEnd_6859766 := by
    simpa [prefixWord, tailWord_6859766, baseEnd_6859766] using wordTrace_append hprefix tailTrace_6859766
  have hstable : (prefixWord ++ tailWord_6859766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859766).length < 2 ^ (prefixWord ++ tailWord_6859766).sum := by decide
  have hdescent : baseEnd_6859766 < baseStart_6859766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859791 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_6859791 : Nat := 118140960795 + 6859791 * 2 ^ 59
def prefixEnd_6859791 : Nat := 4983230072969 + 3 ^ 40 * 6859791 * 2
def baseEnd_6859791 : Nat := 3522369972386475769864901

theorem tailTrace_6859791 : CollatzResearch.WordTrace tailWord_6859791 prefixEnd_6859791 3522369972386475769864901 := by
  unfold tailWord_6859791
  simp only [CollatzResearch.WordTrace]
  refine ⟨250197132291156240875331227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166798088194104160583554151 250197132291156240875331227)
  ·
    refine ⟨375295698436734361312996841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250197132291156240875331227 375295698436734361312996841)
    ·
      refine ⟨281471773827550770984747631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375295698436734361312996841 281471773827550770984747631)
      ·
        refine ⟨422207660741326156477121447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281471773827550770984747631 422207660741326156477121447)
        ·
          refine ⟨633311491111989234715682171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422207660741326156477121447 633311491111989234715682171)
          ·
            refine ⟨949967236667983852073523257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633311491111989234715682171 949967236667983852073523257)
            ·
              refine ⟨712475427500987889055142443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949967236667983852073523257 712475427500987889055142443)
              ·
                refine ⟨1068713141251481833582713665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712475427500987889055142443 1068713141251481833582713665)
                ·
                  refine ⟨801534855938611375187035249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1068713141251481833582713665 801534855938611375187035249)
                  ·
                    refine ⟨601151141953958531390276437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 801534855938611375187035249 601151141953958531390276437)
                    ·
                      refine ⟨3522369972386475769864901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 601151141953958531390276437 3522369972386475769864901)
                      ·
                        rfl

theorem cell23_6859791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_6859791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859791 prefixEnd_6859791 := by exact prefixLift 6859791
  have htrace : WordTrace (prefixWord ++ tailWord_6859791) baseStart_6859791 baseEnd_6859791 := by
    simpa [prefixWord, tailWord_6859791, baseEnd_6859791] using wordTrace_append hprefix tailTrace_6859791
  have hstable : (prefixWord ++ tailWord_6859791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859791).length < 2 ^ (prefixWord ++ tailWord_6859791).sum := by decide
  have hdescent : baseEnd_6859791 < baseStart_6859791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859879 : List Nat := [1, 1, 5, 1, 1, 5, 2, 2, 5]
def baseStart_6859879 : Nat := 118140960795 + 6859879 * 2 ^ 59
def prefixEnd_6859879 : Nat := 4983230072969 + 3 ^ 40 * 6859879 * 2
def baseEnd_6859879 : Nat := 391379462076007936173833

theorem tailTrace_6859879 : CollatzResearch.WordTrace tailWord_6859879 prefixEnd_6859879 391379462076007936173833 := by
  unfold tailWord_6859879
  simp only [CollatzResearch.WordTrace]
  refine ⟨250200341914837431904534691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166800227943224954603023127 250200341914837431904534691)
  ·
    refine ⟨375300512872256147856802037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250200341914837431904534691 375300512872256147856802037)
    ·
      refine ⟨35184423081774013861575191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 375300512872256147856802037 35184423081774013861575191)
      ·
        refine ⟨52776634622661020792362787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35184423081774013861575191 52776634622661020792362787)
        ·
          refine ⟨79164951933991531188544181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52776634622661020792362787 79164951933991531188544181)
          ·
            refine ⟨7421714243811706048926017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79164951933991531188544181 7421714243811706048926017)
            ·
              refine ⟨5566285682858779536694513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7421714243811706048926017 5566285682858779536694513)
              ·
                refine ⟨4174714262144084652520885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5566285682858779536694513 4174714262144084652520885)
                ·
                  refine ⟨391379462076007936173833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4174714262144084652520885 391379462076007936173833)
                  ·
                    rfl

theorem cell23_6859879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 5].length) (baseStart_6859879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859879 prefixEnd_6859879 := by exact prefixLift 6859879
  have htrace : WordTrace (prefixWord ++ tailWord_6859879) baseStart_6859879 baseEnd_6859879 := by
    simpa [prefixWord, tailWord_6859879, baseEnd_6859879] using wordTrace_append hprefix tailTrace_6859879
  have hstable : (prefixWord ++ tailWord_6859879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859879).length < 2 ^ (prefixWord ++ tailWord_6859879).sum := by decide
  have hdescent : baseEnd_6859879 < baseStart_6859879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859882 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_6859882 : Nat := 118140960795 + 6859882 * 2 ^ 59
def prefixEnd_6859882 : Nat := 4983230072969 + 3 ^ 40 * 6859882 * 2
def baseEnd_6859882 : Nat := 3522416699126034913826983

theorem tailTrace_6859882 : CollatzResearch.WordTrace tailWord_6859882 prefixEnd_6859882 3522416699126034913826983 := by
  unfold tailWord_6859882
  simp only [CollatzResearch.WordTrace]
  refine ⟨62550112833456640854223475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166800300889217708944595933 62550112833456640854223475)
  ·
    refine ⟨93825169250184961281335213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62550112833456640854223475 93825169250184961281335213)
    ·
      refine ⟨35184438468819360480500705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93825169250184961281335213 35184438468819360480500705)
      ·
        refine ⟨26388328851614520360375529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35184438468819360480500705 26388328851614520360375529)
        ·
          refine ⟨19791246638710890270281647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26388328851614520360375529 19791246638710890270281647)
          ·
            refine ⟨29686869958066335405422471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19791246638710890270281647 29686869958066335405422471)
            ·
              refine ⟨44530304937099503108133707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29686869958066335405422471 44530304937099503108133707)
              ·
                refine ⟨66795457405649254662200561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44530304937099503108133707 66795457405649254662200561)
                ·
                  refine ⟨50096593054236940996650421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66795457405649254662200561 50096593054236940996650421)
                  ·
                    refine ⟨4696555598834713218435977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50096593054236940996650421 4696555598834713218435977)
                    ·
                      refine ⟨3522416699126034913826983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696555598834713218435977 3522416699126034913826983)
                      ·
                        rfl

theorem cell23_6859882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_6859882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859882 prefixEnd_6859882 := by exact prefixLift 6859882
  have htrace : WordTrace (prefixWord ++ tailWord_6859882) baseStart_6859882 baseEnd_6859882 := by
    simpa [prefixWord, tailWord_6859882, baseEnd_6859882] using wordTrace_append hprefix tailTrace_6859882
  have hstable : (prefixWord ++ tailWord_6859882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859882).length < 2 ^ (prefixWord ++ tailWord_6859882).sum := by decide
  have hdescent : baseEnd_6859882 < baseStart_6859882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
