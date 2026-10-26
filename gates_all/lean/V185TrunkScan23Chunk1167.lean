import V185TrunkScan23Chunk1166

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6913655 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_6913655 : Nat := 118140960795 + 6913655 * 2 ^ 59
def prefixEnd_6913655 : Nat := 4983230072969 + 3 ^ 40 * 6913655 * 2
def baseEnd_6913655 : Nat := 3550028094360253026717185

theorem tailTrace_6913655 : CollatzResearch.WordTrace tailWord_6913655 prefixEnd_6913655 3550028094360253026717185 := by
  unfold tailWord_6913655
  simp only [CollatzResearch.WordTrace]
  refine ⟨252161713768016168114142419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168107809178677445409428279 252161713768016168114142419)
  ·
    refine ⟨378242570652024252171213629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252161713768016168114142419 378242570652024252171213629)
    ·
      refine ⟨141840963994509094564205111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378242570652024252171213629 141840963994509094564205111)
      ·
        refine ⟨212761445991763641846307667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141840963994509094564205111 212761445991763641846307667)
        ·
          refine ⟨319142168987645462769461501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212761445991763641846307667 319142168987645462769461501)
          ·
            refine ⟨119678313370367048538548063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319142168987645462769461501 119678313370367048538548063)
            ·
              refine ⟨179517470055550572807822095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119678313370367048538548063 179517470055550572807822095)
              ·
                refine ⟨269276205083325859211733143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179517470055550572807822095 269276205083325859211733143)
                ·
                  refine ⟨403914307624988788817599715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269276205083325859211733143 403914307624988788817599715)
                  ·
                    refine ⟨605871461437483183226399573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 403914307624988788817599715 605871461437483183226399573)
                    ·
                      refine ⟨3550028094360253026717185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 605871461437483183226399573 3550028094360253026717185)
                      ·
                        rfl

theorem cell23_6913655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_6913655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913655 prefixEnd_6913655 := by exact prefixLift 6913655
  have htrace : WordTrace (prefixWord ++ tailWord_6913655) baseStart_6913655 baseEnd_6913655 := by
    simpa [prefixWord, tailWord_6913655, baseEnd_6913655] using wordTrace_append hprefix tailTrace_6913655
  have hstable : (prefixWord ++ tailWord_6913655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913655).length < 2 ^ (prefixWord ++ tailWord_6913655).sum := by decide
  have hdescent : baseEnd_6913655 < baseStart_6913655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913673 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 2, 2, 2]
def baseStart_6913673 : Nat := 118140960795 + 6913673 * 2 ^ 59
def prefixEnd_6913673 : Nat := 4983230072969 + 3 ^ 40 * 6913673 * 2
def baseEnd_6913673 : Nat := 3550037337012033956292103

theorem tailTrace_6913673 : CollatzResearch.WordTrace tailWord_6913673 prefixEnd_6913673 3550037337012033956292103 := by
  unfold tailWord_6913673
  simp only [CollatzResearch.WordTrace]
  refine ⟨252162370281950957188297673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168108246854633971458865115 252162370281950957188297673)
  ·
    refine ⟨189121777711463217891223255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252162370281950957188297673 189121777711463217891223255)
    ·
      refine ⟨283682666567194826836834883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189121777711463217891223255 283682666567194826836834883)
      ·
        refine ⟨425523999850792240255252325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283682666567194826836834883 425523999850792240255252325)
        ·
          refine ⟨79785749972023545047859811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425523999850792240255252325 79785749972023545047859811)
          ·
            refine ⟨119678624958035317571789717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79785749972023545047859811 119678624958035317571789717)
            ·
              refine ⟨5609935544907905511177643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119678624958035317571789717 5609935544907905511177643)
              ·
                refine ⟨8414903317361858266766465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5609935544907905511177643 8414903317361858266766465)
                ·
                  refine ⟨6311177488021393700074849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8414903317361858266766465 6311177488021393700074849)
                  ·
                    refine ⟨4733383116016045275056137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6311177488021393700074849 4733383116016045275056137)
                    ·
                      refine ⟨3550037337012033956292103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4733383116016045275056137 3550037337012033956292103)
                      ·
                        rfl

theorem cell23_6913673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 2, 2, 2].length) (baseStart_6913673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913673 prefixEnd_6913673 := by exact prefixLift 6913673
  have htrace : WordTrace (prefixWord ++ tailWord_6913673) baseStart_6913673 baseEnd_6913673 := by
    simpa [prefixWord, tailWord_6913673, baseEnd_6913673] using wordTrace_append hprefix tailTrace_6913673
  have hstable : (prefixWord ++ tailWord_6913673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913673).length < 2 ^ (prefixWord ++ tailWord_6913673).sum := by decide
  have hdescent : baseEnd_6913673 < baseStart_6913673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913709 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_6913709 : Nat := 118140960795 + 6913709 * 2 ^ 59
def prefixEnd_6913709 : Nat := 4983230072969 + 3 ^ 40 * 6913709 * 2
def baseEnd_6913709 : Nat := 1183351940771865271813979

theorem tailTrace_6913709 : CollatzResearch.WordTrace tailWord_6913709 prefixEnd_6913709 1183351940771865271813979 := by
  unfold tailWord_6913709
  simp only [CollatzResearch.WordTrace]
  refine ⟨252163683309820535336608181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168109122206547023557738787 252163683309820535336608181)
  ·
    refine ⟨23640345310295675187807017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252163683309820535336608181 23640345310295675187807017)
    ·
      refine ⟨17730258982721756390855263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23640345310295675187807017 17730258982721756390855263)
      ·
        refine ⟨26595388474082634586282895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17730258982721756390855263 26595388474082634586282895)
        ·
          refine ⟨39893082711123951879424343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26595388474082634586282895 39893082711123951879424343)
          ·
            refine ⟨59839624066685927819136515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39893082711123951879424343 59839624066685927819136515)
            ·
              refine ⟨89759436100028891728704773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59839624066685927819136515 89759436100028891728704773)
              ·
                refine ⟨16829894268755417199132145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89759436100028891728704773 16829894268755417199132145)
                ·
                  refine ⟨12622420701566562899349109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16829894268755417199132145 12622420701566562899349109)
                  ·
                    refine ⟨1183351940771865271813979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12622420701566562899349109 1183351940771865271813979)
                    ·
                      rfl

theorem cell23_6913709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_6913709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913709 prefixEnd_6913709 := by exact prefixLift 6913709
  have htrace : WordTrace (prefixWord ++ tailWord_6913709) baseStart_6913709 baseEnd_6913709 := by
    simpa [prefixWord, tailWord_6913709, baseEnd_6913709] using wordTrace_append hprefix tailTrace_6913709
  have hstable : (prefixWord ++ tailWord_6913709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913709).length < 2 ^ (prefixWord ++ tailWord_6913709).sum := by decide
  have hdescent : baseEnd_6913709 < baseStart_6913709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913746 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_6913746 : Nat := 118140960795 + 6913746 * 2 ^ 59
def prefixEnd_6913746 : Nat := 4983230072969 + 3 ^ 40 * 6913746 * 2
def baseEnd_6913746 : Nat := 3550074821099812170679267

theorem tailTrace_6913746 : CollatzResearch.WordTrace tailWord_6913746 prefixEnd_6913746 3550074821099812170679267 := by
  unfold tailWord_6913746
  simp only [CollatzResearch.WordTrace]
  refine ⟨63041258202671622663926273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168110021873790993770470061 63041258202671622663926273)
  ·
    refine ⟨47280943652003716997944705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63041258202671622663926273 47280943652003716997944705)
    ·
      refine ⟨35460707739002787748458529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47280943652003716997944705 35460707739002787748458529)
      ·
        refine ⟨26595530804252090811343897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35460707739002787748458529 26595530804252090811343897)
        ·
          refine ⟨19946648103189068108507923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26595530804252090811343897 19946648103189068108507923)
          ·
            refine ⟨29919972154783602162761885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19946648103189068108507923 29919972154783602162761885)
            ·
              refine ⟨11219989558043850811035707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29919972154783602162761885 11219989558043850811035707)
              ·
                refine ⟨16829984337065776216553561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11219989558043850811035707 16829984337065776216553561)
                ·
                  refine ⟨12622488252799332162415171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16829984337065776216553561 12622488252799332162415171)
                  ·
                    refine ⟨18933732379198998243622757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12622488252799332162415171 18933732379198998243622757)
                    ·
                      refine ⟨3550074821099812170679267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18933732379198998243622757 3550074821099812170679267)
                      ·
                        rfl

theorem cell23_6913746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_6913746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913746 prefixEnd_6913746 := by exact prefixLift 6913746
  have htrace : WordTrace (prefixWord ++ tailWord_6913746) baseStart_6913746 baseEnd_6913746 := by
    simpa [prefixWord, tailWord_6913746, baseEnd_6913746] using wordTrace_append hprefix tailTrace_6913746
  have hstable : (prefixWord ++ tailWord_6913746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913746).length < 2 ^ (prefixWord ++ tailWord_6913746).sum := by decide
  have hdescent : baseEnd_6913746 < baseStart_6913746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913752 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 8]
def baseStart_6913752 : Nat := 118140960795 + 6913752 * 2 ^ 59
def prefixEnd_6913752 : Nat := 4983230072969 + 3 ^ 40 * 6913752 * 2
def baseEnd_6913752 : Nat := 394453100220415460800471

theorem tailTrace_6913752 : CollatzResearch.WordTrace tailWord_6913752 prefixEnd_6913752 394453100220415460800471 := by
  unfold tailWord_6913752
  simp only [CollatzResearch.WordTrace]
  refine ⟨126082625824332376840211755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168110167765776502453615673 126082625824332376840211755)
  ·
    refine ⟨189123938736498565260317633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126082625824332376840211755 189123938736498565260317633)
    ·
      refine ⟨141842954052373923945238225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189123938736498565260317633 141842954052373923945238225)
      ·
        refine ⟨106382215539280442958928669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141842954052373923945238225 106382215539280442958928669)
        ·
          refine ⟨39893330827230166109598251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106382215539280442958928669 39893330827230166109598251)
          ·
            refine ⟨59839996240845249164397377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39893330827230166109598251 59839996240845249164397377)
            ·
              refine ⟨44879997180633936873298033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59839996240845249164397377 44879997180633936873298033)
              ·
                refine ⟨33659997885475452654973525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44879997180633936873298033 33659997885475452654973525)
                ·
                  refine ⟨394453100220415460800471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33659997885475452654973525 394453100220415460800471)
                  ·
                    rfl

theorem cell23_6913752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 8].length) (baseStart_6913752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913752 prefixEnd_6913752 := by exact prefixLift 6913752
  have htrace : WordTrace (prefixWord ++ tailWord_6913752) baseStart_6913752 baseEnd_6913752 := by
    simpa [prefixWord, tailWord_6913752, baseEnd_6913752] using wordTrace_append hprefix tailTrace_6913752
  have hstable : (prefixWord ++ tailWord_6913752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913752).length < 2 ^ (prefixWord ++ tailWord_6913752).sum := by decide
  have hdescent : baseEnd_6913752 < baseStart_6913752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913772 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_6913772 : Nat := 118140960795 + 6913772 * 2 ^ 59
def prefixEnd_6913772 : Nat := 4983230072969 + 3 ^ 40 * 6913772 * 2
def baseEnd_6913772 : Nat := 3550088171596829068954147

theorem tailTrace_6913772 : CollatzResearch.WordTrace tailWord_6913772 prefixEnd_6913772 3550088171596829068954147 := by
  unfold tailWord_6913772
  simp only [CollatzResearch.WordTrace]
  refine ⟨126082990554296148548075785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168110654072394864730767713 126082990554296148548075785)
  ·
    refine ⟨94562242915722111411056839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126082990554296148548075785 94562242915722111411056839)
    ·
      refine ⟨141843364373583167116585259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94562242915722111411056839 141843364373583167116585259)
      ·
        refine ⟨212765046560374750674877889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141843364373583167116585259 212765046560374750674877889)
        ·
          refine ⟨159573784920281063006158417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212765046560374750674877889 159573784920281063006158417)
          ·
            refine ⟨119680338690210797254618813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159573784920281063006158417 119680338690210797254618813)
            ·
              refine ⟨44880127008829048970482055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119680338690210797254618813 44880127008829048970482055)
              ·
                refine ⟨67320190513243573455723083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44880127008829048970482055 67320190513243573455723083)
                ·
                  refine ⟨100980285769865360183584625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67320190513243573455723083 100980285769865360183584625)
                  ·
                    refine ⟨75735214327399020137688469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100980285769865360183584625 75735214327399020137688469)
                    ·
                      refine ⟨3550088171596829068954147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75735214327399020137688469 3550088171596829068954147)
                      ·
                        rfl

theorem cell23_6913772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_6913772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913772 prefixEnd_6913772 := by exact prefixLift 6913772
  have htrace : WordTrace (prefixWord ++ tailWord_6913772) baseStart_6913772 baseEnd_6913772 := by
    simpa [prefixWord, tailWord_6913772, baseEnd_6913772] using wordTrace_append hprefix tailTrace_6913772
  have hstable : (prefixWord ++ tailWord_6913772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913772).length < 2 ^ (prefixWord ++ tailWord_6913772).sum := by decide
  have hdescent : baseEnd_6913772 < baseStart_6913772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913773 : List Nat := [1, 5, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_6913773 : Nat := 118140960795 + 6913773 * 2 ^ 59
def prefixEnd_6913773 : Nat := 4983230072969 + 3 ^ 40 * 6913773 * 2
def baseEnd_6913773 : Nat := 1183362895025827855013881

theorem tailTrace_6913773 : CollatzResearch.WordTrace tailWord_6913773 prefixEnd_6913773 1183362895025827855013881 := by
  unfold tailWord_6913773
  simp only [CollatzResearch.WordTrace]
  refine ⟨252166017581588674266937973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168110678387725782844625315 252166017581588674266937973)
  ·
    refine ⟨23640564148273938212525435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252166017581588674266937973 23640564148273938212525435)
    ·
      refine ⟨35460846222410907318788153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23640564148273938212525435 35460846222410907318788153)
      ·
        refine ⟨26595634666808180489091115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35460846222410907318788153 26595634666808180489091115)
        ·
          refine ⟨39893452000212270733636673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26595634666808180489091115 39893452000212270733636673)
          ·
            refine ⟨29920089000159203050227505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39893452000212270733636673 29920089000159203050227505)
            ·
              refine ⟨22440066750119402287670629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29920089000159203050227505 22440066750119402287670629)
              ·
                refine ⟨4207512515647387928938243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22440066750119402287670629 4207512515647387928938243)
                ·
                  refine ⟨6311268773471081893407365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207512515647387928938243 6311268773471081893407365)
                  ·
                    refine ⟨1183362895025827855013881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6311268773471081893407365 1183362895025827855013881)
                    ·
                      rfl

theorem cell23_6913773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_6913773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913773 prefixEnd_6913773 := by exact prefixLift 6913773
  have htrace : WordTrace (prefixWord ++ tailWord_6913773) baseStart_6913773 baseEnd_6913773 := by
    simpa [prefixWord, tailWord_6913773, baseEnd_6913773] using wordTrace_append hprefix tailTrace_6913773
  have hstable : (prefixWord ++ tailWord_6913773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913773).length < 2 ^ (prefixWord ++ tailWord_6913773).sum := by decide
  have hdescent : baseEnd_6913773 < baseStart_6913773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913780 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6913780 : Nat := 118140960795 + 6913780 * 2 ^ 59
def prefixEnd_6913780 : Nat := 4983230072969 + 3 ^ 40 * 6913780 * 2
def baseEnd_6913780 : Nat := 3550092279442065037654111

theorem tailTrace_6913780 : CollatzResearch.WordTrace tailWord_6913780 prefixEnd_6913780 3550092279442065037654111 := by
  unfold tailWord_6913780
  simp only [CollatzResearch.WordTrace]
  refine ⟨126083136446281657231221397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168110848595042209641628529 126083136446281657231221397)
  ·
    refine ⟨5910147020919452682713503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126083136446281657231221397 5910147020919452682713503)
    ·
      refine ⟨8865220531379179024070255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5910147020919452682713503 8865220531379179024070255)
      ·
        refine ⟨13297830797068768536105383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865220531379179024070255 13297830797068768536105383)
        ·
          refine ⟨19946746195603152804158075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13297830797068768536105383 19946746195603152804158075)
          ·
            refine ⟨29920119293404729206237113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19946746195603152804158075 29920119293404729206237113)
            ·
              refine ⟨22440089470053546904677835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29920119293404729206237113 22440089470053546904677835)
              ·
                refine ⟨33660134205080320357016753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22440089470053546904677835 33660134205080320357016753)
                ·
                  refine ⟨25245100653810240267762565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33660134205080320357016753 25245100653810240267762565)
                  ·
                    refine ⟨4733456372589420050205481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25245100653810240267762565 4733456372589420050205481)
                    ·
                      refine ⟨3550092279442065037654111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4733456372589420050205481 3550092279442065037654111)
                      ·
                        rfl

theorem cell23_6913780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6913780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913780 prefixEnd_6913780 := by exact prefixLift 6913780
  have htrace : WordTrace (prefixWord ++ tailWord_6913780) baseStart_6913780 baseEnd_6913780 := by
    simpa [prefixWord, tailWord_6913780, baseEnd_6913780] using wordTrace_append hprefix tailTrace_6913780
  have hstable : (prefixWord ++ tailWord_6913780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913780).length < 2 ^ (prefixWord ++ tailWord_6913780).sum := by decide
  have hdescent : baseEnd_6913780 < baseStart_6913780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913806 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2]
def baseStart_6913806 : Nat := 118140960795 + 6913806 * 2 ^ 59
def prefixEnd_6913806 : Nat := 4983230072969 + 3 ^ 40 * 6913806 * 2
def baseEnd_6913806 : Nat := 3550105629939081935928991

theorem tailTrace_6913806 : CollatzResearch.WordTrace tailWord_6913806 prefixEnd_6913806 3550105629939081935928991 := by
  unfold tailWord_6913806
  simp only [CollatzResearch.WordTrace]
  refine ⟨31520902648808640112861159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168111480793646080601926181 31520902648808640112861159)
  ·
    refine ⟨47281353973212960169291739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31520902648808640112861159 47281353973212960169291739)
    ·
      refine ⟨70922030959819440253937609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47281353973212960169291739 70922030959819440253937609)
      ·
        refine ⟨53191523219864580190453207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70922030959819440253937609 53191523219864580190453207)
        ·
          refine ⟨79787284829796870285679811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53191523219864580190453207 79787284829796870285679811)
          ·
            refine ⟨119680927244695305428519717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79787284829796870285679811 119680927244695305428519717)
            ·
              refine ⟨22440173858380369767847447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119680927244695305428519717 22440173858380369767847447)
              ·
                refine ⟨33660260787570554651771171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22440173858380369767847447 33660260787570554651771171)
                ·
                  refine ⟨50490391181355831977656757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33660260787570554651771171 50490391181355831977656757)
                  ·
                    refine ⟨4733474173252109247905321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50490391181355831977656757 4733474173252109247905321)
                    ·
                      refine ⟨3550105629939081935928991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4733474173252109247905321 3550105629939081935928991)
                      ·
                        rfl

theorem cell23_6913806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_6913806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913806 prefixEnd_6913806 := by exact prefixLift 6913806
  have htrace : WordTrace (prefixWord ++ tailWord_6913806) baseStart_6913806 baseEnd_6913806 := by
    simpa [prefixWord, tailWord_6913806, baseEnd_6913806] using wordTrace_append hprefix tailTrace_6913806
  have hstable : (prefixWord ++ tailWord_6913806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913806).length < 2 ^ (prefixWord ++ tailWord_6913806).sum := by decide
  have hdescent : baseEnd_6913806 < baseStart_6913806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913819 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 1, 8, 2]
def baseStart_6913819 : Nat := 118140960795 + 6913819 * 2 ^ 59
def prefixEnd_6913819 : Nat := 4983230072969 + 3 ^ 40 * 6913819 * 2
def baseEnd_6913819 : Nat := 3550112305187590385066431

theorem tailTrace_6913819 : CollatzResearch.WordTrace tailWord_6913819 prefixEnd_6913819 3550112305187590385066431 := by
  unfold tailWord_6913819
  simp only [CollatzResearch.WordTrace]
  refine ⟨252167695339422024123112511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168111796892948016082075007 252167695339422024123112511)
  ·
    refine ⟨378251543009133036184668767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252167695339422024123112511 378251543009133036184668767)
    ·
      refine ⟨567377314513699554277003151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378251543009133036184668767 567377314513699554277003151)
      ·
        refine ⟨851065971770549331415504727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567377314513699554277003151 851065971770549331415504727)
        ·
          refine ⟨1276598957655823997123257091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851065971770549331415504727 1276598957655823997123257091)
          ·
            refine ⟨1914898436483735995684885637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276598957655823997123257091 1914898436483735995684885637)
            ·
              refine ⟨359043456840700499190916057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1914898436483735995684885637 359043456840700499190916057)
              ·
                refine ⟨269282592630525374393187043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359043456840700499190916057 269282592630525374393187043)
                ·
                  refine ⟨403923888945788061589780565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269282592630525374393187043 403923888945788061589780565)
                  ·
                    refine ⟨4733483073583453846755241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 403923888945788061589780565 4733483073583453846755241)
                    ·
                      refine ⟨3550112305187590385066431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4733483073583453846755241 3550112305187590385066431)
                      ·
                        rfl

theorem cell23_6913819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 8, 2].length) (baseStart_6913819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913819 prefixEnd_6913819 := by exact prefixLift 6913819
  have htrace : WordTrace (prefixWord ++ tailWord_6913819) baseStart_6913819 baseEnd_6913819 := by
    simpa [prefixWord, tailWord_6913819, baseEnd_6913819] using wordTrace_append hprefix tailTrace_6913819
  have hstable : (prefixWord ++ tailWord_6913819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913819).length < 2 ^ (prefixWord ++ tailWord_6913819).sum := by decide
  have hdescent : baseEnd_6913819 < baseStart_6913819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913839 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 3]
def baseStart_6913839 : Nat := 118140960795 + 6913839 * 2 ^ 59
def prefixEnd_6913839 : Nat := 4983230072969 + 3 ^ 40 * 6913839 * 2
def baseEnd_6913839 : Nat := 3550122574800680306816339

theorem tailTrace_6913839 : CollatzResearch.WordTrace tailWord_6913839 prefixEnd_6913839 3550122574800680306816339 := by
  unfold tailWord_6913839
  simp only [CollatzResearch.WordTrace]
  refine ⟨252168424799349567538840571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168112283199566378359227047 252168424799349567538840571)
  ·
    refine ⟨378252637199024351308260857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252168424799349567538840571 378252637199024351308260857)
    ·
      refine ⟨283689477899268263481195643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378252637199024351308260857 283689477899268263481195643)
      ·
        refine ⟨425534216848902395221793465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283689477899268263481195643 425534216848902395221793465)
        ·
          refine ⟨319150662636676796416345099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425534216848902395221793465 319150662636676796416345099)
          ·
            refine ⟨478725993955015194624517649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319150662636676796416345099 478725993955015194624517649)
            ·
              refine ⟨359044495466261395968388237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478725993955015194624517649 359044495466261395968388237)
              ·
                refine ⟨134641685799848023488145589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359044495466261395968388237 134641685799848023488145589)
                ·
                  refine ⟨12622658043735752202013649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134641685799848023488145589 12622658043735752202013649)
                  ·
                    refine ⟨9466993532801814151510237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12622658043735752202013649 9466993532801814151510237)
                    ·
                      refine ⟨3550122574800680306816339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9466993532801814151510237 3550122574800680306816339)
                      ·
                        rfl

theorem cell23_6913839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 3].length) (baseStart_6913839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913839 prefixEnd_6913839 := by exact prefixLift 6913839
  have htrace : WordTrace (prefixWord ++ tailWord_6913839) baseStart_6913839 baseEnd_6913839 := by
    simpa [prefixWord, tailWord_6913839, baseEnd_6913839] using wordTrace_append hprefix tailTrace_6913839
  have hstable : (prefixWord ++ tailWord_6913839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913839).length < 2 ^ (prefixWord ++ tailWord_6913839).sum := by decide
  have hdescent : baseEnd_6913839 < baseStart_6913839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913853 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_6913853 : Nat := 118140960795 + 6913853 * 2 ^ 59
def prefixEnd_6913853 : Nat := 4983230072969 + 3 ^ 40 * 6913853 * 2
def baseEnd_6913853 : Nat := 3550129763529843252041275

theorem tailTrace_6913853 : CollatzResearch.WordTrace tailWord_6913853 prefixEnd_6913853 3550129763529843252041275 := by
  unfold tailWord_6913853
  simp only [CollatzResearch.WordTrace]
  refine ⟨252168935421298847929850213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168112623614199231953233475 252168935421298847929850213)
  ·
    refine ⟨47281675391493533986846915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252168935421298847929850213 47281675391493533986846915)
    ·
      refine ⟨70922513087240300980270373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47281675391493533986846915 70922513087240300980270373)
      ·
        refine ⟨13297971203857556433800695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70922513087240300980270373 13297971203857556433800695)
        ·
          refine ⟨19946956805786334650701043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13297971203857556433800695 19946956805786334650701043)
          ·
            refine ⟨29920435208679501976051565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19946956805786334650701043 29920435208679501976051565)
            ·
              refine ⟨11220163203254813241019337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29920435208679501976051565 11220163203254813241019337)
              ·
                refine ⟨8415122402441109930764503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11220163203254813241019337 8415122402441109930764503)
                ·
                  refine ⟨12622683603661664896146755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8415122402441109930764503 12622683603661664896146755)
                  ·
                    refine ⟨18934025405492497344220133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12622683603661664896146755 18934025405492497344220133)
                    ·
                      refine ⟨3550129763529843252041275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18934025405492497344220133 3550129763529843252041275)
                      ·
                        rfl

theorem cell23_6913853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_6913853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913853 prefixEnd_6913853 := by exact prefixLift 6913853
  have htrace : WordTrace (prefixWord ++ tailWord_6913853) baseStart_6913853 baseEnd_6913853 := by
    simpa [prefixWord, tailWord_6913853, baseEnd_6913853] using wordTrace_append hprefix tailTrace_6913853
  have hstable : (prefixWord ++ tailWord_6913853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913853).length < 2 ^ (prefixWord ++ tailWord_6913853).sum := by decide
  have hdescent : baseEnd_6913853 < baseStart_6913853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913887 : List Nat := [1, 1, 2, 3, 1, 4, 4, 2, 1, 2, 2]
def baseStart_6913887 : Nat := 118140960795 + 6913887 * 2 ^ 59
def prefixEnd_6913887 : Nat := 4983230072969 + 3 ^ 40 * 6913887 * 2
def baseEnd_6913887 : Nat := 3550147221872096119016119

theorem tailTrace_6913887 : CollatzResearch.WordTrace tailWord_6913887 prefixEnd_6913887 3550147221872096119016119 := by
  unfold tailWord_6913887
  simp only [CollatzResearch.WordTrace]
  refine ⟨252170175503175671736587915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168113450335450447824391943 252170175503175671736587915)
  ·
    refine ⟨378255263254763507604881873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252170175503175671736587915 378255263254763507604881873)
    ·
      refine ⟨283691447441072630703661405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378255263254763507604881873 283691447441072630703661405)
      ·
        refine ⟨106384292790402236513873027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283691447441072630703661405 106384292790402236513873027)
        ·
          refine ⟨159576439185603354770809541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106384292790402236513873027 159576439185603354770809541)
          ·
            refine ⟨29920582347300629019526789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159576439185603354770809541 29920582347300629019526789)
            ·
              refine ⟨5610109190118867941161273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29920582347300629019526789 5610109190118867941161273)
              ·
                refine ⟨4207581892589150955870955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5610109190118867941161273 4207581892589150955870955)
                ·
                  refine ⟨6311372838883726433806433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207581892589150955870955 6311372838883726433806433)
                  ·
                    refine ⟨4733529629162794825354825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6311372838883726433806433 4733529629162794825354825)
                    ·
                      refine ⟨3550147221872096119016119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4733529629162794825354825 3550147221872096119016119)
                      ·
                        rfl

theorem cell23_6913887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_6913887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913887 prefixEnd_6913887 := by exact prefixLift 6913887
  have htrace : WordTrace (prefixWord ++ tailWord_6913887) baseStart_6913887 baseEnd_6913887 := by
    simpa [prefixWord, tailWord_6913887, baseEnd_6913887] using wordTrace_append hprefix tailTrace_6913887
  have hstable : (prefixWord ++ tailWord_6913887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913887).length < 2 ^ (prefixWord ++ tailWord_6913887).sum := by decide
  have hdescent : baseEnd_6913887 < baseStart_6913887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913913 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 1, 3, 2]
def baseStart_6913913 : Nat := 118140960795 + 6913913 * 2 ^ 59
def prefixEnd_6913913 : Nat := 4983230072969 + 3 ^ 40 * 6913913 * 2
def baseEnd_6913913 : Nat := 3550160572369113017290999

theorem tailTrace_6913913 : CollatzResearch.WordTrace tailWord_6913913 prefixEnd_6913913 3550160572369113017290999 := by
  unfold tailWord_6913913
  simp only [CollatzResearch.WordTrace]
  refine ⟨252171123801081478177034393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168114082534054318784689595 252171123801081478177034393)
  ·
    refine ⟨189128342850811108632775795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252171123801081478177034393 189128342850811108632775795)
    ·
      refine ⟨283692514276216662949163693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189128342850811108632775795 283692514276216662949163693)
      ·
        refine ⟨106384692853581248605936385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283692514276216662949163693 106384692853581248605936385)
        ·
          refine ⟨79788519640185936454452289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106384692853581248605936385 79788519640185936454452289)
          ·
            refine ⟨59841389730139452340839217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79788519640185936454452289 59841389730139452340839217)
            ·
              refine ⟨44881042297604589255629413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59841389730139452340839217 44881042297604589255629413)
              ·
                refine ⟨8415195430800860485430515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44881042297604589255629413 8415195430800860485430515)
                ·
                  refine ⟨12622793146201290728145773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8415195430800860485430515 12622793146201290728145773)
                  ·
                    refine ⟨4733547429825484023054665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12622793146201290728145773 4733547429825484023054665)
                    ·
                      refine ⟨3550160572369113017290999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4733547429825484023054665 3550160572369113017290999)
                      ·
                        rfl

theorem cell23_6913913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_6913913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913913 prefixEnd_6913913 := by exact prefixLift 6913913
  have htrace : WordTrace (prefixWord ++ tailWord_6913913) baseStart_6913913 baseEnd_6913913 := by
    simpa [prefixWord, tailWord_6913913, baseEnd_6913913] using wordTrace_append hprefix tailTrace_6913913
  have hstable : (prefixWord ++ tailWord_6913913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913913).length < 2 ^ (prefixWord ++ tailWord_6913913).sum := by decide
  have hdescent : baseEnd_6913913 < baseStart_6913913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913929 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_6913929 : Nat := 118140960795 + 6913929 * 2 ^ 59
def prefixEnd_6913929 : Nat := 4983230072969 + 3 ^ 40 * 6913929 * 2
def baseEnd_6913929 : Nat := 3550168788059584954690925

theorem tailTrace_6913929 : CollatzResearch.WordTrace tailWord_6913929 prefixEnd_6913929 3550168788059584954690925 := by
  unfold tailWord_6913929
  simp only [CollatzResearch.WordTrace]
  refine ⟨252171707369023512909616841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168114471579349008606411227 252171707369023512909616841)
  ·
    refine ⟨189128780526767634682212631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252171707369023512909616841 189128780526767634682212631)
    ·
      refine ⟨283693170790151452023318947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189128780526767634682212631 283693170790151452023318947)
      ·
        refine ⟨425539756185227178034978421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283693170790151452023318947 425539756185227178034978421)
        ·
          refine ⟨39894352142365047940779227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 425539756185227178034978421 39894352142365047940779227)
          ·
            refine ⟨59841528213547571911168841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39894352142365047940779227 59841528213547571911168841)
            ·
              refine ⟨44881146160160678933376631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59841528213547571911168841 44881146160160678933376631)
              ·
                refine ⟨67321719240241018400064947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44881146160160678933376631 67321719240241018400064947)
                ·
                  refine ⟨100982578860361527600097421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67321719240241018400064947 100982578860361527600097421)
                  ·
                    refine ⟨37868467072635572850036533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100982578860361527600097421 37868467072635572850036533)
                    ·
                      refine ⟨3550168788059584954690925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37868467072635572850036533 3550168788059584954690925)
                      ·
                        rfl

theorem cell23_6913929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_6913929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913929 prefixEnd_6913929 := by exact prefixLift 6913929
  have htrace : WordTrace (prefixWord ++ tailWord_6913929) baseStart_6913929 baseEnd_6913929 := by
    simpa [prefixWord, tailWord_6913929, baseEnd_6913929] using wordTrace_append hprefix tailTrace_6913929
  have hstable : (prefixWord ++ tailWord_6913929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913929).length < 2 ^ (prefixWord ++ tailWord_6913929).sum := by decide
  have hdescent : baseEnd_6913929 < baseStart_6913929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913956 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_6913956 : Nat := 118140960795 + 6913956 * 2 ^ 59
def prefixEnd_6913956 : Nat := 4983230072969 + 3 ^ 40 * 6913956 * 2
def baseEnd_6913956 : Nat := 3550182652037256349053301

theorem tailTrace_6913956 : CollatzResearch.WordTrace tailWord_6913956 prefixEnd_6913956 3550182652037256349053301 := by
  unfold tailWord_6913956
  simp only [CollatzResearch.WordTrace]
  refine ⟨126086346069962848260424861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168115128093283797680566481 126086346069962848260424861)
  ·
    refine ⟨47282379776236068097659323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126086346069962848260424861 47282379776236068097659323)
    ·
      refine ⟨70923569664354102146488985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47282379776236068097659323 70923569664354102146488985)
      ·
        refine ⟨53192677248265576609866739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70923569664354102146488985 53192677248265576609866739)
        ·
          refine ⟨79789015872398364914800109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53192677248265576609866739 79789015872398364914800109)
          ·
            refine ⟨29920880952149386843050041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79789015872398364914800109 29920880952149386843050041)
            ·
              refine ⟨22440660714112040132287531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29920880952149386843050041 22440660714112040132287531)
              ·
                refine ⟨33660991071168060198431297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22440660714112040132287531 33660991071168060198431297)
                ·
                  refine ⟨25245743303376045148823473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33660991071168060198431297 25245743303376045148823473)
                  ·
                    refine ⟨18934307477532033861617605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25245743303376045148823473 18934307477532033861617605)
                    ·
                      refine ⟨3550182652037256349053301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18934307477532033861617605 3550182652037256349053301)
                      ·
                        rfl

theorem cell23_6913956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_6913956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913956 prefixEnd_6913956 := by exact prefixLift 6913956
  have htrace : WordTrace (prefixWord ++ tailWord_6913956) baseStart_6913956 baseEnd_6913956 := by
    simpa [prefixWord, tailWord_6913956, baseEnd_6913956] using wordTrace_append hprefix tailTrace_6913956
  have hstable : (prefixWord ++ tailWord_6913956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913956).length < 2 ^ (prefixWord ++ tailWord_6913956).sum := by decide
  have hdescent : baseEnd_6913956 < baseStart_6913956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913996 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_6913996 : Nat := 118140960795 + 6913996 * 2 ^ 59
def prefixEnd_6913996 : Nat := 4983230072969 + 3 ^ 40 * 6913996 * 2
def baseEnd_6913996 : Nat := 1183401063754478730851039

theorem tailTrace_6913996 : CollatzResearch.WordTrace tailWord_6913996 prefixEnd_6913996 1183401063754478730851039 := by
  unfold tailWord_6913996
  simp only [CollatzResearch.WordTrace]
  refine ⟨126087075529890391676152921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168116100706520522234870561 126087075529890391676152921)
  ·
    refine ⟨94565306647417793757114691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126087075529890391676152921 94565306647417793757114691)
    ·
      refine ⟨141847959971126690635672037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94565306647417793757114691 141847959971126690635672037)
      ·
        refine ⟨26596492494586254494188507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141847959971126690635672037 26596492494586254494188507)
        ·
          refine ⟨39894738741879381741282761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26596492494586254494188507 39894738741879381741282761)
          ·
            refine ⟨29921054056409536305962071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39894738741879381741282761 29921054056409536305962071)
            ·
              refine ⟨44881581084614304458943107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29921054056409536305962071 44881581084614304458943107)
              ·
                refine ⟨67322371626921456688414661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44881581084614304458943107 67322371626921456688414661)
                ·
                  refine ⟨12622944680047773129077749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67322371626921456688414661 12622944680047773129077749)
                  ·
                    refine ⟨1183401063754478730851039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12622944680047773129077749 1183401063754478730851039)
                    ·
                      rfl

theorem cell23_6913996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_6913996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913996 prefixEnd_6913996 := by exact prefixLift 6913996
  have htrace : WordTrace (prefixWord ++ tailWord_6913996) baseStart_6913996 baseEnd_6913996 := by
    simpa [prefixWord, tailWord_6913996, baseEnd_6913996] using wordTrace_append hprefix tailTrace_6913996
  have hstable : (prefixWord ++ tailWord_6913996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913996).length < 2 ^ (prefixWord ++ tailWord_6913996).sum := by decide
  have hdescent : baseEnd_6913996 < baseStart_6913996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914053 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 2, 2, 3]
def baseStart_6914053 : Nat := 118140960795 + 6914053 * 2 ^ 59
def prefixEnd_6914053 : Nat := 4983230072969 + 3 ^ 40 * 6914053 * 2
def baseEnd_6914053 : Nat := 3550232459660742469540355

theorem tailTrace_6914053 : CollatzResearch.WordTrace tailWord_6914053 prefixEnd_6914053 3550232459660742469540355 := by
  unfold tailWord_6914053
  simp only [CollatzResearch.WordTrace]
  refine ⟨252176230020574282087130813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168117486680382854724753875 252176230020574282087130813)
  ·
    refine ⟨94566086257715355782674055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252176230020574282087130813 94566086257715355782674055)
    ·
      refine ⟨141849129386573033674011083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94566086257715355782674055 141849129386573033674011083)
      ·
        refine ⟨212773694079859550511016625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141849129386573033674011083 212773694079859550511016625)
        ·
          refine ⟨159580270559894662883262469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212773694079859550511016625 159580270559894662883262469)
          ·
            refine ⟨29921300729980249290611713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159580270559894662883262469 29921300729980249290611713)
            ·
              refine ⟨22440975547485186967958785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29921300729980249290611713 22440975547485186967958785)
              ·
                refine ⟨16830731660613890225969089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22440975547485186967958785 16830731660613890225969089)
                ·
                  refine ⟨12623048745460417669476817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16830731660613890225969089 12623048745460417669476817)
                  ·
                    refine ⟨9467286559095313252107613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12623048745460417669476817 9467286559095313252107613)
                    ·
                      refine ⟨3550232459660742469540355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9467286559095313252107613 3550232459660742469540355)
                      ·
                        rfl

theorem cell23_6914053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_6914053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914053 prefixEnd_6914053 := by exact prefixLift 6914053
  have htrace : WordTrace (prefixWord ++ tailWord_6914053) baseStart_6914053 baseEnd_6914053 := by
    simpa [prefixWord, tailWord_6914053, baseEnd_6914053] using wordTrace_append hprefix tailTrace_6914053
  have hstable : (prefixWord ++ tailWord_6914053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914053).length < 2 ^ (prefixWord ++ tailWord_6914053).sum := by decide
  have hdescent : baseEnd_6914053 < baseStart_6914053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914060 : List Nat := [2, 2, 1, 2, 3, 1, 3, 4, 1, 4]
def baseStart_6914060 : Nat := 118140960795 + 6914060 * 2 ^ 59
def prefixEnd_6914060 : Nat := 4983230072969 + 3 ^ 40 * 6914060 * 2
def baseEnd_6914060 : Nat := 1183412018008441314050941

theorem tailTrace_6914060 : CollatzResearch.WordTrace tailWord_6914060 prefixEnd_6914060 1183412018008441314050941 := by
  unfold tailWord_6914060
  simp only [CollatzResearch.WordTrace]
  refine ⟨126088242665774461141317817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168117656887699281521757089 126088242665774461141317817)
  ·
    refine ⟨94566181999330845855988363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126088242665774461141317817 94566181999330845855988363)
    ·
      refine ⟨141849272998996268783982545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94566181999330845855988363 141849272998996268783982545)
      ·
        refine ⟨106386954749247201587986909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141849272998996268783982545 106386954749247201587986909)
        ·
          refine ⟨39895108030967700595495091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106386954749247201587986909 39895108030967700595495091)
          ·
            refine ⟨59842662046451550893242637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39895108030967700595495091 59842662046451550893242637)
            ·
              refine ⟨22440998267419331584965989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59842662046451550893242637 22440998267419331584965989)
              ·
                refine ⟨4207687175141124672181123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22440998267419331584965989 4207687175141124672181123)
                ·
                  refine ⟨6311530762711687008271685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207687175141124672181123 6311530762711687008271685)
                  ·
                    refine ⟨1183412018008441314050941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6311530762711687008271685 1183412018008441314050941)
                    ·
                      rfl

theorem cell23_6914060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_6914060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914060 prefixEnd_6914060 := by exact prefixLift 6914060
  have htrace : WordTrace (prefixWord ++ tailWord_6914060) baseStart_6914060 baseEnd_6914060 := by
    simpa [prefixWord, tailWord_6914060, baseEnd_6914060] using wordTrace_append hprefix tailTrace_6914060
  have hstable : (prefixWord ++ tailWord_6914060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914060).length < 2 ^ (prefixWord ++ tailWord_6914060).sum := by decide
  have hdescent : baseEnd_6914060 < baseStart_6914060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914133 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 1, 6]
def baseStart_6914133 : Nat := 118140960795 + 6914133 * 2 ^ 59
def prefixEnd_6914133 : Nat := 4983230072969 + 3 ^ 40 * 6914133 * 2
def baseEnd_6914133 : Nat := 1183424512704367385513329

theorem tailTrace_6914133 : CollatzResearch.WordTrace tailWord_6914133 prefixEnd_6914133 1183424512704367385513329 := by
  unfold tailWord_6914133
  simp only [CollatzResearch.WordTrace]
  refine ⟨252179147860284455750043053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168119431906856303833362035 252179147860284455750043053)
  ·
    refine ⟨94567180447606670906266145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252179147860284455750043053 94567180447606670906266145)
    ·
      refine ⟨70925385335705003179699609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94567180447606670906266145 70925385335705003179699609)
      ·
        refine ⟨53194039001778752384774707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70925385335705003179699609 53194039001778752384774707)
        ·
          refine ⟨79791058502668128577162061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53194039001778752384774707 79791058502668128577162061)
          ·
            refine ⟨29921646938500548216435773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79791058502668128577162061 29921646938500548216435773)
            ·
              refine ⟨11220617601937705581163415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29921646938500548216435773 11220617601937705581163415)
              ·
                refine ⟨16830926402906558371745123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11220617601937705581163415 16830926402906558371745123)
                ·
                  refine ⟨25246389604359837557617685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16830926402906558371745123 25246389604359837557617685)
                  ·
                    refine ⟨1183424512704367385513329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25246389604359837557617685 1183424512704367385513329)
                    ·
                      rfl

theorem cell23_6914133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_6914133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914133 prefixEnd_6914133 := by exact prefixLift 6914133
  have htrace : WordTrace (prefixWord ++ tailWord_6914133) baseStart_6914133 baseEnd_6914133 := by
    simpa [prefixWord, tailWord_6914133, baseEnd_6914133] using wordTrace_append hprefix tailTrace_6914133
  have hstable : (prefixWord ++ tailWord_6914133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914133).length < 2 ^ (prefixWord ++ tailWord_6914133).sum := by decide
  have hdescent : baseEnd_6914133 < baseStart_6914133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914134 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_6914134 : Nat := 118140960795 + 6914134 * 2 ^ 59
def prefixEnd_6914134 : Nat := 4983230072969 + 3 ^ 40 * 6914134 * 2
def baseEnd_6914134 : Nat := 3550274051593756652627483

theorem tailTrace_6914134 : CollatzResearch.WordTrace tailWord_6914134 prefixEnd_6914134 3550274051593756652627483 := by
  unfold tailWord_6914134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15761199020830052057551841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168119456222187221947219637 15761199020830052057551841)
  ·
    refine ⟨11820899265622539043163881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15761199020830052057551841 11820899265622539043163881)
    ·
      refine ⟨8865674449216904282372911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11820899265622539043163881 8865674449216904282372911)
      ·
        refine ⟨13298511673825356423559367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865674449216904282372911 13298511673825356423559367)
        ·
          refine ⟨19947767510738034635339051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13298511673825356423559367 19947767510738034635339051)
          ·
            refine ⟨29921651266107051953008577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19947767510738034635339051 29921651266107051953008577)
            ·
              refine ⟨22441238449580288964756433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29921651266107051953008577 22441238449580288964756433)
              ·
                refine ⟨16830928837185216723567325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22441238449580288964756433 16830928837185216723567325)
                ·
                  refine ⟨6311598313944456271337747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16830928837185216723567325 6311598313944456271337747)
                  ·
                    refine ⟨9467397470916684407006621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6311598313944456271337747 9467397470916684407006621)
                    ·
                      refine ⟨3550274051593756652627483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9467397470916684407006621 3550274051593756652627483)
                      ·
                        rfl

theorem cell23_6914134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_6914134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914134 prefixEnd_6914134 := by exact prefixLift 6914134
  have htrace : WordTrace (prefixWord ++ tailWord_6914134) baseStart_6914134 baseEnd_6914134 := by
    simpa [prefixWord, tailWord_6914134, baseEnd_6914134] using wordTrace_append hprefix tailTrace_6914134
  have hstable : (prefixWord ++ tailWord_6914134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914134).length < 2 ^ (prefixWord ++ tailWord_6914134).sum := by decide
  have hdescent : baseEnd_6914134 < baseStart_6914134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914140 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_6914140 : Nat := 118140960795 + 6914140 * 2 ^ 59
def prefixEnd_6914140 : Nat := 4983230072969 + 3 ^ 40 * 6914140 * 2
def baseEnd_6914140 : Nat := 3550277132477683629152455

theorem tailTrace_6914140 : CollatzResearch.WordTrace tailWord_6914140 prefixEnd_6914140 3550277132477683629152455 := by
  unfold tailWord_6914140
  simp only [CollatzResearch.WordTrace]
  refine ⟨126089701585629547972773937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168119602114172730630365249 126089701585629547972773937)
  ·
    refine ⟨94567276189222160979580453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126089701585629547972773937 94567276189222160979580453)
    ·
      refine ⟨17731364285479155183671335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94567276189222160979580453 17731364285479155183671335)
      ·
        refine ⟨26597046428218732775507003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17731364285479155183671335 26597046428218732775507003)
        ·
          refine ⟨39895569642328099163260505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26597046428218732775507003 39895569642328099163260505)
          ·
            refine ⟨29921677231746074372445379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39895569642328099163260505 29921677231746074372445379)
            ·
              refine ⟨44882515847619111558668069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29921677231746074372445379 44882515847619111558668069)
              ·
                refine ⟨8415471721428583417250263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44882515847619111558668069 8415471721428583417250263)
                ·
                  refine ⟨12623207582142875125875395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8415471721428583417250263 12623207582142875125875395)
                  ·
                    refine ⟨18934811373214312688813093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12623207582142875125875395 18934811373214312688813093)
                    ·
                      refine ⟨3550277132477683629152455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18934811373214312688813093 3550277132477683629152455)
                      ·
                        rfl

theorem cell23_6914140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_6914140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914140 prefixEnd_6914140 := by exact prefixLift 6914140
  have htrace : WordTrace (prefixWord ++ tailWord_6914140) baseStart_6914140 baseEnd_6914140 := by
    simpa [prefixWord, tailWord_6914140, baseEnd_6914140] using wordTrace_append hprefix tailTrace_6914140
  have hstable : (prefixWord ++ tailWord_6914140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914140).length < 2 ^ (prefixWord ++ tailWord_6914140).sum := by decide
  have hdescent : baseEnd_6914140 < baseStart_6914140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914160 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 3]
def baseStart_6914160 : Nat := 118140960795 + 6914160 * 2 ^ 59
def prefixEnd_6914160 : Nat := 4983230072969 + 3 ^ 40 * 6914160 * 2
def baseEnd_6914160 : Nat := 3550287402090773550902363

theorem tailTrace_6914160 : CollatzResearch.WordTrace tailWord_6914160 prefixEnd_6914160 3550287402090773550902363 := by
  unfold tailWord_6914160
  simp only [CollatzResearch.WordTrace]
  refine ⟨126090066315593319680637967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168120088420791092907517289 126090066315593319680637967)
  ·
    refine ⟨189135099473389979520956951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126090066315593319680637967 189135099473389979520956951)
    ·
      refine ⟨283702649210084969281435427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189135099473389979520956951 283702649210084969281435427)
      ·
        refine ⟨425553973815127453922153141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283702649210084969281435427 425553973815127453922153141)
        ·
          refine ⟨39895685045168198805201857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 425553973815127453922153141 39895685045168198805201857)
          ·
            refine ⟨29921763783876149103901393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39895685045168198805201857 29921763783876149103901393)
            ·
              refine ⟨22441322837907111827926045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29921763783876149103901393 22441322837907111827926045)
              ·
                refine ⟨8415496064215166935472267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22441322837907111827926045 8415496064215166935472267)
                ·
                  refine ⟨12623244096322750403208401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8415496064215166935472267 12623244096322750403208401)
                  ·
                    refine ⟨9467433072242062802406301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12623244096322750403208401 9467433072242062802406301)
                    ·
                      refine ⟨3550287402090773550902363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9467433072242062802406301 3550287402090773550902363)
                      ·
                        rfl

theorem cell23_6914160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 3].length) (baseStart_6914160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914160 prefixEnd_6914160 := by exact prefixLift 6914160
  have htrace : WordTrace (prefixWord ++ tailWord_6914160) baseStart_6914160 baseEnd_6914160 := by
    simpa [prefixWord, tailWord_6914160, baseEnd_6914160] using wordTrace_append hprefix tailTrace_6914160
  have hstable : (prefixWord ++ tailWord_6914160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914160).length < 2 ^ (prefixWord ++ tailWord_6914160).sum := by decide
  have hdescent : baseEnd_6914160 < baseStart_6914160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914176 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 2, 7]
def baseStart_6914176 : Nat := 118140960795 + 6914176 * 2 ^ 59
def prefixEnd_6914176 : Nat := 4983230072969 + 3 ^ 40 * 6914176 * 2
def baseEnd_6914176 : Nat := 1183431872593748496100763

theorem tailTrace_6914176 : CollatzResearch.WordTrace tailWord_6914176 prefixEnd_6914176 1183431872593748496100763 := by
  unfold tailWord_6914176
  simp only [CollatzResearch.WordTrace]
  refine ⟨126090358099564337046929191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168120477466085782729238921 126090358099564337046929191)
  ·
    refine ⟨189135537149346505570393787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126090358099564337046929191 189135537149346505570393787)
    ·
      refine ⟨283703305724019758355590681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189135537149346505570393787 283703305724019758355590681)
      ·
        refine ⟨212777479293014818766693011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283703305724019758355590681 212777479293014818766693011)
        ·
          refine ⟨319166218939522228150039517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212777479293014818766693011 319166218939522228150039517)
          ·
            refine ⟨119687332102320835556264819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319166218939522228150039517 119687332102320835556264819)
            ·
              refine ⟨179530998153481253334397229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119687332102320835556264819 179530998153481253334397229)
              ·
                refine ⟨67324124307555470000398961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179530998153481253334397229 67324124307555470000398961)
                ·
                  refine ⟨50493093230666602500299221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67324124307555470000398961 50493093230666602500299221)
                  ·
                    refine ⟨1183431872593748496100763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50493093230666602500299221 1183431872593748496100763)
                    ·
                      rfl

theorem cell23_6914176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_6914176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914176 prefixEnd_6914176 := by exact prefixLift 6914176
  have htrace : WordTrace (prefixWord ++ tailWord_6914176) baseStart_6914176 baseEnd_6914176 := by
    simpa [prefixWord, tailWord_6914176, baseEnd_6914176] using wordTrace_append hprefix tailTrace_6914176
  have hstable : (prefixWord ++ tailWord_6914176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914176).length < 2 ^ (prefixWord ++ tailWord_6914176).sum := by decide
  have hdescent : baseEnd_6914176 < baseStart_6914176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914184 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 2, 4]
def baseStart_6914184 : Nat := 118140960795 + 6914184 * 2 ^ 59
def prefixEnd_6914184 : Nat := 4983230072969 + 3 ^ 40 * 6914184 * 2
def baseEnd_6914184 : Nat := 1183433241875493819000751

theorem tailTrace_6914184 : CollatzResearch.WordTrace tailWord_6914184 prefixEnd_6914184 1183433241875493819000751 := by
  unfold tailWord_6914184
  simp only [CollatzResearch.WordTrace]
  refine ⟨126090503991549845730074803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168120671988733127640099737 126090503991549845730074803)
  ·
    refine ⟨189135755987324768595112205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126090503991549845730074803 189135755987324768595112205)
    ·
      refine ⟨70925908495246788223167077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189135755987324768595112205 70925908495246788223167077)
      ·
        refine ⟨13298607842858772791843827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70925908495246788223167077 13298607842858772791843827)
        ·
          refine ⟨19947911764288159187765741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13298607842858772791843827 19947911764288159187765741)
          ·
            refine ⟨7480466911608059695412153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19947911764288159187765741 7480466911608059695412153)
            ·
              refine ⟨5610350183706044771559115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7480466911608059695412153 5610350183706044771559115)
              ·
                refine ⟨8415525275559067157338673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610350183706044771559115 8415525275559067157338673)
                ·
                  refine ⟨6311643956669300368004005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8415525275559067157338673 6311643956669300368004005)
                  ·
                    refine ⟨1183433241875493819000751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6311643956669300368004005 1183433241875493819000751)
                    ·
                      rfl

theorem cell23_6914184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_6914184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914184 prefixEnd_6914184 := by exact prefixLift 6914184
  have htrace : WordTrace (prefixWord ++ tailWord_6914184) baseStart_6914184 baseEnd_6914184 := by
    simpa [prefixWord, tailWord_6914184, baseEnd_6914184] using wordTrace_append hprefix tailTrace_6914184
  have hstable : (prefixWord ++ tailWord_6914184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914184).length < 2 ^ (prefixWord ++ tailWord_6914184).sum := by decide
  have hdescent : baseEnd_6914184 < baseStart_6914184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914225 : List Nat := [1, 2, 2, 5, 3, 1, 2, 2, 1, 2, 2]
def baseStart_6914225 : Nat := 118140960795 + 6914225 * 2 ^ 59
def prefixEnd_6914225 : Nat := 4983230072969 + 3 ^ 40 * 6914225 * 2
def baseEnd_6914225 : Nat := 3550320778333315796589565

theorem tailTrace_6914225 : CollatzResearch.WordTrace tailWord_6914225 prefixEnd_6914225 3550320778333315796589565 := by
  unfold tailWord_6914225
  simp only [CollatzResearch.WordTrace]
  refine ⟨252182503375951155462392129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168121668917300770308261419 252182503375951155462392129)
  ·
    refine ⟨189136877531963366596794097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252182503375951155462392129 189136877531963366596794097)
    ·
      refine ⟨141852658148972524947595573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189136877531963366596794097 141852658148972524947595573)
      ·
        refine ⟨13298686701466174213837085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141852658148972524947595573 13298686701466174213837085)
        ·
          refine ⟨4987007513049815330188907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13298686701466174213837085 4987007513049815330188907)
          ·
            refine ⟨7480511269574722995283361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987007513049815330188907 7480511269574722995283361)
            ·
              refine ⟨5610383452181042246462521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7480511269574722995283361 5610383452181042246462521)
              ·
                refine ⟨4207787589135781684846891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5610383452181042246462521 4207787589135781684846891)
                ·
                  refine ⟨6311681383703672527270337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207787589135781684846891 6311681383703672527270337)
                  ·
                    refine ⟨4733761037777754395452753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6311681383703672527270337 4733761037777754395452753)
                    ·
                      refine ⟨3550320778333315796589565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4733761037777754395452753 3550320778333315796589565)
                      ·
                        rfl

theorem cell23_6914225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_6914225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914225 prefixEnd_6914225 := by exact prefixLift 6914225
  have htrace : WordTrace (prefixWord ++ tailWord_6914225) baseStart_6914225 baseEnd_6914225 := by
    simpa [prefixWord, tailWord_6914225, baseEnd_6914225] using wordTrace_append hprefix tailTrace_6914225
  have hstable : (prefixWord ++ tailWord_6914225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914225).length < 2 ^ (prefixWord ++ tailWord_6914225).sum := by decide
  have hdescent : baseEnd_6914225 < baseStart_6914225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914233 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 1, 6, 3]
def baseStart_6914233 : Nat := 118140960795 + 6914233 * 2 ^ 59
def prefixEnd_6914233 : Nat := 4983230072969 + 3 ^ 40 * 6914233 * 2
def baseEnd_6914233 : Nat := 3550324886178551765289527

theorem tailTrace_6914233 : CollatzResearch.WordTrace tailWord_6914233 prefixEnd_6914233 3550324886178551765289527 := by
  unfold tailWord_6914233
  simp only [CollatzResearch.WordTrace]
  refine ⟨252182795159922172828683353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168121863439948115219122235 252182795159922172828683353)
  ·
    refine ⟨189137096369941629621512515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252182795159922172828683353 189137096369941629621512515)
    ·
      refine ⟨283705644554912444432268773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189137096369941629621512515 283705644554912444432268773)
      ·
        refine ⟨53194808354046083331050395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283705644554912444432268773 53194808354046083331050395)
        ·
          refine ⟨79792212531069124996575593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53194808354046083331050395 79792212531069124996575593)
          ·
            refine ⟨59844159398301843747431695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79792212531069124996575593 59844159398301843747431695)
            ·
              refine ⟨89766239097452765621147543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59844159398301843747431695 89766239097452765621147543)
              ·
                refine ⟨134649358646179148431721315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89766239097452765621147543 134649358646179148431721315)
                ·
                  refine ⟨201974037969268722647581973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134649358646179148431721315 201974037969268722647581973)
                  ·
                    refine ⟨9467533029809471374105405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 201974037969268722647581973 9467533029809471374105405)
                    ·
                      refine ⟨3550324886178551765289527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9467533029809471374105405 3550324886178551765289527)
                      ·
                        rfl

theorem cell23_6914233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_6914233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914233 prefixEnd_6914233 := by exact prefixLift 6914233
  have htrace : WordTrace (prefixWord ++ tailWord_6914233) baseStart_6914233 baseEnd_6914233 := by
    simpa [prefixWord, tailWord_6914233, baseEnd_6914233] using wordTrace_append hprefix tailTrace_6914233
  have hstable : (prefixWord ++ tailWord_6914233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914233).length < 2 ^ (prefixWord ++ tailWord_6914233).sum := by decide
  have hdescent : baseEnd_6914233 < baseStart_6914233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914263 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 3]
def baseStart_6914263 : Nat := 118140960795 + 6914263 * 2 ^ 59
def prefixEnd_6914263 : Nat := 4983230072969 + 3 ^ 40 * 6914263 * 2
def baseEnd_6914263 : Nat := 3550340290598186647914389

theorem tailTrace_6914263 : CollatzResearch.WordTrace tailWord_6914263 prefixEnd_6914263 3550340290598186647914389 := by
  unfold tailWord_6914263
  simp only [CollatzResearch.WordTrace]
  refine ⟨252183889349813487952275443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168122592899875658634850295 252183889349813487952275443)
  ·
    refine ⟨378275834024720231928413165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252183889349813487952275443 378275834024720231928413165)
    ·
      refine ⟨141853437759270086973154937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378275834024720231928413165 141853437759270086973154937)
      ·
        refine ⟨106390078319452565229866203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141853437759270086973154937 106390078319452565229866203)
        ·
          refine ⟨159585117479178847844799305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106390078319452565229866203 159585117479178847844799305)
          ·
            refine ⟨119688838109384135883599479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159585117479178847844799305 119688838109384135883599479)
            ·
              refine ⟨179533257164076203825399219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119688838109384135883599479 179533257164076203825399219)
              ·
                refine ⟨269299885746114305738098829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179533257164076203825399219 269299885746114305738098829)
                ·
                  refine ⟨100987457154792864651787061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269299885746114305738098829 100987457154792864651787061)
                  ·
                    refine ⟨9467574108261831061105037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100987457154792864651787061 9467574108261831061105037)
                    ·
                      refine ⟨3550340290598186647914389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9467574108261831061105037 3550340290598186647914389)
                      ·
                        rfl

theorem cell23_6914263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_6914263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914263 prefixEnd_6914263 := by exact prefixLift 6914263
  have htrace : WordTrace (prefixWord ++ tailWord_6914263) baseStart_6914263 baseEnd_6914263 := by
    simpa [prefixWord, tailWord_6914263, baseEnd_6914263] using wordTrace_append hprefix tailTrace_6914263
  have hstable : (prefixWord ++ tailWord_6914263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914263).length < 2 ^ (prefixWord ++ tailWord_6914263).sum := by decide
  have hdescent : baseEnd_6914263 < baseStart_6914263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914280 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_6914280 : Nat := 118140960795 + 6914280 * 2 ^ 59
def prefixEnd_6914280 : Nat := 4983230072969 + 3 ^ 40 * 6914280 * 2
def baseEnd_6914280 : Nat := 3550349019769313081401811

theorem tailTrace_6914280 : CollatzResearch.WordTrace tailWord_6914280 prefixEnd_6914280 3550349019769313081401811 := by
  unfold tailWord_6914280
  simp only [CollatzResearch.WordTrace]
  refine ⟨126092254695375949927822147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168123006260501266570429529 126092254695375949927822147)
  ·
    refine ⟨189138382043063924891733221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126092254695375949927822147 189138382043063924891733221)
    ·
      refine ⟨35463446633074485917199979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189138382043063924891733221 35463446633074485917199979)
      ·
        refine ⟨53195169949611728875799969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35463446633074485917199979 53195169949611728875799969)
        ·
          refine ⟨39896377462208796656849977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53195169949611728875799969 39896377462208796656849977)
          ·
            refine ⟨29922283096656597492637483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39896377462208796656849977 29922283096656597492637483)
            ·
              refine ⟨44883424644984896238956225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29922283096656597492637483 44883424644984896238956225)
              ·
                refine ⟨33662568483738672179217169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44883424644984896238956225 33662568483738672179217169)
                ·
                  refine ⟨25246926362804004134412877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33662568483738672179217169 25246926362804004134412877)
                  ·
                    refine ⟨9467597386051501550404829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25246926362804004134412877 9467597386051501550404829)
                    ·
                      refine ⟨3550349019769313081401811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9467597386051501550404829 3550349019769313081401811)
                      ·
                        rfl

theorem cell23_6914280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_6914280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914280 prefixEnd_6914280 := by exact prefixLift 6914280
  have htrace : WordTrace (prefixWord ++ tailWord_6914280) baseStart_6914280 baseEnd_6914280 := by
    simpa [prefixWord, tailWord_6914280, baseEnd_6914280] using wordTrace_append hprefix tailTrace_6914280
  have hstable : (prefixWord ++ tailWord_6914280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914280).length < 2 ^ (prefixWord ++ tailWord_6914280).sum := by decide
  have hdescent : baseEnd_6914280 < baseStart_6914280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914283 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 4, 5]
def baseStart_6914283 : Nat := 118140960795 + 6914283 * 2 ^ 59
def prefixEnd_6914283 : Nat := 4983230072969 + 3 ^ 40 * 6914283 * 2
def baseEnd_6914283 : Nat := 1183450186737092189888099

theorem tailTrace_6914283 : CollatzResearch.WordTrace tailWord_6914283 prefixEnd_6914283 1183450186737092189888099 := by
  unfold tailWord_6914283
  simp only [CollatzResearch.WordTrace]
  refine ⟨252184618809741031368003503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168123079206494020912002335 252184618809741031368003503)
  ·
    refine ⟨378276928214611547052005255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252184618809741031368003503 378276928214611547052005255)
    ·
      refine ⟨567415392321917320578007883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378276928214611547052005255 567415392321917320578007883)
      ·
        refine ⟨851123088482875980867011825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567415392321917320578007883 851123088482875980867011825)
        ·
          refine ⟨638342316362156985650258869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851123088482875980867011825 638342316362156985650258869)
          ·
            refine ⟨59844592158952217404711769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 638342316362156985650258869 59844592158952217404711769)
            ·
              refine ⟨44883444119214163053533827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59844592158952217404711769 44883444119214163053533827)
              ·
                refine ⟨67325166178821244580300741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44883444119214163053533827 67325166178821244580300741)
                ·
                  refine ⟨12623468658528983358806389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67325166178821244580300741 12623468658528983358806389)
                  ·
                    refine ⟨1183450186737092189888099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12623468658528983358806389 1183450186737092189888099)
                    ·
                      rfl

theorem cell23_6914283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 5].length) (baseStart_6914283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914283 prefixEnd_6914283 := by exact prefixLift 6914283
  have htrace : WordTrace (prefixWord ++ tailWord_6914283) baseStart_6914283 baseEnd_6914283 := by
    simpa [prefixWord, tailWord_6914283, baseEnd_6914283] using wordTrace_append hprefix tailTrace_6914283
  have hstable : (prefixWord ++ tailWord_6914283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914283).length < 2 ^ (prefixWord ++ tailWord_6914283).sum := by decide
  have hdescent : baseEnd_6914283 < baseStart_6914283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914303 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 4]
def baseStart_6914303 : Nat := 118140960795 + 6914303 * 2 ^ 59
def prefixEnd_6914303 : Nat := 4983230072969 + 3 ^ 40 * 6914303 * 2
def baseEnd_6914303 : Nat := 3550360829824366491414205

theorem tailTrace_6914303 : CollatzResearch.WordTrace tailWord_6914303 prefixEnd_6914303 3550360829824366491414205 := by
  unfold tailWord_6914303
  simp only [CollatzResearch.WordTrace]
  refine ⟨252185348269668574783731563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168123565513112383189154375 252185348269668574783731563)
  ·
    refine ⟨378278022404502862175597345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252185348269668574783731563 378278022404502862175597345)
    ·
      refine ⟨283708516803377146631698009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378278022404502862175597345 283708516803377146631698009)
      ·
        refine ⟨212781387602532859973773507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283708516803377146631698009 212781387602532859973773507)
        ·
          refine ⟨319172081403799289960660261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212781387602532859973773507 319172081403799289960660261)
          ·
            refine ⟨59844765263212366867623799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319172081403799289960660261 59844765263212366867623799)
            ·
              refine ⟨89767147894818550301435699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59844765263212366867623799 89767147894818550301435699)
              ·
                refine ⟨134650721842227825452153549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89767147894818550301435699 134650721842227825452153549)
                ·
                  refine ⟨50494020690835434544557581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134650721842227825452153549 50494020690835434544557581)
                  ·
                    refine ⟨18935257759063287954209093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50494020690835434544557581 18935257759063287954209093)
                    ·
                      refine ⟨3550360829824366491414205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18935257759063287954209093 3550360829824366491414205)
                      ·
                        rfl

theorem cell23_6914303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_6914303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914303 prefixEnd_6914303 := by exact prefixLift 6914303
  have htrace : WordTrace (prefixWord ++ tailWord_6914303) baseStart_6914303 baseEnd_6914303 := by
    simpa [prefixWord, tailWord_6914303, baseEnd_6914303] using wordTrace_append hprefix tailTrace_6914303
  have hstable : (prefixWord ++ tailWord_6914303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914303).length < 2 ^ (prefixWord ++ tailWord_6914303).sum := by decide
  have hdescent : baseEnd_6914303 < baseStart_6914303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914334 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_6914334 : Nat := 118140960795 + 6914334 * 2 ^ 59
def prefixEnd_6914334 : Nat := 4983230072969 + 3 ^ 40 * 6914334 * 2
def baseEnd_6914334 : Nat := 1183458915908218623375521

theorem tailTrace_6914334 : CollatzResearch.WordTrace tailWord_6914334 prefixEnd_6914334 1183458915908218623375521 := by
  unfold tailWord_6914334
  simp only [CollatzResearch.WordTrace]
  refine ⟨31523309866569533384763757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168124319288370844718740037 31523309866569533384763757)
  ·
    refine ⟨11821241199963575019286409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31523309866569533384763757 11821241199963575019286409)
    ·
      refine ⟨8865930899972681264464807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11821241199963575019286409 8865930899972681264464807)
      ·
        refine ⟨13298896349959021896697211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865930899972681264464807 13298896349959021896697211)
        ·
          refine ⟨19948344524938532845045817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13298896349959021896697211 19948344524938532845045817)
          ·
            refine ⟨14961258393703899633784363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19948344524938532845045817 14961258393703899633784363)
            ·
              refine ⟨22441887590555849450676545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14961258393703899633784363 22441887590555849450676545)
              ·
                refine ⟨16831415692916887088007409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22441887590555849450676545 16831415692916887088007409)
                ·
                  refine ⟨12623561769687665316005557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16831415692916887088007409 12623561769687665316005557)
                  ·
                    refine ⟨1183458915908218623375521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12623561769687665316005557 1183458915908218623375521)
                    ·
                      rfl

theorem cell23_6914334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_6914334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914334 prefixEnd_6914334 := by exact prefixLift 6914334
  have htrace : WordTrace (prefixWord ++ tailWord_6914334) baseStart_6914334 baseEnd_6914334 := by
    simpa [prefixWord, tailWord_6914334, baseEnd_6914334] using wordTrace_append hprefix tailTrace_6914334
  have hstable : (prefixWord ++ tailWord_6914334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914334).length < 2 ^ (prefixWord ++ tailWord_6914334).sum := by decide
  have hdescent : baseEnd_6914334 < baseStart_6914334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914383 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_6914383 : Nat := 118140960795 + 6914383 * 2 ^ 59
def prefixEnd_6914383 : Nat := 4983230072969 + 3 ^ 40 * 6914383 * 2
def baseEnd_6914383 : Nat := 3550401908276726178413837

theorem tailTrace_6914383 : CollatzResearch.WordTrace tailWord_6914383 prefixEnd_6914383 3550401908276726178413837 := by
  unfold tailWord_6914383
  simp only [CollatzResearch.WordTrace]
  refine ⟨252188266109378748446643803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168125510739585832297762535 252188266109378748446643803)
  ·
    refine ⟨378282399164068122669965705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252188266109378748446643803 378282399164068122669965705)
    ·
      refine ⟨283711799373051092002474279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378282399164068122669965705 283711799373051092002474279)
      ·
        refine ⟨425567699059576638003711419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283711799373051092002474279 425567699059576638003711419)
        ·
          refine ⟨638351548589364957005567129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425567699059576638003711419 638351548589364957005567129)
          ·
            refine ⟨478763661442023717754175347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638351548589364957005567129 478763661442023717754175347)
            ·
              refine ⟨718145492163035576631263021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478763661442023717754175347 718145492163035576631263021)
              ·
                refine ⟨269304559561138341236723633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 718145492163035576631263021 269304559561138341236723633)
                ·
                  refine ⟨201978419670853755927542725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269304559561138341236723633 201978419670853755927542725)
                  ·
                    refine ⟨37870953688285079236414261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201978419670853755927542725 37870953688285079236414261)
                    ·
                      refine ⟨3550401908276726178413837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37870953688285079236414261 3550401908276726178413837)
                      ·
                        rfl

theorem cell23_6914383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_6914383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914383 prefixEnd_6914383 := by exact prefixLift 6914383
  have htrace : WordTrace (prefixWord ++ tailWord_6914383) baseStart_6914383 baseEnd_6914383 := by
    simpa [prefixWord, tailWord_6914383, baseEnd_6914383] using wordTrace_append hprefix tailTrace_6914383
  have hstable : (prefixWord ++ tailWord_6914383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914383).length < 2 ^ (prefixWord ++ tailWord_6914383).sum := by decide
  have hdescent : baseEnd_6914383 < baseStart_6914383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914444 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 1, 1, 4]
def baseStart_6914444 : Nat := 118140960795 + 6914444 * 2 ^ 59
def prefixEnd_6914444 : Nat := 4983230072969 + 3 ^ 40 * 6914444 * 2
def baseEnd_6914444 : Nat := 3550433230596650439751057

theorem tailTrace_6914444 : CollatzResearch.WordTrace tailWord_6914444 prefixEnd_6914444 3550433230596650439751057 := by
  unfold tailWord_6914444
  simp only [CollatzResearch.WordTrace]
  refine ⟨126095245481078877932307193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168126993974771837243076257 126095245481078877932307193)
  ·
    refine ⟨94571434110809158449230395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126095245481078877932307193 94571434110809158449230395)
    ·
      refine ⟨141857151166213737673845593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94571434110809158449230395 141857151166213737673845593)
      ·
        refine ⟨106392863374660303255384195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141857151166213737673845593 106392863374660303255384195)
        ·
          refine ⟨159589295061990454883076293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106392863374660303255384195 159589295061990454883076293)
          ·
            refine ⟨29922992824123210290576805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159589295061990454883076293 29922992824123210290576805)
            ·
              refine ⟨5610561154523101929483151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29922992824123210290576805 5610561154523101929483151)
              ·
                refine ⟨8415841731784652894224727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610561154523101929483151 8415841731784652894224727)
                ·
                  refine ⟨12623762597676979341337091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8415841731784652894224727 12623762597676979341337091)
                  ·
                    refine ⟨18935643896515469012005637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12623762597676979341337091 18935643896515469012005637)
                    ·
                      refine ⟨3550433230596650439751057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18935643896515469012005637 3550433230596650439751057)
                      ·
                        rfl

theorem cell23_6914444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_6914444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914444 prefixEnd_6914444 := by exact prefixLift 6914444
  have htrace : WordTrace (prefixWord ++ tailWord_6914444) baseStart_6914444 baseEnd_6914444 := by
    simpa [prefixWord, tailWord_6914444, baseEnd_6914444] using wordTrace_append hprefix tailTrace_6914444
  have hstable : (prefixWord ++ tailWord_6914444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914444).length < 2 ^ (prefixWord ++ tailWord_6914444).sum := by decide
  have hdescent : baseEnd_6914444 < baseStart_6914444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914471 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 2, 4]
def baseStart_6914471 : Nat := 118140960795 + 6914471 * 2 ^ 59
def prefixEnd_6914471 : Nat := 4983230072969 + 3 ^ 40 * 6914471 * 2
def baseEnd_6914471 : Nat := 1183482364858107278037811

theorem tailTrace_6914471 : CollatzResearch.WordTrace tailWord_6914471 prefixEnd_6914471 1183482364858107278037811 := by
  unfold tailWord_6914471
  simp only [CollatzResearch.WordTrace]
  refine ⟨252191475733059939475847267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168127650488706626317231511 252191475733059939475847267)
  ·
    refine ⟨378287213599589909213770901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252191475733059939475847267 378287213599589909213770901)
    ·
      refine ⟨17732213137480776994395511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 378287213599589909213770901 17732213137480776994395511)
      ·
        refine ⟨26598319706221165491593267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17732213137480776994395511 26598319706221165491593267)
        ·
          refine ⟨39897479559331748237389901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26598319706221165491593267 39897479559331748237389901)
          ·
            refine ⟨14961554834749405589021213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39897479559331748237389901 14961554834749405589021213)
            ·
              refine ⟨5610583063031027095882955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14961554834749405589021213 5610583063031027095882955)
              ·
                refine ⟨8415874594546540643824433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610583063031027095882955 8415874594546540643824433)
                ·
                  refine ⟨6311905945909905482868325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8415874594546540643824433 6311905945909905482868325)
                  ·
                    refine ⟨1183482364858107278037811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6311905945909905482868325 1183482364858107278037811)
                    ·
                      rfl

theorem cell23_6914471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_6914471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914471 prefixEnd_6914471 := by exact prefixLift 6914471
  have htrace : WordTrace (prefixWord ++ tailWord_6914471) baseStart_6914471 baseEnd_6914471 := by
    simpa [prefixWord, tailWord_6914471, baseEnd_6914471] using wordTrace_append hprefix tailTrace_6914471
  have hstable : (prefixWord ++ tailWord_6914471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914471).length < 2 ^ (prefixWord ++ tailWord_6914471).sum := by decide
  have hdescent : baseEnd_6914471 < baseStart_6914471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914494 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_6914494 : Nat := 118140960795 + 6914494 * 2 ^ 59
def prefixEnd_6914494 : Nat := 4983230072969 + 3 ^ 40 * 6914494 * 2
def baseEnd_6914494 : Nat := 3550458904629375244125827

theorem tailTrace_6914494 : CollatzResearch.WordTrace tailWord_6914494 prefixEnd_6914494 3550458904629375244125827 := by
  unfold tailWord_6914494
  simp only [CollatzResearch.WordTrace]
  refine ⟨31524039326497076800491817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168128209741317742935956357 31524039326497076800491817)
  ·
    refine ⟨23643029494872807600368863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31524039326497076800491817 23643029494872807600368863)
    ·
      refine ⟨35464544242309211400553295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23643029494872807600368863 35464544242309211400553295)
      ·
        refine ⟨53196816363463817100829943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35464544242309211400553295 53196816363463817100829943)
        ·
          refine ⟨79795224545195725651244915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53196816363463817100829943 79795224545195725651244915)
          ·
            refine ⟨119692836817793588476867373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79795224545195725651244915 119692836817793588476867373)
            ·
              refine ⟨44884813806672595678825265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119692836817793588476867373 44884813806672595678825265)
              ·
                refine ⟨33663610355004446759118949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44884813806672595678825265 33663610355004446759118949)
                ·
                  refine ⟨6311926941563333767334803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33663610355004446759118949 6311926941563333767334803)
                  ·
                    refine ⟨9467890412345000651002205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6311926941563333767334803 9467890412345000651002205)
                    ·
                      refine ⟨3550458904629375244125827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9467890412345000651002205 3550458904629375244125827)
                      ·
                        rfl

theorem cell23_6914494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_6914494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914494 prefixEnd_6914494 := by exact prefixLift 6914494
  have htrace : WordTrace (prefixWord ++ tailWord_6914494) baseStart_6914494 baseEnd_6914494 := by
    simpa [prefixWord, tailWord_6914494, baseEnd_6914494] using wordTrace_append hprefix tailTrace_6914494
  have hstable : (prefixWord ++ tailWord_6914494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914494).length < 2 ^ (prefixWord ++ tailWord_6914494).sum := by decide
  have hdescent : baseEnd_6914494 < baseStart_6914494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914520 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_6914520 : Nat := 118140960795 + 6914520 * 2 ^ 59
def prefixEnd_6914520 : Nat := 4983230072969 + 3 ^ 40 * 6914520 * 2
def baseEnd_6914520 : Nat := 3550472255126392142400707

theorem tailTrace_6914520 : CollatzResearch.WordTrace tailWord_6914520 prefixEnd_6914520 3550472255126392142400707 := by
  unfold tailWord_6914520
  simp only [CollatzResearch.WordTrace]
  refine ⟨126096631454941210422190507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168128841939921613896254009 126096631454941210422190507)
  ·
    refine ⟨189144947182411815633285761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126096631454941210422190507 189144947182411815633285761)
    ·
      refine ⟨141858710386808861724964321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189144947182411815633285761 141858710386808861724964321)
      ·
        refine ⟨106394032790106646293723241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141858710386808861724964321 106394032790106646293723241)
        ·
          refine ⟨79795524592579984720292431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106394032790106646293723241 79795524592579984720292431)
          ·
            refine ⟨119693286888869977080438647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79795524592579984720292431 119693286888869977080438647)
            ·
              refine ⟨179539930333304965620657971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119693286888869977080438647 179539930333304965620657971)
              ·
                refine ⟨269309895499957448430986957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179539930333304965620657971 269309895499957448430986957)
                ·
                  refine ⟨100991210812484043161620109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269309895499957448430986957 100991210812484043161620109)
                  ·
                    refine ⟨37871704054681516185607541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100991210812484043161620109 37871704054681516185607541)
                    ·
                      refine ⟨3550472255126392142400707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37871704054681516185607541 3550472255126392142400707)
                      ·
                        rfl

theorem cell23_6914520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_6914520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914520 prefixEnd_6914520 := by exact prefixLift 6914520
  have htrace : WordTrace (prefixWord ++ tailWord_6914520) baseStart_6914520 baseEnd_6914520 := by
    simpa [prefixWord, tailWord_6914520, baseEnd_6914520] using wordTrace_append hprefix tailTrace_6914520
  have hstable : (prefixWord ++ tailWord_6914520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914520).length < 2 ^ (prefixWord ++ tailWord_6914520).sum := by decide
  have hdescent : baseEnd_6914520 < baseStart_6914520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914538 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_6914538 : Nat := 118140960795 + 6914538 * 2 ^ 59
def prefixEnd_6914538 : Nat := 4983230072969 + 3 ^ 40 * 6914538 * 2
def baseEnd_6914538 : Nat := 3550481497778173071975625

theorem tailTrace_6914538 : CollatzResearch.WordTrace tailWord_6914538 prefixEnd_6914538 3550481497778173071975625 := by
  unfold tailWord_6914538
  simp only [CollatzResearch.WordTrace]
  refine ⟨63048479855954302479634067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168129279615878139945690845 63048479855954302479634067)
  ·
    refine ⟨94572719783931453719451101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63048479855954302479634067 94572719783931453719451101)
    ·
      refine ⟨35464769918974295144794163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94572719783931453719451101 35464769918974295144794163)
      ·
        refine ⟨53197154878461442717191245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35464769918974295144794163 53197154878461442717191245)
        ·
          refine ⟨19948933079423041018946717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53197154878461442717191245 19948933079423041018946717)
          ·
            refine ⟨7480849904783640382105019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19948933079423041018946717 7480849904783640382105019)
            ·
              refine ⟨11221274857175460573157529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7480849904783640382105019 11221274857175460573157529)
              ·
                refine ⟨8415956142881595429868147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11221274857175460573157529 8415956142881595429868147)
                ·
                  refine ⟨12623934214322393144802221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8415956142881595429868147 12623934214322393144802221)
                  ·
                    refine ⟨4733975330370897429300833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12623934214322393144802221 4733975330370897429300833)
                    ·
                      refine ⟨3550481497778173071975625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4733975330370897429300833 3550481497778173071975625)
                      ·
                        rfl

theorem cell23_6914538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_6914538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914538 prefixEnd_6914538 := by exact prefixLift 6914538
  have htrace : WordTrace (prefixWord ++ tailWord_6914538) baseStart_6914538 baseEnd_6914538 := by
    simpa [prefixWord, tailWord_6914538, baseEnd_6914538] using wordTrace_append hprefix tailTrace_6914538
  have hstable : (prefixWord ++ tailWord_6914538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914538).length < 2 ^ (prefixWord ++ tailWord_6914538).sum := by decide
  have hdescent : baseEnd_6914538 < baseStart_6914538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914540 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 9]
def baseStart_6914540 : Nat := 118140960795 + 6914540 * 2 ^ 59
def prefixEnd_6914540 : Nat := 4983230072969 + 3 ^ 40 * 6914540 * 2
def baseEnd_6914540 : Nat := 394498058304386896016735

theorem tailTrace_6914540 : CollatzResearch.WordTrace tailWord_6914540 prefixEnd_6914540 394498058304386896016735 := by
  unfold tailWord_6914540
  simp only [CollatzResearch.WordTrace]
  refine ⟨126096996184904982130054537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168129328246539976173406049 126096996184904982130054537)
  ·
    refine ⟨94572747138678736597540903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126096996184904982130054537 94572747138678736597540903)
    ·
      refine ⟨141859120708018104896311355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94572747138678736597540903 141859120708018104896311355)
      ·
        refine ⟨212788681062027157344467033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141859120708018104896311355 212788681062027157344467033)
        ·
          refine ⟨159591510796520368008350275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212788681062027157344467033 159591510796520368008350275)
          ·
            refine ⟨239387266194780552012525413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159591510796520368008350275 239387266194780552012525413)
            ·
              refine ⟨44885112411521353502348515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239387266194780552012525413 44885112411521353502348515)
              ·
                refine ⟨67327668617282030253522773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44885112411521353502348515 67327668617282030253522773)
                ·
                  refine ⟨394498058304386896016735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67327668617282030253522773 394498058304386896016735)
                  ·
                    rfl

theorem cell23_6914540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_6914540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914540 prefixEnd_6914540 := by exact prefixLift 6914540
  have htrace : WordTrace (prefixWord ++ tailWord_6914540) baseStart_6914540 baseEnd_6914540 := by
    simpa [prefixWord, tailWord_6914540, baseEnd_6914540] using wordTrace_append hprefix tailTrace_6914540
  have hstable : (prefixWord ++ tailWord_6914540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914540).length < 2 ^ (prefixWord ++ tailWord_6914540).sum := by decide
  have hdescent : baseEnd_6914540 < baseStart_6914540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914584 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 2, 3, 3]
def baseStart_6914584 : Nat := 118140960795 + 6914584 * 2 ^ 59
def prefixEnd_6914584 : Nat := 4983230072969 + 3 ^ 40 * 6914584 * 2
def baseEnd_6914584 : Nat := 3550505117888279892000413

theorem tailTrace_6914584 : CollatzResearch.WordTrace tailWord_6914584 prefixEnd_6914584 3550505117888279892000413 := by
  unfold tailWord_6914584
  simp only [CollatzResearch.WordTrace]
  refine ⟨126097798590825279887355403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168130398121100373183140537 126097798590825279887355403)
  ·
    refine ⟨189146697886237919831033105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126097798590825279887355403 189146697886237919831033105)
    ·
      refine ⟨141860023414678439873274829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189146697886237919831033105 141860023414678439873274829)
      ·
        refine ⟨53197508780504414952478061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141860023414678439873274829 53197508780504414952478061)
        ·
          refine ⟨19949065792689155607179273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53197508780504414952478061 19949065792689155607179273)
          ·
            refine ⟨14961799344516866705384455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19949065792689155607179273 14961799344516866705384455)
            ·
              refine ⟨22442699016775300058076683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14961799344516866705384455 22442699016775300058076683)
              ·
                refine ⟨33664048525162950087115025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22442699016775300058076683 33664048525162950087115025)
                ·
                  refine ⟨25248036393872212565336269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33664048525162950087115025 25248036393872212565336269)
                  ·
                    refine ⟨9468013647702079712001101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25248036393872212565336269 9468013647702079712001101)
                    ·
                      refine ⟨3550505117888279892000413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9468013647702079712001101 3550505117888279892000413)
                      ·
                        rfl

theorem cell23_6914584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_6914584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914584 prefixEnd_6914584 := by exact prefixLift 6914584
  have htrace : WordTrace (prefixWord ++ tailWord_6914584) baseStart_6914584 baseEnd_6914584 := by
    simpa [prefixWord, tailWord_6914584, baseEnd_6914584] using wordTrace_append hprefix tailTrace_6914584
  have hstable : (prefixWord ++ tailWord_6914584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914584).length < 2 ^ (prefixWord ++ tailWord_6914584).sum := by decide
  have hdescent : baseEnd_6914584 < baseStart_6914584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914594 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_6914594 : Nat := 118140960795 + 6914594 * 2 ^ 59
def prefixEnd_6914594 : Nat := 4983230072969 + 3 ^ 40 * 6914594 * 2
def baseEnd_6914594 : Nat := 3550510252694824852875367

theorem tailTrace_6914594 : CollatzResearch.WordTrace tailWord_6914594 prefixEnd_6914594 3550510252694824852875367 := by
  unfold tailWord_6914594
  simp only [CollatzResearch.WordTrace]
  refine ⟨63048990477903582870643709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168130641274409554321716557 63048990477903582870643709)
  ·
    refine ⟨23643371429213843576491391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63048990477903582870643709 23643371429213843576491391)
    ·
      refine ⟨35465057143820765364737087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23643371429213843576491391 35465057143820765364737087)
      ·
        refine ⟨53197585715731148047105631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35465057143820765364737087 53197585715731148047105631)
        ·
          refine ⟨79796378573596722070658447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53197585715731148047105631 79796378573596722070658447)
          ·
            refine ⟨119694567860395083105987671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79796378573596722070658447 119694567860395083105987671)
            ·
              refine ⟨179541851790592624658981507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119694567860395083105987671 179541851790592624658981507)
              ·
                refine ⟨269312777685888936988472261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179541851790592624658981507 269312777685888936988472261)
                ·
                  refine ⟨50496145816104175685338549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269312777685888936988472261 50496145816104175685338549)
                  ·
                    refine ⟨4734013670259766470500489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50496145816104175685338549 4734013670259766470500489)
                    ·
                      refine ⟨3550510252694824852875367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734013670259766470500489 3550510252694824852875367)
                      ·
                        rfl

theorem cell23_6914594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_6914594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914594 prefixEnd_6914594 := by exact prefixLift 6914594
  have htrace : WordTrace (prefixWord ++ tailWord_6914594) baseStart_6914594 baseEnd_6914594 := by
    simpa [prefixWord, tailWord_6914594, baseEnd_6914594] using wordTrace_append hprefix tailTrace_6914594
  have hstable : (prefixWord ++ tailWord_6914594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914594).length < 2 ^ (prefixWord ++ tailWord_6914594).sum := by decide
  have hdescent : baseEnd_6914594 < baseStart_6914594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914624 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 2, 4, 2]
def baseStart_6914624 : Nat := 118140960795 + 6914624 * 2 ^ 59
def prefixEnd_6914624 : Nat := 4983230072969 + 3 ^ 40 * 6914624 * 2
def baseEnd_6914624 : Nat := 3550525657114459735500229

theorem tailTrace_6914624 : CollatzResearch.WordTrace tailWord_6914624 prefixEnd_6914624 3550525657114459735500229 := by
  unfold tailWord_6914624
  simp only [CollatzResearch.WordTrace]
  refine ⟨126098528050752823303083463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168131370734337097737444617 126098528050752823303083463)
  ·
    refine ⟨189147792076129234954625195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126098528050752823303083463 189147792076129234954625195)
    ·
      refine ⟨283721688114193852431937793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189147792076129234954625195 283721688114193852431937793)
      ·
        refine ⟨212791266085645389323953345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283721688114193852431937793 212791266085645389323953345)
        ·
          refine ⟨159593449564234041992965009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212791266085645389323953345 159593449564234041992965009)
          ·
            refine ⟨119695087173175531494723757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159593449564234041992965009 119695087173175531494723757)
            ·
              refine ⟨44885657689940824310521409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119695087173175531494723757 44885657689940824310521409)
              ·
                refine ⟨33664243267455618232891057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44885657689940824310521409 33664243267455618232891057)
                ·
                  refine ⟨25248182450591713674668293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33664243267455618232891057 25248182450591713674668293)
                  ·
                    refine ⟨4734034209485946314000305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25248182450591713674668293 4734034209485946314000305)
                    ·
                      refine ⟨3550525657114459735500229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734034209485946314000305 3550525657114459735500229)
                      ·
                        rfl

theorem cell23_6914624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 4, 2].length) (baseStart_6914624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914624 prefixEnd_6914624 := by exact prefixLift 6914624
  have htrace : WordTrace (prefixWord ++ tailWord_6914624) baseStart_6914624 baseEnd_6914624 := by
    simpa [prefixWord, tailWord_6914624, baseEnd_6914624] using wordTrace_append hprefix tailTrace_6914624
  have hstable : (prefixWord ++ tailWord_6914624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914624).length < 2 ^ (prefixWord ++ tailWord_6914624).sum := by decide
  have hdescent : baseEnd_6914624 < baseStart_6914624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914634 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 3, 4]
def baseStart_6914634 : Nat := 118140960795 + 6914634 * 2 ^ 59
def prefixEnd_6914634 : Nat := 4983230072969 + 3 ^ 40 * 6914634 * 2
def baseEnd_6914634 : Nat := 1183510263973668232125061

theorem tailTrace_6914634 : CollatzResearch.WordTrace tailWord_6914634 prefixEnd_6914634 1183510263973668232125061 := by
  unfold tailWord_6914634
  simp only [CollatzResearch.WordTrace]
  refine ⟨63049355207867354578507739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168131613887646278876020637 63049355207867354578507739)
  ·
    refine ⟨94574032811801031867761609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63049355207867354578507739 94574032811801031867761609)
    ·
      refine ⟨70930524608850773900821207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94574032811801031867761609 70930524608850773900821207)
      ·
        refine ⟨106395786913276160851231811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70930524608850773900821207 106395786913276160851231811)
        ·
          refine ⟨159593680369914241276847717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106395786913276160851231811 159593680369914241276847717)
          ·
            refine ⟨29923815069358920239408947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159593680369914241276847717 29923815069358920239408947)
            ·
              refine ⟨44885722604038380359113421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29923815069358920239408947 44885722604038380359113421)
              ·
                refine ⟨16832145976514392634667533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44885722604038380359113421 16832145976514392634667533)
                ·
                  refine ⟨6312054741192897238000325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16832145976514392634667533 6312054741192897238000325)
                  ·
                    refine ⟨1183510263973668232125061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6312054741192897238000325 1183510263973668232125061)
                    ·
                      rfl

theorem cell23_6914634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_6914634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914634 prefixEnd_6914634 := by exact prefixLift 6914634
  have htrace : WordTrace (prefixWord ++ tailWord_6914634) baseStart_6914634 baseEnd_6914634 := by
    simpa [prefixWord, tailWord_6914634, baseEnd_6914634] using wordTrace_append hprefix tailTrace_6914634
  have hstable : (prefixWord ++ tailWord_6914634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914634).length < 2 ^ (prefixWord ++ tailWord_6914634).sum := by decide
  have hdescent : baseEnd_6914634 < baseStart_6914634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914644 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_6914644 : Nat := 118140960795 + 6914644 * 2 ^ 59
def prefixEnd_6914644 : Nat := 4983230072969 + 3 ^ 40 * 6914644 * 2
def baseEnd_6914644 : Nat := 3550535926727549657250137

theorem tailTrace_6914644 : CollatzResearch.WordTrace tailWord_6914644 prefixEnd_6914644 3550535926727549657250137 := by
  unfold tailWord_6914644
  simp only [CollatzResearch.WordTrace]
  refine ⟨126098892780716595010947493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168131857040955460014596657 126098892780716595010947493)
  ·
    refine ⟨23643542396384361564552655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126098892780716595010947493 23643542396384361564552655)
    ·
      refine ⟨35465313594576542346828983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23643542396384361564552655 35465313594576542346828983)
      ·
        refine ⟨53197970391864813520243475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35465313594576542346828983 53197970391864813520243475)
        ·
          refine ⟨79796955587797220280365213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53197970391864813520243475 79796955587797220280365213)
          ·
            refine ⟨29923858345423957605136955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79796955587797220280365213 29923858345423957605136955)
            ·
              refine ⟨44885787518135936407705433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29923858345423957605136955 44885787518135936407705433)
              ·
                refine ⟨33664340638601952305779075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44885787518135936407705433 33664340638601952305779075)
                ·
                  refine ⟨50496510957902928458668613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33664340638601952305779075 50496510957902928458668613)
                  ·
                    refine ⟨9468095804606799086000365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50496510957902928458668613 9468095804606799086000365)
                    ·
                      refine ⟨3550535926727549657250137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9468095804606799086000365 3550535926727549657250137)
                      ·
                        rfl

theorem cell23_6914644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_6914644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914644 prefixEnd_6914644 := by exact prefixLift 6914644
  have htrace : WordTrace (prefixWord ++ tailWord_6914644) baseStart_6914644 baseEnd_6914644 := by
    simpa [prefixWord, tailWord_6914644, baseEnd_6914644] using wordTrace_append hprefix tailTrace_6914644
  have hstable : (prefixWord ++ tailWord_6914644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914644).length < 2 ^ (prefixWord ++ tailWord_6914644).sum := by decide
  have hdescent : baseEnd_6914644 < baseStart_6914644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914678 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_6914678 : Nat := 118140960795 + 6914678 * 2 ^ 59
def prefixEnd_6914678 : Nat := 4983230072969 + 3 ^ 40 * 6914678 * 2
def baseEnd_6914678 : Nat := 3550553385069802524224981

theorem tailTrace_6914678 : CollatzResearch.WordTrace tailWord_6914678 prefixEnd_6914678 3550553385069802524224981 := by
  unfold tailWord_6914678
  simp only [CollatzResearch.WordTrace]
  refine ⟨15762439102706875864289543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168132683762206675885755125 15762439102706875864289543)
  ·
    refine ⟨23643658654060313796434315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15762439102706875864289543 23643658654060313796434315)
    ·
      refine ⟨35465487981090470694651473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23643658654060313796434315 35465487981090470694651473)
      ·
        refine ⟨26599115985817853020988605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35465487981090470694651473 26599115985817853020988605)
        ·
          refine ⟨9974668494681694882870727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26599115985817853020988605 9974668494681694882870727)
          ·
            refine ⟨14962002742022542324306091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9974668494681694882870727 14962002742022542324306091)
            ·
              refine ⟨22443004113033813486459137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14962002742022542324306091 22443004113033813486459137)
              ·
                refine ⟨16832253084775360114844353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22443004113033813486459137 16832253084775360114844353)
                ·
                  refine ⟨12624189813581520086133265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16832253084775360114844353 12624189813581520086133265)
                  ·
                    refine ⟨9468142360186140064599949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12624189813581520086133265 9468142360186140064599949)
                    ·
                      refine ⟨3550553385069802524224981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9468142360186140064599949 3550553385069802524224981)
                      ·
                        rfl

theorem cell23_6914678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_6914678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914678 prefixEnd_6914678 := by exact prefixLift 6914678
  have htrace : WordTrace (prefixWord ++ tailWord_6914678) baseStart_6914678 baseEnd_6914678 := by
    simpa [prefixWord, tailWord_6914678, baseEnd_6914678] using wordTrace_append hprefix tailTrace_6914678
  have hstable : (prefixWord ++ tailWord_6914678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914678).length < 2 ^ (prefixWord ++ tailWord_6914678).sum := by decide
  have hdescent : baseEnd_6914678 < baseStart_6914678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914685 : List Nat := [1, 4, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_6914685 : Nat := 118140960795 + 6914685 * 2 ^ 59
def prefixEnd_6914685 : Nat := 4983230072969 + 3 ^ 40 * 6914685 * 2
def baseEnd_6914685 : Nat := 1183518993144794665612483

theorem tailTrace_6914685 : CollatzResearch.WordTrace tailWord_6914685 prefixEnd_6914685 1183518993144794665612483 := by
  unfold tailWord_6914685
  simp only [CollatzResearch.WordTrace]
  refine ⟨252199280954284654024137509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168132853969523102682758339 252199280954284654024137509)
  ·
    refine ⟨47287365178928372629525783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252199280954284654024137509 47287365178928372629525783)
    ·
      refine ⟨70931047768392558944288675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47287365178928372629525783 70931047768392558944288675)
      ·
        refine ⟨106396571652588838416433013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70931047768392558944288675 106396571652588838416433013)
        ·
          refine ⟨9974678592430203601540595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106396571652588838416433013 9974678592430203601540595)
          ·
            refine ⟨14962017888645305402310893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9974678592430203601540595 14962017888645305402310893)
            ·
              refine ⟨5610756708241989525866585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14962017888645305402310893 5610756708241989525866585)
              ·
                refine ⟨4208067531181492144399939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5610756708241989525866585 4208067531181492144399939)
                ·
                  refine ⟨6312101296772238216599909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208067531181492144399939 6312101296772238216599909)
                  ·
                    refine ⟨1183518993144794665612483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6312101296772238216599909 1183518993144794665612483)
                    ·
                      rfl

theorem cell23_6914685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_6914685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914685 prefixEnd_6914685 := by exact prefixLift 6914685
  have htrace : WordTrace (prefixWord ++ tailWord_6914685) baseStart_6914685 baseEnd_6914685 := by
    simpa [prefixWord, tailWord_6914685, baseEnd_6914685] using wordTrace_append hprefix tailTrace_6914685
  have hstable : (prefixWord ++ tailWord_6914685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914685).length < 2 ^ (prefixWord ++ tailWord_6914685).sum := by decide
  have hdescent : baseEnd_6914685 < baseStart_6914685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914691 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 3, 1, 3]
def baseStart_6914691 : Nat := 118140960795 + 6914691 * 2 ^ 59
def prefixEnd_6914691 : Nat := 4983230072969 + 3 ^ 40 * 6914691 * 2
def baseEnd_6914691 : Nat := 3550560060318310973362421

theorem tailTrace_6914691 : CollatzResearch.WordTrace tailWord_6914691 prefixEnd_6914691 3550560060318310973362421 := by
  unfold tailWord_6914691
  simp only [CollatzResearch.WordTrace]
  refine ⟨252199499792262917048855927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168132999861508611365903951 252199499792262917048855927)
  ·
    refine ⟨378299249688394375573283891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252199499792262917048855927 378299249688394375573283891)
    ·
      refine ⟨567448874532591563359925837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378299249688394375573283891 567448874532591563359925837)
      ·
        refine ⟨212793327949721836259972189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 567448874532591563359925837 212793327949721836259972189)
        ·
          refine ⟨79797497981145688597489571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212793327949721836259972189 79797497981145688597489571)
          ·
            refine ⟨119696246971718532896234357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79797497981145688597489571 119696246971718532896234357)
            ·
              refine ⟨11221523153598612459021971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119696246971718532896234357 11221523153598612459021971)
              ·
                refine ⟨16832284730397918688532957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11221523153598612459021971 16832284730397918688532957)
                ·
                  refine ⟨6312106773899219508199859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16832284730397918688532957 6312106773899219508199859)
                  ·
                    refine ⟨9468160160848829262299789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6312106773899219508199859 9468160160848829262299789)
                    ·
                      refine ⟨3550560060318310973362421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9468160160848829262299789 3550560060318310973362421)
                      ·
                        rfl

theorem cell23_6914691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_6914691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914691 prefixEnd_6914691 := by exact prefixLift 6914691
  have htrace : WordTrace (prefixWord ++ tailWord_6914691) baseStart_6914691 baseEnd_6914691 := by
    simpa [prefixWord, tailWord_6914691, baseEnd_6914691] using wordTrace_append hprefix tailTrace_6914691
  have hstable : (prefixWord ++ tailWord_6914691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914691).length < 2 ^ (prefixWord ++ tailWord_6914691).sum := by decide
  have hdescent : baseEnd_6914691 < baseStart_6914691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914697 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 4]
def baseStart_6914697 : Nat := 118140960795 + 6914697 * 2 ^ 59
def prefixEnd_6914697 : Nat := 4983230072969 + 3 ^ 40 * 6914697 * 2
def baseEnd_6914697 : Nat := 3550563141202237949887393

theorem tailTrace_6914697 : CollatzResearch.WordTrace tailWord_6914697 prefixEnd_6914697 3550563141202237949887393 := by
  unfold tailWord_6914697
  simp only [CollatzResearch.WordTrace]
  refine ⟨252199718630241180073574345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168133145753494120049049563 252199718630241180073574345)
  ·
    refine ⟨189149788972680885055180759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252199718630241180073574345 189149788972680885055180759)
    ·
      refine ⟨283724683459021327582771139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189149788972680885055180759 283724683459021327582771139)
      ·
        refine ⟨425587025188531991374156709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283724683459021327582771139 425587025188531991374156709)
        ·
          refine ⟨79797567222849748382654383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425587025188531991374156709 79797567222849748382654383)
          ·
            refine ⟨119696350834274622573981575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79797567222849748382654383 119696350834274622573981575)
            ·
              refine ⟨179544526251411933860972363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119696350834274622573981575 179544526251411933860972363)
              ·
                refine ⟨269316789377117900791458545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179544526251411933860972363 269316789377117900791458545)
                ·
                  refine ⟨201987592032838425593593909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269316789377117900791458545 201987592032838425593593909)
                  ·
                    refine ⟨18936336753078602399399429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 201987592032838425593593909 18936336753078602399399429)
                    ·
                      refine ⟨3550563141202237949887393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18936336753078602399399429 3550563141202237949887393)
                      ·
                        rfl

theorem cell23_6914697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_6914697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914697 prefixEnd_6914697 := by exact prefixLift 6914697
  have htrace : WordTrace (prefixWord ++ tailWord_6914697) baseStart_6914697 baseEnd_6914697 := by
    simpa [prefixWord, tailWord_6914697, baseEnd_6914697] using wordTrace_append hprefix tailTrace_6914697
  have hstable : (prefixWord ++ tailWord_6914697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914697).length < 2 ^ (prefixWord ++ tailWord_6914697).sum := by decide
  have hdescent : baseEnd_6914697 < baseStart_6914697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914698 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 6]
def baseStart_6914698 : Nat := 118140960795 + 6914698 * 2 ^ 59
def prefixEnd_6914698 : Nat := 4983230072969 + 3 ^ 40 * 6914698 * 2
def baseEnd_6914698 : Nat := 394507072742543605108321

theorem tailTrace_6914698 : CollatzResearch.WordTrace tailWord_6914698 prefixEnd_6914698 394507072742543605108321 := by
  unfold tailWord_6914698
  simp only [CollatzResearch.WordTrace]
  refine ⟨63049938775809389311090187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168133170068825038162907165 63049938775809389311090187)
  ·
    refine ⟨94574908163714083966635281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63049938775809389311090187 94574908163714083966635281)
    ·
      refine ⟨70931181122785562974976461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94574908163714083966635281 70931181122785562974976461)
      ·
        refine ⟨26599192921044586115616173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70931181122785562974976461 26599192921044586115616173)
        ·
          refine ⟨9974697345391719793356065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26599192921044586115616173 9974697345391719793356065)
          ·
            refine ⟨7481023009043789845017049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9974697345391719793356065 7481023009043789845017049)
            ·
              refine ⟨5610767256782842383762787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7481023009043789845017049 5610767256782842383762787)
              ·
                refine ⟨8416150885174263575644181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610767256782842383762787 8416150885174263575644181)
                ·
                  refine ⟨394507072742543605108321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8416150885174263575644181 394507072742543605108321)
                  ·
                    rfl

theorem cell23_6914698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_6914698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914698 prefixEnd_6914698 := by exact prefixLift 6914698
  have htrace : WordTrace (prefixWord ++ tailWord_6914698) baseStart_6914698 baseEnd_6914698 := by
    simpa [prefixWord, tailWord_6914698, baseEnd_6914698] using wordTrace_append hprefix tailTrace_6914698
  have hstable : (prefixWord ++ tailWord_6914698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914698).length < 2 ^ (prefixWord ++ tailWord_6914698).sum := by decide
  have hdescent : baseEnd_6914698 < baseStart_6914698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914724 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_6914724 : Nat := 118140960795 + 6914724 * 2 ^ 59
def prefixEnd_6914724 : Nat := 4983230072969 + 3 ^ 40 * 6914724 * 2
def baseEnd_6914724 : Nat := 1183525668393303114749923

theorem tailTrace_6914724 : CollatzResearch.WordTrace tailWord_6914724 prefixEnd_6914724 1183525668393303114749923 := by
  unfold tailWord_6914724
  simp only [CollatzResearch.WordTrace]
  refine ⟨126100351700571681842403613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168133802267428909123204817 126100351700571681842403613)
  ·
    refine ⟨47287631887714380690901355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126100351700571681842403613 47287631887714380690901355)
    ·
      refine ⟨70931447831571571036352033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47287631887714380690901355 70931447831571571036352033)
      ·
        refine ⟨53198585873678678277264025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70931447831571571036352033 53198585873678678277264025)
        ·
          refine ⟨39898939405259008707948019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53198585873678678277264025 39898939405259008707948019)
          ·
            refine ⟨59848409107888513061922029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39898939405259008707948019 59848409107888513061922029)
            ·
              refine ⟨22443153415458192398220761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59848409107888513061922029 22443153415458192398220761)
              ·
                refine ⟨16832365061593644298665571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22443153415458192398220761 16832365061593644298665571)
                ·
                  refine ⟨25248547592390466447998357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16832365061593644298665571 25248547592390466447998357)
                  ·
                    refine ⟨1183525668393303114749923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25248547592390466447998357 1183525668393303114749923)
                    ·
                      rfl

theorem cell23_6914724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_6914724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914724 prefixEnd_6914724 := by exact prefixLift 6914724
  have htrace : WordTrace (prefixWord ++ tailWord_6914724) baseStart_6914724 baseEnd_6914724 := by
    simpa [prefixWord, tailWord_6914724, baseEnd_6914724] using wordTrace_append hprefix tailTrace_6914724
  have hstable : (prefixWord ++ tailWord_6914724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914724).length < 2 ^ (prefixWord ++ tailWord_6914724).sum := by decide
  have hdescent : baseEnd_6914724 < baseStart_6914724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914748 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 3, 2, 2]
def baseStart_6914748 : Nat := 118140960795 + 6914748 * 2 ^ 59
def prefixEnd_6914748 : Nat := 4983230072969 + 3 ^ 40 * 6914748 * 2
def baseEnd_6914748 : Nat := 3550589328715617250349659

theorem tailTrace_6914748 : CollatzResearch.WordTrace tailWord_6914748 prefixEnd_6914748 3550589328715617250349659 := by
  unfold tailWord_6914748
  simp only [CollatzResearch.WordTrace]
  refine ⟨126100789376528207891840449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168134385835370943855787265 126100789376528207891840449)
  ·
    refine ⟨94575592032396155918880337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126100789376528207891840449 94575592032396155918880337)
    ·
      refine ⟨70931694024297116939160253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94575592032396155918880337 70931694024297116939160253)
      ·
        refine ⟨26599385259111418852185095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70931694024297116939160253 26599385259111418852185095)
        ·
          refine ⟨39899077888667128278277643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26599385259111418852185095 39899077888667128278277643)
          ·
            refine ⟨59848616833000692417416465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39899077888667128278277643 59848616833000692417416465)
            ·
              refine ⟨44886462624750519313062349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59848616833000692417416465 44886462624750519313062349)
              ·
                refine ⟨16832423484281444742398381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44886462624750519313062349 16832423484281444742398381)
                ·
                  refine ⟨6312158806605541778399393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16832423484281444742398381 6312158806605541778399393)
                  ·
                    refine ⟨4734119104954156333799545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6312158806605541778399393 4734119104954156333799545)
                    ·
                      refine ⟨3550589328715617250349659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734119104954156333799545 3550589328715617250349659)
                      ·
                        rfl

theorem cell23_6914748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_6914748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914748 prefixEnd_6914748 := by exact prefixLift 6914748
  have htrace : WordTrace (prefixWord ++ tailWord_6914748) baseStart_6914748 baseEnd_6914748 := by
    simpa [prefixWord, tailWord_6914748, baseEnd_6914748] using wordTrace_append hprefix tailTrace_6914748
  have hstable : (prefixWord ++ tailWord_6914748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914748).length < 2 ^ (prefixWord ++ tailWord_6914748).sum := by decide
  have hdescent : baseEnd_6914748 < baseStart_6914748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914785 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 1, 2, 3]
def baseStart_6914785 : Nat := 118140960795 + 6914785 * 2 ^ 59
def prefixEnd_6914785 : Nat := 4983230072969 + 3 ^ 40 * 6914785 * 2
def baseEnd_6914785 : Nat := 3550608327499833605586989

theorem tailTrace_6914785 : CollatzResearch.WordTrace tailWord_6914785 prefixEnd_6914785 3550608327499833605586989 := by
  unfold tailWord_6914785
  simp only [CollatzResearch.WordTrace]
  refine ⟨252202928253922371102777809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168135285502614914068518539 252202928253922371102777809)
  ·
    refine ⟨189152196190441778327083357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252202928253922371102777809 189152196190441778327083357)
    ·
      refine ⟨70932073571415666872656259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189152196190441778327083357 70932073571415666872656259)
      ·
        refine ⟨106398110357123500308984389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70932073571415666872656259 106398110357123500308984389)
        ·
          refine ⟨19949645691960656307934573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106398110357123500308984389 19949645691960656307934573)
          ·
            refine ⟨7481117134485246115475465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19949645691960656307934573 7481117134485246115475465)
            ·
              refine ⟨5610837850863934586606599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7481117134485246115475465 5610837850863934586606599)
              ·
                refine ⟨8416256776295901879909899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610837850863934586606599 8416256776295901879909899)
                ·
                  refine ⟨12624385164443852819864849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8416256776295901879909899 12624385164443852819864849)
                  ·
                    refine ⟨9468288873332889614898637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12624385164443852819864849 9468288873332889614898637)
                    ·
                      refine ⟨3550608327499833605586989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9468288873332889614898637 3550608327499833605586989)
                      ·
                        rfl

theorem cell23_6914785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_6914785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914785 prefixEnd_6914785 := by exact prefixLift 6914785
  have htrace : WordTrace (prefixWord ++ tailWord_6914785) baseStart_6914785 baseEnd_6914785 := by
    simpa [prefixWord, tailWord_6914785, baseEnd_6914785] using wordTrace_append hprefix tailTrace_6914785
  have hstable : (prefixWord ++ tailWord_6914785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914785).length < 2 ^ (prefixWord ++ tailWord_6914785).sum := by decide
  have hdescent : baseEnd_6914785 < baseStart_6914785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914798 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_6914798 : Nat := 118140960795 + 6914798 * 2 ^ 59
def prefixEnd_6914798 : Nat := 4983230072969 + 3 ^ 40 * 6914798 * 2
def baseEnd_6914798 : Nat := 3550615002748342054724429

theorem tailTrace_6914798 : CollatzResearch.WordTrace tailWord_6914798 prefixEnd_6914798 3550615002748342054724429 := by
  unfold tailWord_6914798
  simp only [CollatzResearch.WordTrace]
  refine ⟨31525425300359409290375131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168135601601916849548667365 31525425300359409290375131)
  ·
    refine ⟨47288137950539113935562697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31525425300359409290375131 47288137950539113935562697)
    ·
      refine ⟨35466103462904335451672023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47288137950539113935562697 35466103462904335451672023)
      ·
        refine ⟨53199155194356503177508035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35466103462904335451672023 53199155194356503177508035)
        ·
          refine ⟨79798732791534754766262053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53199155194356503177508035 79798732791534754766262053)
          ·
            refine ⟨14962262398412766518674135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79798732791534754766262053 14962262398412766518674135)
            ·
              refine ⟨22443393597619149778011203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14962262398412766518674135 22443393597619149778011203)
              ·
                refine ⟨33665090396428724667016805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22443393597619149778011203 33665090396428724667016805)
                ·
                  refine ⟨6312204449330385875065651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33665090396428724667016805 6312204449330385875065651)
                  ·
                    refine ⟨9468306673995578812598477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6312204449330385875065651 9468306673995578812598477)
                    ·
                      refine ⟨3550615002748342054724429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9468306673995578812598477 3550615002748342054724429)
                      ·
                        rfl

theorem cell23_6914798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_6914798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914798 prefixEnd_6914798 := by exact prefixLift 6914798
  have htrace : WordTrace (prefixWord ++ tailWord_6914798) baseStart_6914798 baseEnd_6914798 := by
    simpa [prefixWord, tailWord_6914798, baseEnd_6914798] using wordTrace_append hprefix tailTrace_6914798
  have hstable : (prefixWord ++ tailWord_6914798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914798).length < 2 ^ (prefixWord ++ tailWord_6914798).sum := by decide
  have hdescent : baseEnd_6914798 < baseStart_6914798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914908 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_6914908 : Nat := 118140960795 + 6914908 * 2 ^ 59
def prefixEnd_6914908 : Nat := 4983230072969 + 3 ^ 40 * 6914908 * 2
def baseEnd_6914908 : Nat := 1183557161873445541449641

theorem tailTrace_6914908 : CollatzResearch.WordTrace tailWord_6914908 prefixEnd_6914908 1183557161873445541449641 := by
  unfold tailWord_6914908
  simp only [CollatzResearch.WordTrace]
  refine ⟨126103707216238381554752689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168138276288317842073003585 126103707216238381554752689)
  ·
    refine ⟨94577780412178786166064517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126103707216238381554752689 94577780412178786166064517)
    ·
      refine ⟨17733333827283522406137097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94577780412178786166064517 17733333827283522406137097)
      ·
        refine ⟨13300000370462641804602823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17733333827283522406137097 13300000370462641804602823)
        ·
          refine ⟨19950000555693962706904235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13300000370462641804602823 19950000555693962706904235)
          ·
            refine ⟨29925000833540944060356353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19950000555693962706904235 29925000833540944060356353)
            ·
              refine ⟨22443750625155708045267265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29925000833540944060356353 22443750625155708045267265)
              ·
                refine ⟨16832812968866781033950449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22443750625155708045267265 16832812968866781033950449)
                ·
                  refine ⟨12624609726650085775462837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16832812968866781033950449 12624609726650085775462837)
                  ·
                    refine ⟨1183557161873445541449641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12624609726650085775462837 1183557161873445541449641)
                    ·
                      rfl

theorem cell23_6914908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_6914908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914908 prefixEnd_6914908 := by exact prefixLift 6914908
  have htrace : WordTrace (prefixWord ++ tailWord_6914908) baseStart_6914908 baseEnd_6914908 := by
    simpa [prefixWord, tailWord_6914908, baseEnd_6914908] using wordTrace_append hprefix tailTrace_6914908
  have hstable : (prefixWord ++ tailWord_6914908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914908).length < 2 ^ (prefixWord ++ tailWord_6914908).sum := by decide
  have hdescent : baseEnd_6914908 < baseStart_6914908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914911 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 4]
def baseStart_6914911 : Nat := 118140960795 + 6914911 * 2 ^ 59
def prefixEnd_6914911 : Nat := 4983230072969 + 3 ^ 40 * 6914911 * 2
def baseEnd_6914911 : Nat := 3550673026062300112611409

theorem tailTrace_6914911 : CollatzResearch.WordTrace tailWord_6914911 prefixEnd_6914911 3550673026062300112611409 := by
  unfold tailWord_6914911
  simp only [CollatzResearch.WordTrace]
  refine ⟨252207523851465894621864587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168138349234310596414576391 252207523851465894621864587)
  ·
    refine ⟨378311285777198841932796881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252207523851465894621864587 378311285777198841932796881)
    ·
      refine ⟨283733464332899131449597661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378311285777198841932796881 283733464332899131449597661)
      ·
        refine ⟨106400049124837174293599123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283733464332899131449597661 106400049124837174293599123)
        ·
          refine ⟨159600073687255761440398685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106400049124837174293599123 159600073687255761440398685)
          ·
            refine ⟨59850027632720910540149507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159600073687255761440398685 59850027632720910540149507)
            ·
              refine ⟨89775041449081365810224261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59850027632720910540149507 89775041449081365810224261)
              ·
                refine ⟨16832820271702756089417049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89775041449081365810224261 16832820271702756089417049)
                ·
                  refine ⟨12624615203777067067062787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16832820271702756089417049 12624615203777067067062787)
                  ·
                    refine ⟨18936922805665600600594181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12624615203777067067062787 18936922805665600600594181)
                    ·
                      refine ⟨3550673026062300112611409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18936922805665600600594181 3550673026062300112611409)
                      ·
                        rfl

theorem cell23_6914911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_6914911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914911 prefixEnd_6914911 := by exact prefixLift 6914911
  have htrace : WordTrace (prefixWord ++ tailWord_6914911) baseStart_6914911 baseEnd_6914911 := by
    simpa [prefixWord, tailWord_6914911, baseEnd_6914911] using wordTrace_append hprefix tailTrace_6914911
  have hstable : (prefixWord ++ tailWord_6914911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914911).length < 2 ^ (prefixWord ++ tailWord_6914911).sum := by decide
  have hdescent : baseEnd_6914911 < baseStart_6914911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914931 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 3]
def baseStart_6914931 : Nat := 118140960795 + 6914931 * 2 ^ 59
def prefixEnd_6914931 : Nat := 4983230072969 + 3 ^ 40 * 6914931 * 2
def baseEnd_6914931 : Nat := 3550683295675390034361317

theorem tailTrace_6914931 : CollatzResearch.WordTrace tailWord_6914931 prefixEnd_6914931 3550683295675390034361317 := by
  unfold tailWord_6914931
  simp only [CollatzResearch.WordTrace]
  refine ⟨252208253311393438037592647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168138835540928958691728431 252208253311393438037592647)
  ·
    refine ⟨378312379967090157056388971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252208253311393438037592647 378312379967090157056388971)
    ·
      refine ⟨567468569950635235584583457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378312379967090157056388971 567468569950635235584583457)
      ·
        refine ⟨425601427462976426688437593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567468569950635235584583457 425601427462976426688437593)
        ·
          refine ⟨319201070597232320016328195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425601427462976426688437593 319201070597232320016328195)
          ·
            refine ⟨478801605895848480024492293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319201070597232320016328195 478801605895848480024492293)
            ·
              refine ⟨89775301105471590004592305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 478801605895848480024492293 89775301105471590004592305)
              ·
                refine ⟨67331475829103692503444229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89775301105471590004592305 67331475829103692503444229)
                ·
                  refine ⟨12624651717956942344395793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67331475829103692503444229 12624651717956942344395793)
                  ·
                    refine ⟨9468488788467706758296845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12624651717956942344395793 9468488788467706758296845)
                    ·
                      refine ⟨3550683295675390034361317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9468488788467706758296845 3550683295675390034361317)
                      ·
                        rfl

theorem cell23_6914931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 3].length) (baseStart_6914931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914931 prefixEnd_6914931 := by exact prefixLift 6914931
  have htrace : WordTrace (prefixWord ++ tailWord_6914931) baseStart_6914931 baseEnd_6914931 := by
    simpa [prefixWord, tailWord_6914931, baseEnd_6914931] using wordTrace_append hprefix tailTrace_6914931
  have hstable : (prefixWord ++ tailWord_6914931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914931).length < 2 ^ (prefixWord ++ tailWord_6914931).sum := by decide
  have hdescent : baseEnd_6914931 < baseStart_6914931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914942 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6914942 : Nat := 118140960795 + 6914942 * 2 ^ 59
def prefixEnd_6914942 : Nat := 4983230072969 + 3 ^ 40 * 6914942 * 2
def baseEnd_6914942 : Nat := 1183562981320863163774589

theorem tailTrace_6914942 : CollatzResearch.WordTrace tailWord_6914942 prefixEnd_6914942 1183562981320863163774589 := by
  unfold tailWord_6914942
  simp only [CollatzResearch.WordTrace]
  refine ⟨31526081814294198364530385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168139103009569057944162053 31526081814294198364530385)
  ·
    refine ⟨23644561360720648773397789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31526081814294198364530385 23644561360720648773397789)
    ·
      refine ⟨8866710510270243290024171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23644561360720648773397789 8866710510270243290024171)
      ·
        refine ⟨13300065765405364935036257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8866710510270243290024171 13300065765405364935036257)
        ·
          refine ⟨9975049324054023701277193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13300065765405364935036257 9975049324054023701277193)
          ·
            refine ⟨7481286993040517775957895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9975049324054023701277193 7481286993040517775957895)
            ·
              refine ⟨11221930489560776663936843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7481286993040517775957895 11221930489560776663936843)
              ·
                refine ⟨16832895734341164995905265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11221930489560776663936843 16832895734341164995905265)
                ·
                  refine ⟨12624671800755873746928949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16832895734341164995905265 12624671800755873746928949)
                  ·
                    refine ⟨1183562981320863163774589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12624671800755873746928949 1183562981320863163774589)
                    ·
                      rfl

theorem cell23_6914942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6914942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914942 prefixEnd_6914942 := by exact prefixLift 6914942
  have htrace : WordTrace (prefixWord ++ tailWord_6914942) baseStart_6914942 baseEnd_6914942 := by
    simpa [prefixWord, tailWord_6914942, baseEnd_6914942] using wordTrace_append hprefix tailTrace_6914942
  have hstable : (prefixWord ++ tailWord_6914942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914942).length < 2 ^ (prefixWord ++ tailWord_6914942).sum := by decide
  have hdescent : baseEnd_6914942 < baseStart_6914942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6914988 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 4, 3, 2]
def baseStart_6914988 : Nat := 118140960795 + 6914988 * 2 ^ 59
def prefixEnd_6914988 : Nat := 4983230072969 + 3 ^ 40 * 6914988 * 2
def baseEnd_6914988 : Nat := 3550712564072696311348555

theorem tailTrace_6914988 : CollatzResearch.WordTrace tailWord_6914988 prefixEnd_6914988 3550712564072696311348555 := by
  unfold tailWord_6914988
  simp only [CollatzResearch.WordTrace]
  refine ⟨126105166136093468386208809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168140221514791291181611745 126105166136093468386208809)
  ·
    refine ⟨94578874602070101289656607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126105166136093468386208809 94578874602070101289656607)
    ·
      refine ⟨141868311903105151934484911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94578874602070101289656607 141868311903105151934484911)
      ·
        refine ⟨212802467854657727901727367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141868311903105151934484911 212802467854657727901727367)
        ·
          refine ⟨319203701781986591852591051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212802467854657727901727367 319203701781986591852591051)
          ·
            refine ⟨478805552672979887778886577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319203701781986591852591051 478805552672979887778886577)
            ·
              refine ⟨359104164504734915834164933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478805552672979887778886577 359104164504734915834164933)
              ·
                refine ⟨67332030844637796718905925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359104164504734915834164933 67332030844637796718905925)
                ·
                  refine ⟨12624755783369586884794861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67332030844637796718905925 12624755783369586884794861)
                  ·
                    refine ⟨4734283418763595081798073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12624755783369586884794861 4734283418763595081798073)
                    ·
                      refine ⟨3550712564072696311348555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734283418763595081798073 3550712564072696311348555)
                      ·
                        rfl

theorem cell23_6914988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 3, 2].length) (baseStart_6914988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6914988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6914988 prefixEnd_6914988 := by exact prefixLift 6914988
  have htrace : WordTrace (prefixWord ++ tailWord_6914988) baseStart_6914988 baseEnd_6914988 := by
    simpa [prefixWord, tailWord_6914988, baseEnd_6914988] using wordTrace_append hprefix tailTrace_6914988
  have hstable : (prefixWord ++ tailWord_6914988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6914988).length < 2 ^ (prefixWord ++ tailWord_6914988).sum := by decide
  have hdescent : baseEnd_6914988 < baseStart_6914988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6914988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915029 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 3, 1, 3]
def baseStart_6915029 : Nat := 118140960795 + 6915029 * 2 ^ 59
def prefixEnd_6915029 : Nat := 4983230072969 + 3 ^ 40 * 6915029 * 2
def baseEnd_6915029 : Nat := 3550733616779530650935867

theorem tailTrace_6915029 : CollatzResearch.WordTrace tailWord_6915029 prefixEnd_6915029 3550733616779530650935867 := by
  unfold tailWord_6915029
  simp only [CollatzResearch.WordTrace]
  refine ⟨252211827665038400774660141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168141218443358933849773427 252211827665038400774660141)
  ·
    refine ⟨94579435374389400290497553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252211827665038400774660141 94579435374389400290497553)
    ·
      refine ⟨70934576530792050217873165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94579435374389400290497553 70934576530792050217873165)
      ·
        refine ⟨26600466199047018831702437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70934576530792050217873165 26600466199047018831702437)
        ·
          refine ⟨4987587412321316030944207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26600466199047018831702437 4987587412321316030944207)
          ·
            refine ⟨7481381118481974046416311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987587412321316030944207 7481381118481974046416311)
            ·
              refine ⟨11222071677722961069624467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7481381118481974046416311 11222071677722961069624467)
              ·
                refine ⟨16833107516584441604436701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11222071677722961069624467 16833107516584441604436701)
                ·
                  refine ⟨6312415318719165601663763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16833107516584441604436701 6312415318719165601663763)
                  ·
                    refine ⟨9468622978078748402495645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6312415318719165601663763 9468622978078748402495645)
                    ·
                      refine ⟨3550733616779530650935867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9468622978078748402495645 3550733616779530650935867)
                      ·
                        rfl

theorem cell23_6915029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_6915029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915029 prefixEnd_6915029 := by exact prefixLift 6915029
  have htrace : WordTrace (prefixWord ++ tailWord_6915029) baseStart_6915029 baseEnd_6915029 := by
    simpa [prefixWord, tailWord_6915029, baseEnd_6915029] using wordTrace_append hprefix tailTrace_6915029
  have hstable : (prefixWord ++ tailWord_6915029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915029).length < 2 ^ (prefixWord ++ tailWord_6915029).sum := by decide
  have hdescent : baseEnd_6915029 < baseStart_6915029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915031 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_6915031 : Nat := 118140960795 + 6915031 * 2 ^ 59
def prefixEnd_6915031 : Nat := 4983230072969 + 3 ^ 40 * 6915031 * 2
def baseEnd_6915031 : Nat := 3550734643740839643110857

theorem tailTrace_6915031 : CollatzResearch.WordTrace tailWord_6915031 prefixEnd_6915031 3550734643740839643110857 := by
  unfold tailWord_6915031
  simp only [CollatzResearch.WordTrace]
  refine ⟨252211900611031155116232947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168141267074020770077488631 252211900611031155116232947)
  ·
    refine ⟨378317850916546732674349421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252211900611031155116232947 378317850916546732674349421)
    ·
      refine ⟨141869194093705024752881033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378317850916546732674349421 141869194093705024752881033)
      ·
        refine ⟨106401895570278768564660775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141869194093705024752881033 106401895570278768564660775)
        ·
          refine ⟨159602843355418152846991163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106401895570278768564660775 159602843355418152846991163)
          ·
            refine ⟨239404265033127229270486745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159602843355418152846991163 239404265033127229270486745)
            ·
              refine ⟨179553198774845421952865059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239404265033127229270486745 179553198774845421952865059)
              ·
                refine ⟨269329798162268132929297589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179553198774845421952865059 269329798162268132929297589)
                ·
                  refine ⟨25249668577712637462121649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269329798162268132929297589 25249668577712637462121649)
                  ·
                    refine ⟨18937251433284478096591237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25249668577712637462121649 18937251433284478096591237)
                    ·
                      refine ⟨3550734643740839643110857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18937251433284478096591237 3550734643740839643110857)
                      ·
                        rfl

theorem cell23_6915031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_6915031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915031 prefixEnd_6915031 := by exact prefixLift 6915031
  have htrace : WordTrace (prefixWord ++ tailWord_6915031) baseStart_6915031 baseEnd_6915031 := by
    simpa [prefixWord, tailWord_6915031, baseEnd_6915031] using wordTrace_append hprefix tailTrace_6915031
  have hstable : (prefixWord ++ tailWord_6915031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915031).length < 2 ^ (prefixWord ++ tailWord_6915031).sum := by decide
  have hdescent : baseEnd_6915031 < baseStart_6915031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915055 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 1, 2, 3]
def baseStart_6915055 : Nat := 118140960795 + 6915055 * 2 ^ 59
def prefixEnd_6915055 : Nat := 4983230072969 + 3 ^ 40 * 6915055 * 2
def baseEnd_6915055 : Nat := 3550746967276547549210747

theorem tailTrace_6915055 : CollatzResearch.WordTrace tailWord_6915055 prefixEnd_6915055 3550746967276547549210747 := by
  unfold tailWord_6915055
  simp only [CollatzResearch.WordTrace]
  refine ⟨252212775962944207215106619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168141850641962804810071079 252212775962944207215106619)
  ·
    refine ⟨378319163944416310822659929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252212775962944207215106619 378319163944416310822659929)
    ·
      refine ⟨283739372958312233116994947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378319163944416310822659929 283739372958312233116994947)
      ·
        refine ⟨425609059437468349675492421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283739372958312233116994947 425609059437468349675492421)
        ·
          refine ⟨79801698644525315564154829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425609059437468349675492421 79801698644525315564154829)
          ·
            refine ⟨29925636991696993336558061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79801698644525315564154829 29925636991696993336558061)
            ·
              refine ⟨11222113871886372501209273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29925636991696993336558061 11222113871886372501209273)
              ·
                refine ⟨8416585403914779375906955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11222113871886372501209273 8416585403914779375906955)
                ·
                  refine ⟨12624878105872169063860433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8416585403914779375906955 12624878105872169063860433)
                  ·
                    refine ⟨9468658579404126797895325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12624878105872169063860433 9468658579404126797895325)
                    ·
                      refine ⟨3550746967276547549210747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9468658579404126797895325 3550746967276547549210747)
                      ·
                        rfl

theorem cell23_6915055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 2, 3].length) (baseStart_6915055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915055 prefixEnd_6915055 := by exact prefixLift 6915055
  have htrace : WordTrace (prefixWord ++ tailWord_6915055) baseStart_6915055 baseEnd_6915055 := by
    simpa [prefixWord, tailWord_6915055, baseEnd_6915055] using wordTrace_append hprefix tailTrace_6915055
  have hstable : (prefixWord ++ tailWord_6915055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915055).length < 2 ^ (prefixWord ++ tailWord_6915055).sum := by decide
  have hdescent : baseEnd_6915055 < baseStart_6915055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915068 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_6915068 : Nat := 118140960795 + 6915068 * 2 ^ 59
def prefixEnd_6915068 : Nat := 4983230072969 + 3 ^ 40 * 6915068 * 2
def baseEnd_6915068 : Nat := 3550753642525055998348187

theorem tailTrace_6915068 : CollatzResearch.WordTrace tailWord_6915068 prefixEnd_6915068 3550753642525055998348187 := by
  unfold tailWord_6915068
  simp only [CollatzResearch.WordTrace]
  refine ⟨126106625055948555217664929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168142166741264740290219905 126106625055948555217664929)
  ·
    refine ⟨94579968791961416413248697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126106625055948555217664929 94579968791961416413248697)
    ·
      refine ⟨70934976593971062309936523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94579968791961416413248697 70934976593971062309936523)
      ·
        refine ⟨106402464890956593464904785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70934976593971062309936523 106402464890956593464904785)
        ·
          refine ⟨79801848668217445098678589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106402464890956593464904785 79801848668217445098678589)
          ·
            refine ⟨29925693250581541912004471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79801848668217445098678589 29925693250581541912004471)
            ·
              refine ⟨44888539875872312868006707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29925693250581541912004471 44888539875872312868006707)
              ·
                refine ⟨67332809813808469302010061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44888539875872312868006707 67332809813808469302010061)
                ·
                  refine ⟨25249803680178175988253773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67332809813808469302010061 25249803680178175988253773)
                  ·
                    refine ⟨9468676380066815995595165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25249803680178175988253773 9468676380066815995595165)
                    ·
                      refine ⟨3550753642525055998348187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9468676380066815995595165 3550753642525055998348187)
                      ·
                        rfl

theorem cell23_6915068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_6915068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915068 prefixEnd_6915068 := by exact prefixLift 6915068
  have htrace : WordTrace (prefixWord ++ tailWord_6915068) baseStart_6915068 baseEnd_6915068 := by
    simpa [prefixWord, tailWord_6915068, baseEnd_6915068] using wordTrace_append hprefix tailTrace_6915068
  have hstable : (prefixWord ++ tailWord_6915068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915068).length < 2 ^ (prefixWord ++ tailWord_6915068).sum := by decide
  have hdescent : baseEnd_6915068 < baseStart_6915068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915081 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_6915081 : Nat := 118140960795 + 6915081 * 2 ^ 59
def prefixEnd_6915081 : Nat := 4983230072969 + 3 ^ 40 * 6915081 * 2
def baseEnd_6915081 : Nat := 3550760317773564447485627

theorem tailTrace_6915081 : CollatzResearch.WordTrace tailWord_6915081 prefixEnd_6915081 3550760317773564447485627 := by
  unfold tailWord_6915081
  simp only [CollatzResearch.WordTrace]
  refine ⟨252213724260850013655553097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168142482840566675770368731 252213724260850013655553097)
  ·
    refine ⟨189160293195637510241664823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252213724260850013655553097 189160293195637510241664823)
    ·
      refine ⟨283740439793456265362497235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189160293195637510241664823 283740439793456265362497235)
      ·
        refine ⟨425610659690184398043745853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283740439793456265362497235 425610659690184398043745853)
        ·
          refine ⟨159603997383819149266404695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425610659690184398043745853 159603997383819149266404695)
          ·
            refine ⟨239405996075728723899607043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159603997383819149266404695 239405996075728723899607043)
            ·
              refine ⟨359108994113593085849410565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239405996075728723899607043 359108994113593085849410565)
              ·
                refine ⟨67332936396298703596764481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359108994113593085849410565 67332936396298703596764481)
                ·
                  refine ⟨50499702297224027697573361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67332936396298703596764481 50499702297224027697573361)
                  ·
                    refine ⟨37874776722918020773180021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50499702297224027697573361 37874776722918020773180021)
                    ·
                      refine ⟨3550760317773564447485627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37874776722918020773180021 3550760317773564447485627)
                      ·
                        rfl

theorem cell23_6915081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_6915081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915081 prefixEnd_6915081 := by exact prefixLift 6915081
  have htrace : WordTrace (prefixWord ++ tailWord_6915081) baseStart_6915081 baseEnd_6915081 := by
    simpa [prefixWord, tailWord_6915081, baseEnd_6915081] using wordTrace_append hprefix tailTrace_6915081
  have hstable : (prefixWord ++ tailWord_6915081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915081).length < 2 ^ (prefixWord ++ tailWord_6915081).sum := by decide
  have hdescent : baseEnd_6915081 < baseStart_6915081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915086 : List Nat := [4, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2]
def baseStart_6915086 : Nat := 118140960795 + 6915086 * 2 ^ 59
def prefixEnd_6915086 : Nat := 4983230072969 + 3 ^ 40 * 6915086 * 2
def baseEnd_6915086 : Nat := 3550762885176836927923105

theorem tailTrace_6915086 : CollatzResearch.WordTrace tailWord_6915086 prefixEnd_6915086 3550762885176836927923105 := by
  unfold tailWord_6915086
  simp only [CollatzResearch.WordTrace]
  refine ⟨31526738328228987438685639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168142604417221266339656741 31526738328228987438685639)
  ·
    refine ⟨47290107492343481158028459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31526738328228987438685639 47290107492343481158028459)
    ·
      refine ⟨70935161238515221737042689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47290107492343481158028459 70935161238515221737042689)
      ·
        refine ⟨53201370928886416302782017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70935161238515221737042689 53201370928886416302782017)
        ·
          refine ⟨39901028196664812227086513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53201370928886416302782017 39901028196664812227086513)
          ·
            refine ⟨29925771147498609170314885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39901028196664812227086513 29925771147498609170314885)
            ·
              refine ⟨5611082090155989219434041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29925771147498609170314885 5611082090155989219434041)
              ·
                refine ⟨4208311567616991914575531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5611082090155989219434041 4208311567616991914575531)
                ·
                  refine ⟨6312467351425487871863297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208311567616991914575531 6312467351425487871863297)
                  ·
                    refine ⟨4734350513569115903897473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6312467351425487871863297 4734350513569115903897473)
                    ·
                      refine ⟨3550762885176836927923105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734350513569115903897473 3550762885176836927923105)
                      ·
                        rfl

theorem cell23_6915086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_6915086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915086 prefixEnd_6915086 := by exact prefixLift 6915086
  have htrace : WordTrace (prefixWord ++ tailWord_6915086) baseStart_6915086 baseEnd_6915086 := by
    simpa [prefixWord, tailWord_6915086, baseEnd_6915086] using wordTrace_append hprefix tailTrace_6915086
  have hstable : (prefixWord ++ tailWord_6915086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915086).length < 2 ^ (prefixWord ++ tailWord_6915086).sum := by decide
  have hdescent : baseEnd_6915086 < baseStart_6915086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915118 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_6915118 : Nat := 118140960795 + 6915118 * 2 ^ 59
def prefixEnd_6915118 : Nat := 4983230072969 + 3 ^ 40 * 6915118 * 2
def baseEnd_6915118 : Nat := 1183593105519260267574319

theorem tailTrace_6915118 : CollatzResearch.WordTrace tailWord_6915118 prefixEnd_6915118 1183593105519260267574319 := by
  unfold tailWord_6915118
  simp only [CollatzResearch.WordTrace]
  refine ⟨31526884220214496121831251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168143382507810645983100005 31526884220214496121831251)
  ·
    refine ⟨47290326330321744182746877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31526884220214496121831251 47290326330321744182746877)
    ·
      refine ⟨17733872373870654068530079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47290326330321744182746877 17733872373870654068530079)
      ·
        refine ⟨26600808560805981102795119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17733872373870654068530079 26600808560805981102795119)
        ·
          refine ⟨39901212841208971654192679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26600808560805981102795119 39901212841208971654192679)
          ·
            refine ⟨59851819261813457481289019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39901212841208971654192679 59851819261813457481289019)
            ·
              refine ⟨89777728892720186221933529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59851819261813457481289019 89777728892720186221933529)
              ·
                refine ⟨67333296669540139666450147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89777728892720186221933529 67333296669540139666450147)
                ·
                  refine ⟨100999945004310209499675221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67333296669540139666450147 100999945004310209499675221)
                  ·
                    refine ⟨1183593105519260267574319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100999945004310209499675221 1183593105519260267574319)
                    ·
                      rfl

theorem cell23_6915118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_6915118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915118 prefixEnd_6915118 := by exact prefixLift 6915118
  have htrace : WordTrace (prefixWord ++ tailWord_6915118) baseStart_6915118 baseEnd_6915118 := by
    simpa [prefixWord, tailWord_6915118, baseEnd_6915118] using wordTrace_append hprefix tailTrace_6915118
  have hstable : (prefixWord ++ tailWord_6915118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915118).length < 2 ^ (prefixWord ++ tailWord_6915118).sum := by decide
  have hdescent : baseEnd_6915118 < baseStart_6915118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915129 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 1, 3, 2]
def baseStart_6915129 : Nat := 118140960795 + 6915129 * 2 ^ 59
def prefixEnd_6915129 : Nat := 4983230072969 + 3 ^ 40 * 6915129 * 2
def baseEnd_6915129 : Nat := 3550784964844980259685407

theorem tailTrace_6915129 : CollatzResearch.WordTrace tailWord_6915129 prefixEnd_6915129 3550784964844980259685407 := by
  unfold tailWord_6915129
  simp only [CollatzResearch.WordTrace]
  refine ⟨252215474964676117853300441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168143649976450745235533627 252215474964676117853300441)
  ·
    refine ⟨189161606223507088389975331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252215474964676117853300441 189161606223507088389975331)
    ·
      refine ⟨283742409335260632584962997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189161606223507088389975331 283742409335260632584962997)
      ·
        refine ⟨26600850875180684304840281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283742409335260632584962997 26600850875180684304840281)
        ·
          refine ⟨19950638156385513228630211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26600850875180684304840281 19950638156385513228630211)
          ·
            refine ⟨29925957234578269842945317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19950638156385513228630211 29925957234578269842945317)
            ·
              refine ⟨5611116981483425595552247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29925957234578269842945317 5611116981483425595552247)
              ·
                refine ⟨8416675472225138393328371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611116981483425595552247 8416675472225138393328371)
                ·
                  refine ⟨12625013208337707589992557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8416675472225138393328371 12625013208337707589992557)
                  ·
                    refine ⟨4734379953126640346247209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12625013208337707589992557 4734379953126640346247209)
                    ·
                      refine ⟨3550784964844980259685407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734379953126640346247209 3550784964844980259685407)
                      ·
                        rfl

theorem cell23_6915129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_6915129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915129 prefixEnd_6915129 := by exact prefixLift 6915129
  have htrace : WordTrace (prefixWord ++ tailWord_6915129) baseStart_6915129 baseEnd_6915129 := by
    simpa [prefixWord, tailWord_6915129, baseEnd_6915129] using wordTrace_append hprefix tailTrace_6915129
  have hstable : (prefixWord ++ tailWord_6915129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915129).length < 2 ^ (prefixWord ++ tailWord_6915129).sum := by decide
  have hdescent : baseEnd_6915129 < baseStart_6915129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915151 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_6915151 : Nat := 118140960795 + 6915151 * 2 ^ 59
def prefixEnd_6915151 : Nat := 4983230072969 + 3 ^ 40 * 6915151 * 2
def baseEnd_6915151 : Nat := 3550796261419379173610305

theorem tailTrace_6915151 : CollatzResearch.WordTrace tailWord_6915151 prefixEnd_6915151 3550796261419379173610305 := by
  unfold tailWord_6915151
  simp only [CollatzResearch.WordTrace]
  refine ⟨252216277370596415610601307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168144184913730943740400871 252216277370596415610601307)
  ·
    refine ⟨378324416055894623415901961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252216277370596415610601307 378324416055894623415901961)
    ·
      refine ⟨283743312041920967561926471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378324416055894623415901961 283743312041920967561926471)
      ·
        refine ⟨425614968062881451342889707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283743312041920967561926471 425614968062881451342889707)
        ·
          refine ⟨638422452094322177014334561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425614968062881451342889707 638422452094322177014334561)
          ·
            refine ⟨478816839070741632760750921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638422452094322177014334561 478816839070741632760750921)
            ·
              refine ⟨359112629303056224570563191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478816839070741632760750921 359112629303056224570563191)
              ·
                refine ⟨538668943954584336855844787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359112629303056224570563191 538668943954584336855844787)
                ·
                  refine ⟨808003415931876505283767181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538668943954584336855844787 808003415931876505283767181)
                  ·
                    refine ⟨303001280974453689481412693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 808003415931876505283767181 303001280974453689481412693)
                    ·
                      refine ⟨3550796261419379173610305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 303001280974453689481412693 3550796261419379173610305)
                      ·
                        rfl

theorem cell23_6915151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_6915151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915151 prefixEnd_6915151 := by exact prefixLift 6915151
  have htrace : WordTrace (prefixWord ++ tailWord_6915151) baseStart_6915151 baseEnd_6915151 := by
    simpa [prefixWord, tailWord_6915151, baseEnd_6915151] using wordTrace_append hprefix tailTrace_6915151
  have hstable : (prefixWord ++ tailWord_6915151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915151).length < 2 ^ (prefixWord ++ tailWord_6915151).sum := by decide
  have hdescent : baseEnd_6915151 < baseStart_6915151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915182 : List Nat := [4, 1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_6915182 : Nat := 118140960795 + 6915182 * 2 ^ 59
def prefixEnd_6915182 : Nat := 4983230072969 + 3 ^ 40 * 6915182 * 2
def baseEnd_6915182 : Nat := 394534686591074283591407

theorem tailTrace_6915182 : CollatzResearch.WordTrace tailWord_6915182 prefixEnd_6915182 394534686591074283591407 := by
  unfold tailWord_6915182
  simp only [CollatzResearch.WordTrace]
  refine ⟨31527176004185513488122475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168144938688989405269986533 31527176004185513488122475)
  ·
    refine ⟨47290764006278270232183713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31527176004185513488122475 47290764006278270232183713)
    ·
      refine ⟨35468073004708702674137785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47290764006278270232183713 35468073004708702674137785)
      ·
        refine ⟨26601054753531527005603339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35468073004708702674137785 26601054753531527005603339)
        ·
          refine ⟨39901582130297290508405009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26601054753531527005603339 39901582130297290508405009)
          ·
            refine ⟨29926186597722967881303757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39901582130297290508405009 29926186597722967881303757)
            ·
              refine ⟨11222319974146112955488909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29926186597722967881303757 11222319974146112955488909)
              ·
                refine ⟨4208369990304792358308341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11222319974146112955488909 4208369990304792358308341)
                ·
                  refine ⟨394534686591074283591407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4208369990304792358308341 394534686591074283591407)
                  ·
                    rfl

theorem cell23_6915182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_6915182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915182 prefixEnd_6915182 := by exact prefixLift 6915182
  have htrace : WordTrace (prefixWord ++ tailWord_6915182) baseStart_6915182 baseEnd_6915182 := by
    simpa [prefixWord, tailWord_6915182, baseEnd_6915182] using wordTrace_append hprefix tailTrace_6915182
  have hstable : (prefixWord ++ tailWord_6915182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915182).length < 2 ^ (prefixWord ++ tailWord_6915182).sum := by decide
  have hdescent : baseEnd_6915182 < baseStart_6915182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915205 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 5]
def baseStart_6915205 : Nat := 118140960795 + 6915205 * 2 ^ 59
def prefixEnd_6915205 : Nat := 4983230072969 + 3 ^ 40 * 6915205 * 2
def baseEnd_6915205 : Nat := 3550823989374721962335057

theorem tailTrace_6915205 : CollatzResearch.WordTrace tailWord_6915205 prefixEnd_6915205 3550823989374721962335057 := by
  unfold tailWord_6915205
  simp only [CollatzResearch.WordTrace]
  refine ⟨252218246912400782833067069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168145497941600521888711379 252218246912400782833067069)
  ·
    refine ⟨94581842592150293562400151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252218246912400782833067069 94581842592150293562400151)
    ·
      refine ⟨141872763888225440343600227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94581842592150293562400151 141872763888225440343600227)
      ·
        refine ⟨212809145832338160515400341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141872763888225440343600227 212809145832338160515400341)
        ·
          refine ⟨9975428710890851274159391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 212809145832338160515400341 9975428710890851274159391)
          ·
            refine ⟨14963143066336276911239087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9975428710890851274159391 14963143066336276911239087)
            ·
              refine ⟨22444714599504415366858631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14963143066336276911239087 22444714599504415366858631)
              ·
                refine ⟨33667071899256623050287947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22444714599504415366858631 33667071899256623050287947)
                ·
                  refine ⟨50500607848884934575431921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33667071899256623050287947 50500607848884934575431921)
                  ·
                    refine ⟨37875455886663700931573941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50500607848884934575431921 37875455886663700931573941)
                    ·
                      refine ⟨3550823989374721962335057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37875455886663700931573941 3550823989374721962335057)
                      ·
                        rfl

theorem cell23_6915205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_6915205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915205 prefixEnd_6915205 := by exact prefixLift 6915205
  have htrace : WordTrace (prefixWord ++ tailWord_6915205) baseStart_6915205 baseEnd_6915205 := by
    simpa [prefixWord, tailWord_6915205, baseEnd_6915205] using wordTrace_append hprefix tailTrace_6915205
  have hstable : (prefixWord ++ tailWord_6915205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915205).length < 2 ^ (prefixWord ++ tailWord_6915205).sum := by decide
  have hdescent : baseEnd_6915205 < baseStart_6915205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915255 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 6]
def baseStart_6915255 : Nat := 118140960795 + 6915255 * 2 ^ 59
def prefixEnd_6915255 : Nat := 4983230072969 + 3 ^ 40 * 6915255 * 2
def baseEnd_6915255 : Nat := 394538851489716307412203

theorem tailTrace_6915255 : CollatzResearch.WordTrace tailWord_6915255 prefixEnd_6915255 394538851489716307412203 := by
  unfold tailWord_6915255
  simp only [CollatzResearch.WordTrace]
  refine ⟨252220070562219641372387219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168146713708146427581591479 252220070562219641372387219)
  ·
    refine ⟨378330105843329462058580829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252220070562219641372387219 378330105843329462058580829)
    ·
      refine ⟨141873789691248548271967811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378330105843329462058580829 141873789691248548271967811)
      ·
        refine ⟨212810684536872822407951717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141873789691248548271967811 212810684536872822407951717)
        ·
          refine ⟨39902003350663654201490947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212810684536872822407951717 39902003350663654201490947)
          ·
            refine ⟨59853005025995481302236421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39902003350663654201490947 59853005025995481302236421)
            ·
              refine ⟨11222438442374152744169329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59853005025995481302236421 11222438442374152744169329)
              ·
                refine ⟨8416828831780614558126997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11222438442374152744169329 8416828831780614558126997)
                ·
                  refine ⟨394538851489716307412203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8416828831780614558126997 394538851489716307412203)
                  ·
                    rfl

theorem cell23_6915255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 6].length) (baseStart_6915255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915255 prefixEnd_6915255 := by exact prefixLift 6915255
  have htrace : WordTrace (prefixWord ++ tailWord_6915255) baseStart_6915255 baseEnd_6915255 := by
    simpa [prefixWord, tailWord_6915255, baseEnd_6915255] using wordTrace_append hprefix tailTrace_6915255
  have hstable : (prefixWord ++ tailWord_6915255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915255).length < 2 ^ (prefixWord ++ tailWord_6915255).sum := by decide
  have hdescent : baseEnd_6915255 < baseStart_6915255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915258 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_6915258 : Nat := 118140960795 + 6915258 * 2 ^ 59
def prefixEnd_6915258 : Nat := 4983230072969 + 3 ^ 40 * 6915258 * 2
def baseEnd_6915258 : Nat := 3550851203849410254972313

theorem tailTrace_6915258 : CollatzResearch.WordTrace tailWord_6915258 prefixEnd_6915258 3550851203849410254972313 := by
  unfold tailWord_6915258
  simp only [CollatzResearch.WordTrace]
  refine ⟨63055044995302193221186607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168146786654139181923164285 63055044995302193221186607)
  ·
    refine ⟨94582567492953289831779911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63055044995302193221186607 94582567492953289831779911)
    ·
      refine ⟨141873851239429934747669867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94582567492953289831779911 141873851239429934747669867)
      ·
        refine ⟨212810776859144902121504801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141873851239429934747669867 212810776859144902121504801)
        ·
          refine ⟨159608082644358676591128601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212810776859144902121504801 159608082644358676591128601)
          ·
            refine ⟨119706061983269007443346451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159608082644358676591128601 119706061983269007443346451)
            ·
              refine ⟨179559092974903511165019677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119706061983269007443346451 179559092974903511165019677)
              ·
                refine ⟨67334659865588816686882379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179559092974903511165019677 67334659865588816686882379)
                ·
                  refine ⟨101001989798383225030323569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67334659865588816686882379 101001989798383225030323569)
                  ·
                    refine ⟨75751492348787418772742677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101001989798383225030323569 75751492348787418772742677)
                    ·
                      refine ⟨3550851203849410254972313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75751492348787418772742677 3550851203849410254972313)
                      ·
                        rfl

theorem cell23_6915258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_6915258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915258 prefixEnd_6915258 := by exact prefixLift 6915258
  have htrace : WordTrace (prefixWord ++ tailWord_6915258) baseStart_6915258 baseEnd_6915258 := by
    simpa [prefixWord, tailWord_6915258, baseEnd_6915258] using wordTrace_append hprefix tailTrace_6915258
  have hstable : (prefixWord ++ tailWord_6915258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915258).length < 2 ^ (prefixWord ++ tailWord_6915258).sum := by decide
  have hdescent : baseEnd_6915258 < baseStart_6915258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915328 : List Nat := [2, 1, 1, 2, 1, 1, 3, 12]
def baseStart_6915328 : Nat := 118140960795 + 6915328 * 2 ^ 59
def prefixEnd_6915328 : Nat := 4983230072969 + 3 ^ 40 * 6915328 * 2
def baseEnd_6915328 : Nat := 131514338796119443744333

theorem tailTrace_6915328 : CollatzResearch.WordTrace tailWord_6915328 prefixEnd_6915328 131514338796119443744333 := by
  unfold tailWord_6915328
  simp only [CollatzResearch.WordTrace]
  refine ⟨126111366545477587419897319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168148488727303449893196425 126111366545477587419897319)
  ·
    refine ⟨189167049818216381129845979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126111366545477587419897319 189167049818216381129845979)
    ·
      refine ⟨283750574727324571694768969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189167049818216381129845979 283750574727324571694768969)
      ·
        refine ⟨212812931045493428771076727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283750574727324571694768969 212812931045493428771076727)
        ·
          refine ⟨319219396568240143156615091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212812931045493428771076727 319219396568240143156615091)
          ·
            refine ⟨478829094852360214734922637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319219396568240143156615091 478829094852360214734922637)
            ·
              refine ⟨179560910569635080525595989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 478829094852360214734922637 179560910569635080525595989)
              ·
                refine ⟨131514338796119443744333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 179560910569635080525595989 131514338796119443744333)
                ·
                  rfl

theorem cell23_6915328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 12].length) (baseStart_6915328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915328 prefixEnd_6915328 := by exact prefixLift 6915328
  have htrace : WordTrace (prefixWord ++ tailWord_6915328) baseStart_6915328 baseEnd_6915328 := by
    simpa [prefixWord, tailWord_6915328, baseEnd_6915328] using wordTrace_append hprefix tailTrace_6915328
  have hstable : (prefixWord ++ tailWord_6915328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915328).length < 2 ^ (prefixWord ++ tailWord_6915328).sum := by decide
  have hdescent : baseEnd_6915328 < baseStart_6915328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915332 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_6915332 : Nat := 118140960795 + 6915332 * 2 ^ 59
def prefixEnd_6915332 : Nat := 4983230072969 + 3 ^ 40 * 6915332 * 2
def baseEnd_6915332 : Nat := 1183629733805947655148991

theorem tailTrace_6915332 : CollatzResearch.WordTrace tailWord_6915332 prefixEnd_6915332 1183629733805947655148991 := by
  unfold tailWord_6915332
  simp only [CollatzResearch.WordTrace]
  refine ⟨126111439491470341761470125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168148585988627122348626833 126111439491470341761470125)
  ·
    refine ⟨47291789809301378160551297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126111439491470341761470125 47291789809301378160551297)
    ·
      refine ⟨35468842356976033620413473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47291789809301378160551297 35468842356976033620413473)
      ·
        refine ⟨26601631767732025215310105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35468842356976033620413473 26601631767732025215310105)
        ·
          refine ⟨19951223825799018911482579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26601631767732025215310105 19951223825799018911482579)
          ·
            refine ⟨29926835738698528367223869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19951223825799018911482579 29926835738698528367223869)
            ·
              refine ⟨11222563402011948137708951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29926835738698528367223869 11222563402011948137708951)
              ·
                refine ⟨16833845103017922206563427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11222563402011948137708951 16833845103017922206563427)
                ·
                  refine ⟨25250767654526883309845141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16833845103017922206563427 25250767654526883309845141)
                  ·
                    refine ⟨1183629733805947655148991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25250767654526883309845141 1183629733805947655148991)
                    ·
                      rfl

theorem cell23_6915332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_6915332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915332 prefixEnd_6915332 := by exact prefixLift 6915332
  have htrace : WordTrace (prefixWord ++ tailWord_6915332) baseStart_6915332 baseEnd_6915332 := by
    simpa [prefixWord, tailWord_6915332, baseEnd_6915332] using wordTrace_append hprefix tailTrace_6915332
  have hstable : (prefixWord ++ tailWord_6915332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915332).length < 2 ^ (prefixWord ++ tailWord_6915332).sum := by decide
  have hdescent : baseEnd_6915332 < baseStart_6915332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915339 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 3, 2, 2]
def baseStart_6915339 : Nat := 118140960795 + 6915339 * 2 ^ 59
def prefixEnd_6915339 : Nat := 4983230072969 + 3 ^ 40 * 6915339 * 2
def baseEnd_6915339 : Nat := 3550892795782424438059441

theorem tailTrace_6915339 : CollatzResearch.WordTrace tailWord_6915339 prefixEnd_6915339 3550892795782424438059441 := by
  unfold tailWord_6915339
  simp only [CollatzResearch.WordTrace]
  refine ⟨252223134293915323718445071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168148756195943549145630047 252223134293915323718445071)
  ·
    refine ⟨378334701440872985577667607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252223134293915323718445071 378334701440872985577667607)
    ·
      refine ⟨567502052161309478366501411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378334701440872985577667607 567502052161309478366501411)
      ·
        refine ⟨851253078241964217549752117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567502052161309478366501411 851253078241964217549752117)
        ·
          refine ⟨79804976085184145395289261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 851253078241964217549752117 79804976085184145395289261)
          ·
            refine ⟨29926866031944054523233473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79804976085184145395289261 29926866031944054523233473)
            ·
              refine ⟨22445149523958040892425105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29926866031944054523233473 22445149523958040892425105)
              ·
                refine ⟨16833862142968530669318829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22445149523958040892425105 16833862142968530669318829)
                ·
                  refine ⟨6312698303613199000994561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16833862142968530669318829 6312698303613199000994561)
                  ·
                    refine ⟨4734523727709899250745921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6312698303613199000994561 4734523727709899250745921)
                    ·
                      refine ⟨3550892795782424438059441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734523727709899250745921 3550892795782424438059441)
                      ·
                        rfl

theorem cell23_6915339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 2, 2].length) (baseStart_6915339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915339 prefixEnd_6915339 := by exact prefixLift 6915339
  have htrace : WordTrace (prefixWord ++ tailWord_6915339) baseStart_6915339 baseEnd_6915339 := by
    simpa [prefixWord, tailWord_6915339, baseEnd_6915339] using wordTrace_append hprefix tailTrace_6915339
  have hstable : (prefixWord ++ tailWord_6915339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915339).length < 2 ^ (prefixWord ++ tailWord_6915339).sum := by decide
  have hdescent : baseEnd_6915339 < baseStart_6915339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915355 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 3]
def baseStart_6915355 : Nat := 118140960795 + 6915355 * 2 ^ 59
def prefixEnd_6915355 : Nat := 4983230072969 + 3 ^ 40 * 6915355 * 2
def baseEnd_6915355 : Nat := 3550901011472896375459367

theorem tailTrace_6915355 : CollatzResearch.WordTrace tailWord_6915355 prefixEnd_6915355 3550901011472896375459367 := by
  unfold tailWord_6915355
  simp only [CollatzResearch.WordTrace]
  refine ⟨252223717861857358451027519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168149145241238238967351679 252223717861857358451027519)
  ·
    refine ⟨378335576792786037676541279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252223717861857358451027519 378335576792786037676541279)
    ·
      refine ⟨567503365189179056514811919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378335576792786037676541279 567503365189179056514811919)
      ·
        refine ⟨851255047783768584772217879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567503365189179056514811919 851255047783768584772217879)
        ·
          refine ⟨1276882571675652877158326819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851255047783768584772217879 1276882571675652877158326819)
          ·
            refine ⟨1915323857513479315737490229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276882571675652877158326819 1915323857513479315737490229)
            ·
              refine ⟨179561611641888685850389709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1915323857513479315737490229 179561611641888685850389709)
              ·
                refine ⟨67335604365708257193896141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179561611641888685850389709 67335604365708257193896141)
                ·
                  refine ⟨25250851637140596447711053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67335604365708257193896141 25250851637140596447711053)
                  ·
                    refine ⟨9469069363927723667891645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25250851637140596447711053 9469069363927723667891645)
                    ·
                      refine ⟨3550901011472896375459367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9469069363927723667891645 3550901011472896375459367)
                      ·
                        rfl

theorem cell23_6915355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 3].length) (baseStart_6915355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915355 prefixEnd_6915355 := by exact prefixLift 6915355
  have htrace : WordTrace (prefixWord ++ tailWord_6915355) baseStart_6915355 baseEnd_6915355 := by
    simpa [prefixWord, tailWord_6915355, baseEnd_6915355] using wordTrace_append hprefix tailTrace_6915355
  have hstable : (prefixWord ++ tailWord_6915355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915355).length < 2 ^ (prefixWord ++ tailWord_6915355).sum := by decide
  have hdescent : baseEnd_6915355 < baseStart_6915355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915362 : List Nat := [3, 3, 1, 1, 4, 2, 9]
def baseStart_6915362 : Nat := 118140960795 + 6915362 * 2 ^ 59
def prefixEnd_6915362 : Nat := 4983230072969 + 3 ^ 40 * 6915362 * 2
def baseEnd_6915362 : Nat := 43838328467129356149035

theorem tailTrace_6915362 : CollatzResearch.WordTrace tailWord_6915362 prefixEnd_6915362 43838328467129356149035 := by
  unfold tailWord_6915362
  simp only [CollatzResearch.WordTrace]
  refine ⟨63055993293207999661633085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168149315448554665764354893 63055993293207999661633085)
  ·
    refine ⟨23645997484952999873112407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63055993293207999661633085 23645997484952999873112407)
    ·
      refine ⟨35468996227429499809668611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23645997484952999873112407 35468996227429499809668611)
      ·
        refine ⟨53203494341144249714502917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35468996227429499809668611 53203494341144249714502917)
        ·
          refine ⟨9975655188964546821469297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53203494341144249714502917 9975655188964546821469297)
          ·
            refine ⟨7481741391723410116101973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9975655188964546821469297 7481741391723410116101973)
            ·
              refine ⟨43838328467129356149035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7481741391723410116101973 43838328467129356149035)
              ·
                rfl

theorem cell23_6915362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 9].length) (baseStart_6915362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915362 prefixEnd_6915362 := by exact prefixLift 6915362
  have htrace : WordTrace (prefixWord ++ tailWord_6915362) baseStart_6915362 baseEnd_6915362 := by
    simpa [prefixWord, tailWord_6915362, baseEnd_6915362] using wordTrace_append hprefix tailTrace_6915362
  have hstable : (prefixWord ++ tailWord_6915362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915362).length < 2 ^ (prefixWord ++ tailWord_6915362).sum := by decide
  have hdescent : baseEnd_6915362 < baseStart_6915362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915373 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_6915373 : Nat := 118140960795 + 6915373 * 2 ^ 59
def prefixEnd_6915373 : Nat := 4983230072969 + 3 ^ 40 * 6915373 * 2
def baseEnd_6915373 : Nat := 3550910254124677305034285

theorem tailTrace_6915373 : CollatzResearch.WordTrace tailWord_6915373 prefixEnd_6915373 3550910254124677305034285 := by
  unfold tailWord_6915373
  simp only [CollatzResearch.WordTrace]
  refine ⟨252224374375792147525182773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168149582917194765016788515 252224374375792147525182773)
  ·
    refine ⟨23646035097730513830485885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252224374375792147525182773 23646035097730513830485885)
    ·
      refine ⟨8867263161648942686432207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23646035097730513830485885 8867263161648942686432207)
      ·
        refine ⟨13300894742473414029648311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8867263161648942686432207 13300894742473414029648311)
        ·
          refine ⟨19951342113710121044472467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13300894742473414029648311 19951342113710121044472467)
          ·
            refine ⟨29927013170565181566708701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19951342113710121044472467 29927013170565181566708701)
            ·
              refine ⟨11222629938961943087515763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29927013170565181566708701 11222629938961943087515763)
              ·
                refine ⟨16833944908442914631273645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11222629938961943087515763 16833944908442914631273645)
                ·
                  refine ⟨6312729340666092986727617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16833944908442914631273645 6312729340666092986727617)
                  ·
                    refine ⟨4734547005499569740045713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6312729340666092986727617 4734547005499569740045713)
                    ·
                      refine ⟨3550910254124677305034285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734547005499569740045713 3550910254124677305034285)
                      ·
                        rfl

theorem cell23_6915373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_6915373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915373 prefixEnd_6915373 := by exact prefixLift 6915373
  have htrace : WordTrace (prefixWord ++ tailWord_6915373) baseStart_6915373 baseEnd_6915373 := by
    simpa [prefixWord, tailWord_6915373, baseEnd_6915373] using wordTrace_append hprefix tailTrace_6915373
  have hstable : (prefixWord ++ tailWord_6915373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915373).length < 2 ^ (prefixWord ++ tailWord_6915373).sum := by decide
  have hdescent : baseEnd_6915373 < baseStart_6915373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915399 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 3, 3, 2]
def baseStart_6915399 : Nat := 118140960795 + 6915399 * 2 ^ 59
def prefixEnd_6915399 : Nat := 4983230072969 + 3 ^ 40 * 6915399 * 2
def baseEnd_6915399 : Nat := 3550923604621694203309165

theorem tailTrace_6915399 : CollatzResearch.WordTrace tailWord_6915399 prefixEnd_6915399 3550923604621694203309165 := by
  unfold tailWord_6915399
  simp only [CollatzResearch.WordTrace]
  refine ⟨252225322673697953965629251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168150215115798635977086167 252225322673697953965629251)
  ·
    refine ⟨378337984010546930948443877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252225322673697953965629251 378337984010546930948443877)
    ·
      refine ⟨70938372001977549552833227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 378337984010546930948443877 70938372001977549552833227)
      ·
        refine ⟨106407558002966324329249841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70938372001977549552833227 106407558002966324329249841)
        ·
          refine ⟨79805668502224743246937381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106407558002966324329249841 79805668502224743246937381)
          ·
            refine ⟨14963562844167139358800759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79805668502224743246937381 14963562844167139358800759)
            ·
              refine ⟨22445344266250709038201139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14963562844167139358800759 22445344266250709038201139)
              ·
                refine ⟨33668016399376063557301709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22445344266250709038201139 33668016399376063557301709)
                ·
                  refine ⟨12625506149766023833988141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33668016399376063557301709 12625506149766023833988141)
                  ·
                    refine ⟨4734564806162258937745553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12625506149766023833988141 4734564806162258937745553)
                    ·
                      refine ⟨3550923604621694203309165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734564806162258937745553 3550923604621694203309165)
                      ·
                        rfl

theorem cell23_6915399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_6915399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915399 prefixEnd_6915399 := by exact prefixLift 6915399
  have htrace : WordTrace (prefixWord ++ tailWord_6915399) baseStart_6915399 baseEnd_6915399 := by
    simpa [prefixWord, tailWord_6915399, baseEnd_6915399] using wordTrace_append hprefix tailTrace_6915399
  have hstable : (prefixWord ++ tailWord_6915399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915399).length < 2 ^ (prefixWord ++ tailWord_6915399).sum := by decide
  have hdescent : baseEnd_6915399 < baseStart_6915399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915416 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 1, 3, 2]
def baseStart_6915416 : Nat := 118140960795 + 6915416 * 2 ^ 59
def prefixEnd_6915416 : Nat := 4983230072969 + 3 ^ 40 * 6915416 * 2
def baseEnd_6915416 : Nat := 3550932333792820636796587

theorem tailTrace_6915416 : CollatzResearch.WordTrace tailWord_6915416 prefixEnd_6915416 3550932333792820636796587 := by
  unfold tailWord_6915416
  simp only [CollatzResearch.WordTrace]
  refine ⟨126112971357318182934499051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168150628476424243912665401 126112971357318182934499051)
  ·
    refine ⟨189169457035977274401748577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126112971357318182934499051 189169457035977274401748577)
    ·
      refine ⟨141877092776982955801311433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189169457035977274401748577 141877092776982955801311433)
      ·
        refine ⟨106407819582737216850983575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141877092776982955801311433 106407819582737216850983575)
        ·
          refine ⟨159611729374105825276475363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106407819582737216850983575 159611729374105825276475363)
          ·
            refine ⟨239417594061158737914713045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159611729374105825276475363 239417594061158737914713045)
            ·
              refine ⟨5611349860808407919876087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 239417594061158737914713045 5611349860808407919876087)
              ·
                refine ⟨8417024791212611879814131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611349860808407919876087 8417024791212611879814131)
                ·
                  refine ⟨12625537186818917819721197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8417024791212611879814131 12625537186818917819721197)
                  ·
                    refine ⟨4734576445057094182395449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12625537186818917819721197 4734576445057094182395449)
                    ·
                      refine ⟨3550932333792820636796587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734576445057094182395449 3550932333792820636796587)
                      ·
                        rfl

theorem cell23_6915416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_6915416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915416 prefixEnd_6915416 := by exact prefixLift 6915416
  have htrace : WordTrace (prefixWord ++ tailWord_6915416) baseStart_6915416 baseEnd_6915416 := by
    simpa [prefixWord, tailWord_6915416, baseEnd_6915416] using wordTrace_append hprefix tailTrace_6915416
  have hstable : (prefixWord ++ tailWord_6915416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915416).length < 2 ^ (prefixWord ++ tailWord_6915416).sum := by decide
  have hdescent : baseEnd_6915416 < baseStart_6915416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915425 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_6915425 : Nat := 118140960795 + 6915425 * 2 ^ 59
def prefixEnd_6915425 : Nat := 4983230072969 + 3 ^ 40 * 6915425 * 2
def baseEnd_6915425 : Nat := 3550936955118711101584045

theorem tailTrace_6915425 : CollatzResearch.WordTrace tailWord_6915425 prefixEnd_6915425 3550936955118711101584045 := by
  unfold tailWord_6915425
  simp only [CollatzResearch.WordTrace]
  refine ⟨252226270971603760406075729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168150847314402506937383819 252226270971603760406075729)
  ·
    refine ⟨189169703228702820304556797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252226270971603760406075729 189169703228702820304556797)
    ·
      refine ⟨70938638710763557614208799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189169703228702820304556797 70938638710763557614208799)
      ·
        refine ⟨106407958066145336421313199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70938638710763557614208799 106407958066145336421313199)
        ·
          refine ⟨159611937099218004631969799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106407958066145336421313199 159611937099218004631969799)
          ·
            refine ⟨239417905648827006947954699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159611937099218004631969799 239417905648827006947954699)
            ·
              refine ⟨359126858473240510421932049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239417905648827006947954699 359126858473240510421932049)
              ·
                refine ⟨269345143854930382816449037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359126858473240510421932049 269345143854930382816449037)
                ·
                  refine ⟨101004428945598893556168389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269345143854930382816449037 101004428945598893556168389)
                  ·
                    refine ⟨18938330427299792541781573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101004428945598893556168389 18938330427299792541781573)
                    ·
                      refine ⟨3550936955118711101584045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18938330427299792541781573 3550936955118711101584045)
                      ·
                        rfl

theorem cell23_6915425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_6915425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915425 prefixEnd_6915425 := by exact prefixLift 6915425
  have htrace : WordTrace (prefixWord ++ tailWord_6915425) baseStart_6915425 baseEnd_6915425 := by
    simpa [prefixWord, tailWord_6915425, baseEnd_6915425] using wordTrace_append hprefix tailTrace_6915425
  have hstable : (prefixWord ++ tailWord_6915425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915425).length < 2 ^ (prefixWord ++ tailWord_6915425).sum := by decide
  have hdescent : baseEnd_6915425 < baseStart_6915425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915442 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_6915442 : Nat := 118140960795 + 6915442 * 2 ^ 59
def prefixEnd_6915442 : Nat := 4983230072969 + 3 ^ 40 * 6915442 * 2
def baseEnd_6915442 : Nat := 3550945684289837535071467

theorem tailTrace_6915442 : CollatzResearch.WordTrace tailWord_6915442 prefixEnd_6915442 3550945684289837535071467 := by
  unfold tailWord_6915442
  simp only [CollatzResearch.WordTrace]
  refine ⟨63056722753135543077361145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168151260675028114872963053 63056722753135543077361145)
  ·
    refine ⟨47292542064851657308020859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63056722753135543077361145 47292542064851657308020859)
    ·
      refine ⟨70938813097277485962031289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47292542064851657308020859 70938813097277485962031289)
      ·
        refine ⟨53204109822958114471523467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70938813097277485962031289 53204109822958114471523467)
        ·
          refine ⟨79806164734437171707285201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53204109822958114471523467 79806164734437171707285201)
          ·
            refine ⟨59854623550827878780463901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79806164734437171707285201 59854623550827878780463901)
            ·
              refine ⟨22445483831560454542673963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59854623550827878780463901 22445483831560454542673963)
              ·
                refine ⟨33668225747340681814010945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22445483831560454542673963 33668225747340681814010945)
                ·
                  refine ⟨25251169310505511360508209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33668225747340681814010945 25251169310505511360508209)
                  ·
                    refine ⟨18938376982879133520381157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25251169310505511360508209 18938376982879133520381157)
                    ·
                      refine ⟨3550945684289837535071467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18938376982879133520381157 3550945684289837535071467)
                      ·
                        rfl

theorem cell23_6915442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_6915442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915442 prefixEnd_6915442 := by exact prefixLift 6915442
  have htrace : WordTrace (prefixWord ++ tailWord_6915442) baseStart_6915442 baseEnd_6915442 := by
    simpa [prefixWord, tailWord_6915442, baseEnd_6915442] using wordTrace_append hprefix tailTrace_6915442
  have hstable : (prefixWord ++ tailWord_6915442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915442).length < 2 ^ (prefixWord ++ tailWord_6915442).sum := by decide
  have hdescent : baseEnd_6915442 < baseStart_6915442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915480 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 2, 2, 2]
def baseStart_6915480 : Nat := 118140960795 + 6915480 * 2 ^ 59
def prefixEnd_6915480 : Nat := 4983230072969 + 3 ^ 40 * 6915480 * 2
def baseEnd_6915480 : Nat := 3550965196554708386396293

theorem tailTrace_6915480 : CollatzResearch.WordTrace tailWord_6915480 prefixEnd_6915480 3550965196554708386396293 := by
  unfold tailWord_6915480
  simp only [CollatzResearch.WordTrace]
  refine ⟨126114138493202252399663947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168152184657603003199551929 126114138493202252399663947)
  ·
    refine ⟨189171207739803378599495921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126114138493202252399663947 189171207739803378599495921)
    ·
      refine ⟨141878405804852533949621941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189171207739803378599495921 141878405804852533949621941)
      ·
        refine ⟨13301100544204925057777057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141878405804852533949621941 13301100544204925057777057)
        ·
          refine ⟨9975825408153693793332793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13301100544204925057777057 9975825408153693793332793)
          ·
            refine ⟨7481869056115270344999595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9975825408153693793332793 7481869056115270344999595)
            ·
              refine ⟨11222803584172905517499393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7481869056115270344999595 11222803584172905517499393)
              ·
                refine ⟨8417102688129679138124545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11222803584172905517499393 8417102688129679138124545)
                ·
                  refine ⟨6312827016097259353593409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8417102688129679138124545 6312827016097259353593409)
                  ·
                    refine ⟨4734620262072944515195057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6312827016097259353593409 4734620262072944515195057)
                    ·
                      refine ⟨3550965196554708386396293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734620262072944515195057 3550965196554708386396293)
                      ·
                        rfl

theorem cell23_6915480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_6915480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915480 prefixEnd_6915480 := by exact prefixLift 6915480
  have htrace : WordTrace (prefixWord ++ tailWord_6915480) baseStart_6915480 baseEnd_6915480 := by
    simpa [prefixWord, tailWord_6915480, baseEnd_6915480] using wordTrace_append hprefix tailTrace_6915480
  have hstable : (prefixWord ++ tailWord_6915480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915480).length < 2 ^ (prefixWord ++ tailWord_6915480).sum := by decide
  have hdescent : baseEnd_6915480 < baseStart_6915480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915482 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_6915482 : Nat := 118140960795 + 6915482 * 2 ^ 59
def prefixEnd_6915482 : Nat := 4983230072969 + 3 ^ 40 * 6915482 * 2
def baseEnd_6915482 : Nat := 1183655407838672459523761

theorem tailTrace_6915482 : CollatzResearch.WordTrace tailWord_6915482 prefixEnd_6915482 1183655407838672459523761 := by
  unfold tailWord_6915482
  simp only [CollatzResearch.WordTrace]
  refine ⟨63057087483099314785225175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168152233288264839427267133 63057087483099314785225175)
  ·
    refine ⟨94585631224648972177837763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63057087483099314785225175 94585631224648972177837763)
    ·
      refine ⟨141878446836973458266756645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94585631224648972177837763 141878446836973458266756645)
      ·
        refine ⟨26602208781932523425016871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141878446836973458266756645 26602208781932523425016871)
        ·
          refine ⟨39903313172898785137525307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26602208781932523425016871 39903313172898785137525307)
          ·
            refine ⟨59854969759348177706287961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39903313172898785137525307 59854969759348177706287961)
            ·
              refine ⟨44891227319511133279715971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59854969759348177706287961 44891227319511133279715971)
              ·
                refine ⟨67336840979266699919573957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44891227319511133279715971 67336840979266699919573957)
                ·
                  refine ⟨12625657683612506234920117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67336840979266699919573957 12625657683612506234920117)
                  ·
                    refine ⟨1183655407838672459523761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12625657683612506234920117 1183655407838672459523761)
                    ·
                      rfl

theorem cell23_6915482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_6915482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915482 prefixEnd_6915482 := by exact prefixLift 6915482
  have htrace : WordTrace (prefixWord ++ tailWord_6915482) baseStart_6915482 baseEnd_6915482 := by
    simpa [prefixWord, tailWord_6915482, baseEnd_6915482] using wordTrace_append hprefix tailTrace_6915482
  have hstable : (prefixWord ++ tailWord_6915482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915482).length < 2 ^ (prefixWord ++ tailWord_6915482).sum := by decide
  have hdescent : baseEnd_6915482 < baseStart_6915482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915486 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_6915486 : Nat := 118140960795 + 6915486 * 2 ^ 59
def prefixEnd_6915486 : Nat := 4983230072969 + 3 ^ 40 * 6915486 * 2
def baseEnd_6915486 : Nat := 394552030826515040324585

theorem tailTrace_6915486 : CollatzResearch.WordTrace tailWord_6915486 prefixEnd_6915486 394552030826515040324585 := by
  unfold tailWord_6915486
  simp only [CollatzResearch.WordTrace]
  refine ⟨31528561978047845978005789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168152330549588511882697541 31528561978047845978005789)
  ·
    refine ⟨11823210741767942241752171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31528561978047845978005789 11823210741767942241752171)
    ·
      refine ⟨17734816112651913362628257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11823210741767942241752171 17734816112651913362628257)
      ·
        refine ⟨13301112084488935021971193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17734816112651913362628257 13301112084488935021971193)
        ·
          refine ⟨9975834063366701266478395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13301112084488935021971193 9975834063366701266478395)
          ·
            refine ⟨14963751095050051899717593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9975834063366701266478395 14963751095050051899717593)
            ·
              refine ⟨11222813321287538924788195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14963751095050051899717593 11222813321287538924788195)
              ·
                refine ⟨16834219981931308387182293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11222813321287538924788195 16834219981931308387182293)
                ·
                  refine ⟨394552030826515040324585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16834219981931308387182293 394552030826515040324585)
                  ·
                    rfl

theorem cell23_6915486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_6915486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915486 prefixEnd_6915486 := by exact prefixLift 6915486
  have htrace : WordTrace (prefixWord ++ tailWord_6915486) baseStart_6915486 baseEnd_6915486 := by
    simpa [prefixWord, tailWord_6915486, baseEnd_6915486] using wordTrace_append hprefix tailTrace_6915486
  have hstable : (prefixWord ++ tailWord_6915486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915486).length < 2 ^ (prefixWord ++ tailWord_6915486).sum := by decide
  have hdescent : baseEnd_6915486 < baseStart_6915486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915546 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 3, 4]
def baseStart_6915546 : Nat := 118140960795 + 6915546 * 2 ^ 59
def prefixEnd_6915546 : Nat := 4983230072969 + 3 ^ 40 * 6915546 * 2
def baseEnd_6915546 : Nat := 1183666362092635042723663

theorem tailTrace_6915546 : CollatzResearch.WordTrace tailWord_6915546 prefixEnd_6915546 1183666362092635042723663 := by
  unfold tailWord_6915546
  simp only [CollatzResearch.WordTrace]
  refine ⟨63057671051041349517807623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168153789469443598714153661 63057671051041349517807623)
  ·
    refine ⟨94586506576562024276711435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63057671051041349517807623 94586506576562024276711435)
    ·
      refine ⟨141879759864843036415067153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94586506576562024276711435 141879759864843036415067153)
      ·
        refine ⟨106409819898632277311300365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141879759864843036415067153 106409819898632277311300365)
        ·
          refine ⟨39903682461987103991737637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106409819898632277311300365 39903682461987103991737637)
          ·
            refine ⟨7481940461622581998450807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39903682461987103991737637 7481940461622581998450807)
            ·
              refine ⟨11222910692433872997676211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7481940461622581998450807 11222910692433872997676211)
              ·
                refine ⟨16834366038650809496514317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11222910692433872997676211 16834366038650809496514317)
                ·
                  refine ⟨6312887264494053561192869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16834366038650809496514317 6312887264494053561192869)
                  ·
                    refine ⟨1183666362092635042723663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6312887264494053561192869 1183666362092635042723663)
                    ·
                      rfl

theorem cell23_6915546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_6915546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915546 prefixEnd_6915546 := by exact prefixLift 6915546
  have htrace : WordTrace (prefixWord ++ tailWord_6915546) baseStart_6915546 baseEnd_6915546 := by
    simpa [prefixWord, tailWord_6915546, baseEnd_6915546] using wordTrace_append hprefix tailTrace_6915546
  have hstable : (prefixWord ++ tailWord_6915546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915546).length < 2 ^ (prefixWord ++ tailWord_6915546).sum := by decide
  have hdescent : baseEnd_6915546 < baseStart_6915546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915552 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 3]
def baseStart_6915552 : Nat := 118140960795 + 6915552 * 2 ^ 59
def prefixEnd_6915552 : Nat := 4983230072969 + 3 ^ 40 * 6915552 * 2
def baseEnd_6915552 : Nat := 3551002167161832104695961

theorem tailTrace_6915552 : CollatzResearch.WordTrace tailWord_6915552 prefixEnd_6915552 3551002167161832104695961 := by
  unfold tailWord_6915552
  simp only [CollatzResearch.WordTrace]
  refine ⟨126115451521071830547974455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168153935361429107397299273 126115451521071830547974455)
  ·
    refine ⟨189173177281607745821961683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126115451521071830547974455 189173177281607745821961683)
    ·
      refine ⟨283759765922411618732942525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189173177281607745821961683 283759765922411618732942525)
      ·
        refine ⟨106409912220904357024853447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283759765922411618732942525 106409912220904357024853447)
        ·
          refine ⟨159614868331356535537280171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106409912220904357024853447 159614868331356535537280171)
          ·
            refine ⟨239422302497034803305920257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159614868331356535537280171 239422302497034803305920257)
            ·
              refine ⟨179566726872776102479440193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239422302497034803305920257 179566726872776102479440193)
              ·
                refine ⟨134675045154582076859580145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179566726872776102479440193 134675045154582076859580145)
                ·
                  refine ⟨101006283865936557644685109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134675045154582076859580145 101006283865936557644685109)
                  ·
                    refine ⟨9469339112431552279189229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101006283865936557644685109 9469339112431552279189229)
                    ·
                      refine ⟨3551002167161832104695961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9469339112431552279189229 3551002167161832104695961)
                      ·
                        rfl

theorem cell23_6915552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_6915552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915552 prefixEnd_6915552 := by exact prefixLift 6915552
  have htrace : WordTrace (prefixWord ++ tailWord_6915552) baseStart_6915552 baseEnd_6915552 := by
    simpa [prefixWord, tailWord_6915552, baseEnd_6915552] using wordTrace_append hprefix tailTrace_6915552
  have hstable : (prefixWord ++ tailWord_6915552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915552).length < 2 ^ (prefixWord ++ tailWord_6915552).sum := by decide
  have hdescent : baseEnd_6915552 < baseStart_6915552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915559 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 6]
def baseStart_6915559 : Nat := 118140960795 + 6915559 * 2 ^ 59
def prefixEnd_6915559 : Nat := 4983230072969 + 3 ^ 40 * 6915559 * 2
def baseEnd_6915559 : Nat := 394556195725157064145381

theorem tailTrace_6915559 : CollatzResearch.WordTrace tailWord_6915559 prefixEnd_6915559 394556195725157064145381 := by
  unfold tailWord_6915559
  simp only [CollatzResearch.WordTrace]
  refine ⟨252231158353118301291453731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168154105568745534194302487 252231158353118301291453731)
  ·
    refine ⟨378346737529677451937180597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252231158353118301291453731 378346737529677451937180597)
    ·
      refine ⟨35470006643407261119110681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 378346737529677451937180597 35470006643407261119110681)
      ·
        refine ⟨26602504982555445839333011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35470006643407261119110681 26602504982555445839333011)
        ·
          refine ⟨39903757473833168758999517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26602504982555445839333011 39903757473833168758999517)
          ·
            refine ⟨14963909052687438284624819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39903757473833168758999517 14963909052687438284624819)
            ·
              refine ⟨22445863579031157426937229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14963909052687438284624819 22445863579031157426937229)
              ·
                refine ⟨8417198842136684035101461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22445863579031157426937229 8417198842136684035101461)
                ·
                  refine ⟨394556195725157064145381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8417198842136684035101461 394556195725157064145381)
                  ·
                    rfl

theorem cell23_6915559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 6].length) (baseStart_6915559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915559 prefixEnd_6915559 := by exact prefixLift 6915559
  have htrace : WordTrace (prefixWord ++ tailWord_6915559) baseStart_6915559 baseEnd_6915559 := by
    simpa [prefixWord, tailWord_6915559, baseEnd_6915559] using wordTrace_append hprefix tailTrace_6915559
  have hstable : (prefixWord ++ tailWord_6915559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915559).length < 2 ^ (prefixWord ++ tailWord_6915559).sum := by decide
  have hdescent : baseEnd_6915559 < baseStart_6915559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915573 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_6915573 : Nat := 118140960795 + 6915573 * 2 ^ 59
def prefixEnd_6915573 : Nat := 4983230072969 + 3 ^ 40 * 6915573 * 2
def baseEnd_6915573 : Nat := 3551012950255576522533365

theorem tailTrace_6915573 : CollatzResearch.WordTrace tailWord_6915573 prefixEnd_6915573 3551012950255576522533365 := by
  unfold tailWord_6915573
  simp only [CollatzResearch.WordTrace]
  refine ⟨252231668975067581682463373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168154445983378387788308915 252231668975067581682463373)
  ·
    refine ⟨94586875865650343130923765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252231668975067581682463373 94586875865650343130923765)
    ·
      refine ⟨8867519612404719668524103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94586875865650343130923765 8867519612404719668524103)
      ·
        refine ⟨13301279418607079502786155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8867519612404719668524103 13301279418607079502786155)
        ·
          refine ⟨19951919127910619254179233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13301279418607079502786155 19951919127910619254179233)
          ·
            refine ⟨14963939345932964440634425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19951919127910619254179233 14963939345932964440634425)
            ·
              refine ⟨11222954509449723330475819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14963939345932964440634425 11222954509449723330475819)
              ·
                refine ⟨16834431764174584995713729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11222954509449723330475819 16834431764174584995713729)
                ·
                  refine ⟨12625823823130938746785297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16834431764174584995713729 12625823823130938746785297)
                  ·
                    refine ⟨9469367867348204060088973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12625823823130938746785297 9469367867348204060088973)
                    ·
                      refine ⟨3551012950255576522533365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9469367867348204060088973 3551012950255576522533365)
                      ·
                        rfl

theorem cell23_6915573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_6915573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915573 prefixEnd_6915573 := by exact prefixLift 6915573
  have htrace : WordTrace (prefixWord ++ tailWord_6915573) baseStart_6915573 baseEnd_6915573 := by
    simpa [prefixWord, tailWord_6915573, baseEnd_6915573] using wordTrace_append hprefix tailTrace_6915573
  have hstable : (prefixWord ++ tailWord_6915573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915573).length < 2 ^ (prefixWord ++ tailWord_6915573).sum := by decide
  have hdescent : baseEnd_6915573 < baseStart_6915573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915579 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 6, 3, 2]
def baseStart_6915579 : Nat := 118140960795 + 6915579 * 2 ^ 59
def prefixEnd_6915579 : Nat := 4983230072969 + 3 ^ 40 * 6915579 * 2
def baseEnd_6915579 : Nat := 3551016031139503499058337

theorem tailTrace_6915579 : CollatzResearch.WordTrace tailWord_6915579 prefixEnd_6915579 3551016031139503499058337 := by
  unfold tailWord_6915579
  simp only [CollatzResearch.WordTrace]
  refine ⟨252231887813045844707181791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168154591875363896471454527 252231887813045844707181791)
  ·
    refine ⟨378347831719568767060772687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252231887813045844707181791 378347831719568767060772687)
    ·
      refine ⟨567521747579353150591159031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378347831719568767060772687 567521747579353150591159031)
      ·
        refine ⟨851282621369029725886738547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567521747579353150591159031 851282621369029725886738547)
        ·
          refine ⟨1276923932053544588830107821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851282621369029725886738547 1276923932053544588830107821)
          ·
            refine ⟨478846474520079220811290433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1276923932053544588830107821 478846474520079220811290433)
            ·
              refine ⟨359134855890059415608467825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478846474520079220811290433 359134855890059415608467825)
              ·
                refine ⟨269351141917544561706350869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359134855890059415608467825 269351141917544561706350869)
                ·
                  refine ⟨12625834777384901329985197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 269351141917544561706350869 12625834777384901329985197)
                  ·
                    refine ⟨4734688041519337998744449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12625834777384901329985197 4734688041519337998744449)
                    ·
                      refine ⟨3551016031139503499058337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734688041519337998744449 3551016031139503499058337)
                      ·
                        rfl

theorem cell23_6915579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 3, 2].length) (baseStart_6915579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915579 prefixEnd_6915579 := by exact prefixLift 6915579
  have htrace : WordTrace (prefixWord ++ tailWord_6915579) baseStart_6915579 baseEnd_6915579 := by
    simpa [prefixWord, tailWord_6915579, baseEnd_6915579] using wordTrace_append hprefix tailTrace_6915579
  have hstable : (prefixWord ++ tailWord_6915579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915579).length < 2 ^ (prefixWord ++ tailWord_6915579).sum := by decide
  have hdescent : baseEnd_6915579 < baseStart_6915579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915597 : List Nat := [1, 7, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_6915597 : Nat := 118140960795 + 6915597 * 2 ^ 59
def prefixEnd_6915597 : Nat := 4983230072969 + 3 ^ 40 * 6915597 * 2
def baseEnd_6915597 : Nat := 1183675091263761476211085

theorem tailTrace_6915597 : CollatzResearch.WordTrace tailWord_6915597 prefixEnd_6915597 1183675091263761476211085 := by
  unfold tailWord_6915597
  simp only [CollatzResearch.WordTrace]
  refine ⟨252232544326980633781337045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168155029551320422520891363 252232544326980633781337045)
  ·
    refine ⟨5911700257663608604250087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 252232544326980633781337045 5911700257663608604250087)
    ·
      refine ⟨8867550386495412906375131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5911700257663608604250087 8867550386495412906375131)
      ·
        refine ⟨13301325579743119359562697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8867550386495412906375131 13301325579743119359562697)
        ·
          refine ⟨9975994184807339519672023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13301325579743119359562697 9975994184807339519672023)
          ·
            refine ⟨14963991277211009279508035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9975994184807339519672023 14963991277211009279508035)
            ·
              refine ⟨22445986915816513919262053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14963991277211009279508035 22445986915816513919262053)
              ·
                refine ⟨4208622546715596359861635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22445986915816513919262053 4208622546715596359861635)
                ·
                  refine ⟨6312933820073394539792453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208622546715596359861635 6312933820073394539792453)
                  ·
                    refine ⟨1183675091263761476211085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6312933820073394539792453 1183675091263761476211085)
                    ·
                      rfl

theorem cell23_6915597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_6915597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915597 prefixEnd_6915597 := by exact prefixLift 6915597
  have htrace : WordTrace (prefixWord ++ tailWord_6915597) baseStart_6915597 baseEnd_6915597 := by
    simpa [prefixWord, tailWord_6915597, baseEnd_6915597] using wordTrace_append hprefix tailTrace_6915597
  have hstable : (prefixWord ++ tailWord_6915597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915597).length < 2 ^ (prefixWord ++ tailWord_6915597).sum := by decide
  have hdescent : baseEnd_6915597 < baseStart_6915597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915603 : List Nat := [1, 1, 1, 2, 1, 7, 1, 4, 1, 1, 3]
def baseStart_6915603 : Nat := 118140960795 + 6915603 * 2 ^ 59
def prefixEnd_6915603 : Nat := 4983230072969 + 3 ^ 40 * 6915603 * 2
def baseEnd_6915603 : Nat := 3551028354675211405158227

theorem tailTrace_6915603 : CollatzResearch.WordTrace tailWord_6915603 prefixEnd_6915603 3551028354675211405158227 := by
  unfold tailWord_6915603
  simp only [CollatzResearch.WordTrace]
  refine ⟨252232763164958896806055463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168155175443305931204036975 252232763164958896806055463)
  ·
    refine ⟨378349144747438345209083195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252232763164958896806055463 378349144747438345209083195)
    ·
      refine ⟨567523717121157517813624793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378349144747438345209083195 567523717121157517813624793)
      ·
        refine ⟨425642787840868138360218595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567523717121157517813624793 425642787840868138360218595)
        ·
          refine ⟨638464181761302207540327893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425642787840868138360218595 638464181761302207540327893)
          ·
            refine ⟨14964004260030520489226435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 638464181761302207540327893 14964004260030520489226435)
            ·
              refine ⟨22446006390045780733839653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14964004260030520489226435 22446006390045780733839653)
              ·
                refine ⟨4208626198133583887594935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22446006390045780733839653 4208626198133583887594935)
                ·
                  refine ⟨6312939297200375831392403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208626198133583887594935 6312939297200375831392403)
                  ·
                    refine ⟨9469408945800563747088605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6312939297200375831392403 9469408945800563747088605)
                    ·
                      refine ⟨3551028354675211405158227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9469408945800563747088605 3551028354675211405158227)
                      ·
                        rfl

theorem cell23_6915603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 1, 1, 3].length) (baseStart_6915603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915603 prefixEnd_6915603 := by exact prefixLift 6915603
  have htrace : WordTrace (prefixWord ++ tailWord_6915603) baseStart_6915603 baseEnd_6915603 := by
    simpa [prefixWord, tailWord_6915603, baseEnd_6915603] using wordTrace_append hprefix tailTrace_6915603
  have hstable : (prefixWord ++ tailWord_6915603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915603).length < 2 ^ (prefixWord ++ tailWord_6915603).sum := by decide
  have hdescent : baseEnd_6915603 < baseStart_6915603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915626 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_6915626 : Nat := 118140960795 + 6915626 * 2 ^ 59
def prefixEnd_6915626 : Nat := 4983230072969 + 3 ^ 40 * 6915626 * 2
def baseEnd_6915626 : Nat := 3551040164730264815170621

theorem tailTrace_6915626 : CollatzResearch.WordTrace tailWord_6915626 prefixEnd_6915626 3551040164730264815170621 := by
  unfold tailWord_6915626
  simp only [CollatzResearch.WordTrace]
  refine ⟨63058400510968892933535683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168155734695917047822761821 63058400510968892933535683)
  ·
    refine ⟨94587600766453339400303525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63058400510968892933535683 94587600766453339400303525)
    ·
      refine ⟨17735175143710001137556911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94587600766453339400303525 17735175143710001137556911)
      ·
        refine ⟨26602762715565001706335367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17735175143710001137556911 26602762715565001706335367)
        ·
          refine ⟨39904144073347502559503051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26602762715565001706335367 39904144073347502559503051)
          ·
            refine ⟨59856216110021253839254577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39904144073347502559503051 59856216110021253839254577)
            ·
              refine ⟨44892162082515940379440933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59856216110021253839254577 44892162082515940379440933)
              ·
                refine ⟨8417280390471738821145175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44892162082515940379440933 8417280390471738821145175)
                ·
                  refine ⟨12625920585707608231717763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8417280390471738821145175 12625920585707608231717763)
                  ·
                    refine ⟨18938880878561412347576645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12625920585707608231717763 18938880878561412347576645)
                    ·
                      refine ⟨3551040164730264815170621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18938880878561412347576645 3551040164730264815170621)
                      ·
                        rfl

theorem cell23_6915626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_6915626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915626 prefixEnd_6915626 := by exact prefixLift 6915626
  have htrace : WordTrace (prefixWord ++ tailWord_6915626) baseStart_6915626 baseEnd_6915626 := by
    simpa [prefixWord, tailWord_6915626, baseEnd_6915626] using wordTrace_append hprefix tailTrace_6915626
  have hstable : (prefixWord ++ tailWord_6915626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915626).length < 2 ^ (prefixWord ++ tailWord_6915626).sum := by decide
  have hdescent : baseEnd_6915626 < baseStart_6915626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915630 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_6915630 : Nat := 118140960795 + 6915630 * 2 ^ 59
def prefixEnd_6915630 : Nat := 4983230072969 + 3 ^ 40 * 6915630 * 2
def baseEnd_6915630 : Nat := 3551042218652882799520603

theorem tailTrace_6915630 : CollatzResearch.WordTrace tailWord_6915630 prefixEnd_6915630 3551042218652882799520603 := by
  unfold tailWord_6915630
  simp only [CollatzResearch.WordTrace]
  refine ⟨31529218491982635052161043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168155831957240720278192229 31529218491982635052161043)
  ·
    refine ⟨47293827737973952578241565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31529218491982635052161043 47293827737973952578241565)
    ·
      refine ⟨17735185401740232216840587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47293827737973952578241565 17735185401740232216840587)
      ·
        refine ⟨26602778102610348325260881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17735185401740232216840587 26602778102610348325260881)
        ·
          refine ⟨19952083576957761243945661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26602778102610348325260881 19952083576957761243945661)
          ·
            refine ⟨7482031341359160466479623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19952083576957761243945661 7482031341359160466479623)
            ·
              refine ⟨11223047012038740699719435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7482031341359160466479623 11223047012038740699719435)
              ·
                refine ⟨16834570518058111049579153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11223047012038740699719435 16834570518058111049579153)
                ·
                  refine ⟨12625927888543583287184365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16834570518058111049579153 12625927888543583287184365)
                  ·
                    refine ⟨4734722958203843732694137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12625927888543583287184365 4734722958203843732694137)
                    ·
                      refine ⟨3551042218652882799520603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734722958203843732694137 3551042218652882799520603)
                      ·
                        rfl

theorem cell23_6915630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_6915630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915630 prefixEnd_6915630 := by exact prefixLift 6915630
  have htrace : WordTrace (prefixWord ++ tailWord_6915630) baseStart_6915630 baseEnd_6915630 := by
    simpa [prefixWord, tailWord_6915630, baseEnd_6915630] using wordTrace_append hprefix tailTrace_6915630
  have hstable : (prefixWord ++ tailWord_6915630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915630).length < 2 ^ (prefixWord ++ tailWord_6915630).sum := by decide
  have hdescent : baseEnd_6915630 < baseStart_6915630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915639 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_6915639 : Nat := 118140960795 + 6915639 * 2 ^ 59
def prefixEnd_6915639 : Nat := 4983230072969 + 3 ^ 40 * 6915639 * 2
def baseEnd_6915639 : Nat := 3551046839978773264308061

theorem tailTrace_6915639 : CollatzResearch.WordTrace tailWord_6915639 prefixEnd_6915639 3551046839978773264308061 := by
  unfold tailWord_6915639
  simp only [CollatzResearch.WordTrace]
  refine ⟨252234076192828474954365971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168156050795218983302910647 252234076192828474954365971)
  ·
    refine ⟨378351114289242712431548957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252234076192828474954365971 378351114289242712431548957)
    ·
      refine ⟨141881667858466017161830859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378351114289242712431548957 141881667858466017161830859)
      ·
        refine ⟨212822501787699025742746289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141881667858466017161830859 212822501787699025742746289)
        ·
          refine ⟨159616876340774269307059717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212822501787699025742746289 159616876340774269307059717)
          ·
            refine ⟨29928164313895175495073697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159616876340774269307059717 29928164313895175495073697)
            ·
              refine ⟨22446123235421381621305273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29928164313895175495073697 22446123235421381621305273)
              ·
                refine ⟨16834592426566036215978955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22446123235421381621305273 16834592426566036215978955)
                ·
                  refine ⟨25251888639849054323968433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16834592426566036215978955 25251888639849054323968433)
                  ·
                    refine ⟨18938916479886790742976325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25251888639849054323968433 18938916479886790742976325)
                    ·
                      refine ⟨3551046839978773264308061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18938916479886790742976325 3551046839978773264308061)
                      ·
                        rfl

theorem cell23_6915639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_6915639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915639 prefixEnd_6915639 := by exact prefixLift 6915639
  have htrace : WordTrace (prefixWord ++ tailWord_6915639) baseStart_6915639 baseEnd_6915639 := by
    simpa [prefixWord, tailWord_6915639, baseEnd_6915639] using wordTrace_append hprefix tailTrace_6915639
  have hstable : (prefixWord ++ tailWord_6915639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915639).length < 2 ^ (prefixWord ++ tailWord_6915639).sum := by decide
  have hdescent : baseEnd_6915639 < baseStart_6915639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915660 : List Nat := [2, 2, 1, 3, 1, 3, 2, 4, 1, 2, 2]
def baseStart_6915660 : Nat := 118140960795 + 6915660 * 2 ^ 59
def prefixEnd_6915660 : Nat := 4983230072969 + 3 ^ 40 * 6915660 * 2
def baseEnd_6915660 : Nat := 3551057623072517682145465

theorem tailTrace_6915660 : CollatzResearch.WordTrace tailWord_6915660 prefixEnd_6915660 3551057623072517682145465 := by
  unfold tailWord_6915660
  simp only [CollatzResearch.WordTrace]
  refine ⟨126117421062876197770440217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168156561417168263693920289 126117421062876197770440217)
  ·
    refine ⟨94588065797157148327830163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126117421062876197770440217 94588065797157148327830163)
    ·
      refine ⟨141882098695735722491745245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94588065797157148327830163 141882098695735722491745245)
      ·
        refine ⟨53205787010900895934404467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141882098695735722491745245 53205787010900895934404467)
        ·
          refine ⟨79808680516351343901606701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53205787010900895934404467 79808680516351343901606701)
          ·
            refine ⟨29928255193631753963102513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79808680516351343901606701 29928255193631753963102513)
            ·
              refine ⟨22446191395223815472326885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29928255193631753963102513 22446191395223815472326885)
              ·
                refine ⟨4208660886604465401061291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22446191395223815472326885 4208660886604465401061291)
                ·
                  refine ⟨6312991329906698101591937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208660886604465401061291 6312991329906698101591937)
                  ·
                    refine ⟨4734743497430023576193953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6312991329906698101591937 4734743497430023576193953)
                    ·
                      refine ⟨3551057623072517682145465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734743497430023576193953 3551057623072517682145465)
                      ·
                        rfl

theorem cell23_6915660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_6915660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915660 prefixEnd_6915660 := by exact prefixLift 6915660
  have htrace : WordTrace (prefixWord ++ tailWord_6915660) baseStart_6915660 baseEnd_6915660 := by
    simpa [prefixWord, tailWord_6915660, baseEnd_6915660] using wordTrace_append hprefix tailTrace_6915660
  have hstable : (prefixWord ++ tailWord_6915660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915660).length < 2 ^ (prefixWord ++ tailWord_6915660).sum := by decide
  have hdescent : baseEnd_6915660 < baseStart_6915660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915694 : List Nat := [4, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_6915694 : Nat := 118140960795 + 6915694 * 2 ^ 59
def prefixEnd_6915694 : Nat := 4983230072969 + 3 ^ 40 * 6915694 * 2
def baseEnd_6915694 : Nat := 3551075081414770549120309

theorem tailTrace_6915694 : CollatzResearch.WordTrace tailWord_6915694 prefixEnd_6915694 3551075081414770549120309 := by
  unfold tailWord_6915694
  simp only [CollatzResearch.WordTrace]
  refine ⟨31529510275953652418452267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168157388138419479565078757 31529510275953652418452267)
  ·
    refine ⟨47294265413930478627678401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31529510275953652418452267 47294265413930478627678401)
    ·
      refine ⟨35470699060447858970758801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47294265413930478627678401 35470699060447858970758801)
      ·
        refine ⟨26603024295335894228069101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35470699060447858970758801 26603024295335894228069101)
        ·
          refine ⟨9976134110750960335525913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26603024295335894228069101 9976134110750960335525913)
          ·
            refine ⟨7482100583063220251644435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9976134110750960335525913 7482100583063220251644435)
            ·
              refine ⟨11223150874594830377466653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7482100583063220251644435 11223150874594830377466653)
              ·
                refine ⟨4208681577973061391549995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11223150874594830377466653 4208681577973061391549995)
                ·
                  refine ⟨6313022366959592087324993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208681577973061391549995 6313022366959592087324993)
                  ·
                    refine ⟨4734766775219694065493745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6313022366959592087324993 4734766775219694065493745)
                    ·
                      refine ⟨3551075081414770549120309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734766775219694065493745 3551075081414770549120309)
                      ·
                        rfl

theorem cell23_6915694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_6915694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915694 prefixEnd_6915694 := by exact prefixLift 6915694
  have htrace : WordTrace (prefixWord ++ tailWord_6915694) baseStart_6915694 baseEnd_6915694 := by
    simpa [prefixWord, tailWord_6915694, baseEnd_6915694] using wordTrace_append hprefix tailTrace_6915694
  have hstable : (prefixWord ++ tailWord_6915694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915694).length < 2 ^ (prefixWord ++ tailWord_6915694).sum := by decide
  have hdescent : baseEnd_6915694 < baseStart_6915694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915776 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 1, 7, 2]
def baseStart_6915776 : Nat := 118140960795 + 6915776 * 2 ^ 59
def prefixEnd_6915776 : Nat := 4983230072969 + 3 ^ 40 * 6915776 * 2
def baseEnd_6915776 : Nat := 3551117186828439228294931

theorem tailTrace_6915776 : CollatzResearch.WordTrace tailWord_6915776 prefixEnd_6915776 3551117186828439228294931 := by
  unfold tailWord_6915776
  simp only [CollatzResearch.WordTrace]
  refine ⟨126119536496666073676051591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168159381995554764901402121 126119536496666073676051591)
  ·
    refine ⟨189179304744999110514077387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126119536496666073676051591 189179304744999110514077387)
    ·
      refine ⟨283768957117498665771116081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189179304744999110514077387 283768957117498665771116081)
      ·
        refine ⟨212826717838123999328337061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283768957117498665771116081 212826717838123999328337061)
        ·
          refine ⟨39905009594648249874063199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212826717838123999328337061 39905009594648249874063199)
          ·
            refine ⟨59857514391972374811094799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39905009594648249874063199 59857514391972374811094799)
            ·
              refine ⟨89786271587958562216642199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59857514391972374811094799 89786271587958562216642199)
              ·
                refine ⟨134679407381937843324963299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89786271587958562216642199 134679407381937843324963299)
                ·
                  refine ⟨202019111072906764987444949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134679407381937843324963299 202019111072906764987444949)
                  ·
                    refine ⟨4734822915771252304393241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 202019111072906764987444949 4734822915771252304393241)
                    ·
                      refine ⟨3551117186828439228294931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734822915771252304393241 3551117186828439228294931)
                      ·
                        rfl

theorem cell23_6915776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 7, 2].length) (baseStart_6915776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915776 prefixEnd_6915776 := by exact prefixLift 6915776
  have htrace : WordTrace (prefixWord ++ tailWord_6915776) baseStart_6915776 baseEnd_6915776 := by
    simpa [prefixWord, tailWord_6915776, baseEnd_6915776] using wordTrace_append hprefix tailTrace_6915776
  have hstable : (prefixWord ++ tailWord_6915776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915776).length < 2 ^ (prefixWord ++ tailWord_6915776).sum := by decide
  have hdescent : baseEnd_6915776 < baseStart_6915776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915819 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 6]
def baseStart_6915819 : Nat := 118140960795 + 6915819 * 2 ^ 59
def prefixEnd_6915819 : Nat := 4983230072969 + 3 ^ 40 * 6915819 * 2
def baseEnd_6915819 : Nat := 3551139266496582560057233

theorem tailTrace_6915819 : CollatzResearch.WordTrace tailWord_6915819 prefixEnd_6915819 3551139266496582560057233 := by
  unfold tailWord_6915819
  simp only [CollatzResearch.WordTrace]
  refine ⟨252240641332176365695918511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168160427554784243797279007 252240641332176365695918511)
  ·
    refine ⟨378360961998264548543877767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252240641332176365695918511 378360961998264548543877767)
    ·
      refine ⟨567541442997396822815816651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378360961998264548543877767 567541442997396822815816651)
      ·
        refine ⟨851312164496095234223724977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567541442997396822815816651 851312164496095234223724977)
        ·
          refine ⟨638484123372071425667793733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851312164496095234223724977 638484123372071425667793733)
          ·
            refine ⟨119715773132263392312711325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 638484123372071425667793733 119715773132263392312711325)
            ·
              refine ⟨44893414924598772117266747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119715773132263392312711325 44893414924598772117266747)
              ·
                refine ⟨67340122386898158175900121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44893414924598772117266747 67340122386898158175900121)
                ·
                  refine ⟨50505091790173618631925091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67340122386898158175900121 50505091790173618631925091)
                  ·
                    refine ⟨75757637685260427947887637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50505091790173618631925091 75757637685260427947887637)
                    ·
                      refine ⟨3551139266496582560057233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75757637685260427947887637 3551139266496582560057233)
                      ·
                        rfl

theorem cell23_6915819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_6915819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915819 prefixEnd_6915819 := by exact prefixLift 6915819
  have htrace : WordTrace (prefixWord ++ tailWord_6915819) baseStart_6915819 baseEnd_6915819 := by
    simpa [prefixWord, tailWord_6915819, baseEnd_6915819] using wordTrace_append hprefix tailTrace_6915819
  have hstable : (prefixWord ++ tailWord_6915819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915819).length < 2 ^ (prefixWord ++ tailWord_6915819).sum := by decide
  have hdescent : baseEnd_6915819 < baseStart_6915819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915849 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_6915849 : Nat := 118140960795 + 6915849 * 2 ^ 59
def prefixEnd_6915849 : Nat := 4983230072969 + 3 ^ 40 * 6915849 * 2
def baseEnd_6915849 : Nat := 3551154670916217442682095

theorem tailTrace_6915849 : CollatzResearch.WordTrace tailWord_6915849 prefixEnd_6915849 3551154670916217442682095 := by
  unfold tailWord_6915849
  simp only [CollatzResearch.WordTrace]
  refine ⟨252241735522067680819510601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168161157014711787213007067 252241735522067680819510601)
  ·
    refine ⟨189181301641550760614632951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252241735522067680819510601 189181301641550760614632951)
    ·
      refine ⟨283771952462326140921949427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189181301641550760614632951 283771952462326140921949427)
      ·
        refine ⟨425657928693489211382924141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283771952462326140921949427 425657928693489211382924141)
        ·
          refine ⟨159621723260058454268596553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425657928693489211382924141 159621723260058454268596553)
          ·
            refine ⟨119716292445043840701447415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159621723260058454268596553 119716292445043840701447415)
            ·
              refine ⟨179574438667565761052171123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119716292445043840701447415 179574438667565761052171123)
              ·
                refine ⟨269361658001348641578256685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179574438667565761052171123 269361658001348641578256685)
                ·
                  refine ⟨101010621750505740591846257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269361658001348641578256685 101010621750505740591846257)
                  ·
                    refine ⟨75757966312879305443884693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101010621750505740591846257 75757966312879305443884693)
                    ·
                      refine ⟨3551154670916217442682095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75757966312879305443884693 3551154670916217442682095)
                      ·
                        rfl

theorem cell23_6915849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_6915849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915849 prefixEnd_6915849 := by exact prefixLift 6915849
  have htrace : WordTrace (prefixWord ++ tailWord_6915849) baseStart_6915849 baseEnd_6915849 := by
    simpa [prefixWord, tailWord_6915849, baseEnd_6915849] using wordTrace_append hprefix tailTrace_6915849
  have hstable : (prefixWord ++ tailWord_6915849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915849).length < 2 ^ (prefixWord ++ tailWord_6915849).sum := by decide
  have hdescent : baseEnd_6915849 < baseStart_6915849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915890 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_6915890 : Nat := 118140960795 + 6915890 * 2 ^ 59
def prefixEnd_6915890 : Nat := 4983230072969 + 3 ^ 40 * 6915890 * 2
def baseEnd_6915890 : Nat := 3551175723623051782269407

theorem tailTrace_6915890 : CollatzResearch.WordTrace tailWord_6915890 prefixEnd_6915890 3551175723623051782269407 := by
  unfold tailWord_6915890
  simp only [CollatzResearch.WordTrace]
  refine ⟨63060807728729786205438281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168162153943279429881168749 63060807728729786205438281)
  ·
    refine ⟨47295605796547339654078711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63060807728729786205438281 47295605796547339654078711)
    ·
      refine ⟨70943408694821009481118067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47295605796547339654078711 70943408694821009481118067)
      ·
        refine ⟨106415113042231514221677101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70943408694821009481118067 106415113042231514221677101)
        ·
          refine ⟨39905667390836817833128913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106415113042231514221677101 39905667390836817833128913)
          ·
            refine ⟨29929250543127613374846685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39905667390836817833128913 29929250543127613374846685)
            ·
              refine ⟨11223468953672855015567507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29929250543127613374846685 11223468953672855015567507)
              ·
                refine ⟨16835203430509282523351261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11223468953672855015567507 16835203430509282523351261)
                ·
                  refine ⟨6313201286440980946256723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16835203430509282523351261 6313201286440980946256723)
                  ·
                    refine ⟨9469801929661471419385085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6313201286440980946256723 9469801929661471419385085)
                    ·
                      refine ⟨3551175723623051782269407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9469801929661471419385085 3551175723623051782269407)
                      ·
                        rfl

theorem cell23_6915890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_6915890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915890 prefixEnd_6915890 := by exact prefixLift 6915890
  have htrace : WordTrace (prefixWord ++ tailWord_6915890) baseStart_6915890 baseEnd_6915890 := by
    simpa [prefixWord, tailWord_6915890, baseEnd_6915890] using wordTrace_append hprefix tailTrace_6915890
  have hstable : (prefixWord ++ tailWord_6915890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915890).length < 2 ^ (prefixWord ++ tailWord_6915890).sum := by decide
  have hdescent : baseEnd_6915890 < baseStart_6915890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915897 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 6]
def baseStart_6915897 : Nat := 118140960795 + 6915897 * 2 ^ 59
def prefixEnd_6915897 : Nat := 4983230072969 + 3 ^ 40 * 6915897 * 2
def baseEnd_6915897 : Nat := 394575479776403694986875

theorem tailTrace_6915897 : CollatzResearch.WordTrace tailWord_6915897 prefixEnd_6915897 394575479776403694986875 := by
  unfold tailWord_6915897
  simp only [CollatzResearch.WordTrace]
  refine ⟨252243486225893785017257945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168162324150595856678171963 252243486225893785017257945)
  ·
    refine ⟨189182614669420338762943459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252243486225893785017257945 189182614669420338762943459)
    ·
      refine ⟨283773922004130508144415189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189182614669420338762943459 283773922004130508144415189)
      ·
        refine ⟨6650951296971808784634731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 283773922004130508144415189 6650951296971808784634731)
        ·
          refine ⟨9976426945457713176952097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6650951296971808784634731 9976426945457713176952097)
          ·
            refine ⟨7482320209093284882714073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9976426945457713176952097 7482320209093284882714073)
            ·
              refine ⟨5611740156819963662035555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7482320209093284882714073 5611740156819963662035555)
              ·
                refine ⟨8417610235229945493053333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611740156819963662035555 8417610235229945493053333)
                ·
                  refine ⟨394575479776403694986875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8417610235229945493053333 394575479776403694986875)
                  ·
                    rfl

theorem cell23_6915897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 6].length) (baseStart_6915897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915897 prefixEnd_6915897 := by exact prefixLift 6915897
  have htrace : WordTrace (prefixWord ++ tailWord_6915897) baseStart_6915897 baseEnd_6915897 := by
    simpa [prefixWord, tailWord_6915897, baseEnd_6915897] using wordTrace_append hprefix tailTrace_6915897
  have hstable : (prefixWord ++ tailWord_6915897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915897).length < 2 ^ (prefixWord ++ tailWord_6915897).sum := by decide
  have hdescent : baseEnd_6915897 < baseStart_6915897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915917 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_6915917 : Nat := 118140960795 + 6915917 * 2 ^ 59
def prefixEnd_6915917 : Nat := 4983230072969 + 3 ^ 40 * 6915917 * 2
def baseEnd_6915917 : Nat := 3551189587600723176631783

theorem tailTrace_6915917 : CollatzResearch.WordTrace tailWord_6915917 prefixEnd_6915917 3551189587600723176631783 := by
  unfold tailWord_6915917
  simp only [CollatzResearch.WordTrace]
  refine ⟨252244215685821328432986005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168162810457214218955324003 252244215685821328432986005)
  ·
    refine ⟨11823947610272874770296219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 252244215685821328432986005 11823947610272874770296219)
    ·
      refine ⟨17735921415409312155444329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11823947610272874770296219 17735921415409312155444329)
      ·
        refine ⟨13301941061556984116583247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17735921415409312155444329 13301941061556984116583247)
        ·
          refine ⟨19952911592335476174874871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13301941061556984116583247 19952911592335476174874871)
          ·
            refine ⟨29929367388503214262312307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19952911592335476174874871 29929367388503214262312307)
            ·
              refine ⟨44894051082754821393468461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29929367388503214262312307 44894051082754821393468461)
              ·
                refine ⟨16835269156033058022550673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44894051082754821393468461 16835269156033058022550673)
                ·
                  refine ⟨12626451867024793516913005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16835269156033058022550673 12626451867024793516913005)
                  ·
                    refine ⟨4734919450134297568842377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12626451867024793516913005 4734919450134297568842377)
                    ·
                      refine ⟨3551189587600723176631783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4734919450134297568842377 3551189587600723176631783)
                      ·
                        rfl

theorem cell23_6915917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_6915917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915917 prefixEnd_6915917 := by exact prefixLift 6915917
  have htrace : WordTrace (prefixWord ++ tailWord_6915917) baseStart_6915917 baseEnd_6915917 := by
    simpa [prefixWord, tailWord_6915917, baseEnd_6915917] using wordTrace_append hprefix tailTrace_6915917
  have hstable : (prefixWord ++ tailWord_6915917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915917).length < 2 ^ (prefixWord ++ tailWord_6915917).sum := by decide
  have hdescent : baseEnd_6915917 < baseStart_6915917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915930 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4]
def baseStart_6915930 : Nat := 118140960795 + 6915930 * 2 ^ 59
def prefixEnd_6915930 : Nat := 4983230072969 + 3 ^ 40 * 6915930 * 2
def baseEnd_6915930 : Nat := 3551196262849231625769223

theorem tailTrace_6915930 : CollatzResearch.WordTrace tailWord_6915930 prefixEnd_6915930 3551196262849231625769223 := by
  unfold tailWord_6915930
  simp only [CollatzResearch.WordTrace]
  refine ⟨63061172458693557913302311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168163126556516154435472829 63061172458693557913302311)
  ·
    refine ⟨94591758688040336869953467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63061172458693557913302311 94591758688040336869953467)
    ·
      refine ⟨141887638032060505304930201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94591758688040336869953467 141887638032060505304930201)
      ·
        refine ⟨106415728524045378978697651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141887638032060505304930201 106415728524045378978697651)
        ·
          refine ⟨159623592786068068468046477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106415728524045378978697651 159623592786068068468046477)
          ·
            refine ⟨59858847294775525675517429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159623592786068068468046477 59858847294775525675517429)
            ·
              refine ⟨5611766933885205532079759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59858847294775525675517429 5611766933885205532079759)
              ·
                refine ⟨8417650400827808298119639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611766933885205532079759 8417650400827808298119639)
                ·
                  refine ⟨12626475601241712447179459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8417650400827808298119639 12626475601241712447179459)
                  ·
                    refine ⟨18939713401862568670769189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12626475601241712447179459 18939713401862568670769189)
                    ·
                      refine ⟨3551196262849231625769223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18939713401862568670769189 3551196262849231625769223)
                      ·
                        rfl

theorem cell23_6915930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_6915930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915930 prefixEnd_6915930 := by exact prefixLift 6915930
  have htrace : WordTrace (prefixWord ++ tailWord_6915930) baseStart_6915930 baseEnd_6915930 := by
    simpa [prefixWord, tailWord_6915930, baseEnd_6915930] using wordTrace_append hprefix tailTrace_6915930
  have hstable : (prefixWord ++ tailWord_6915930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915930).length < 2 ^ (prefixWord ++ tailWord_6915930).sum := by decide
  have hdescent : baseEnd_6915930 < baseStart_6915930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915950 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_6915950 : Nat := 118140960795 + 6915950 * 2 ^ 59
def prefixEnd_6915950 : Nat := 4983230072969 + 3 ^ 40 * 6915950 * 2
def baseEnd_6915950 : Nat := 3551206532462321547519131

theorem tailTrace_6915950 : CollatzResearch.WordTrace tailWord_6915950 prefixEnd_6915950 3551206532462321547519131 := by
  unfold tailWord_6915950
  simp only [CollatzResearch.WordTrace]
  refine ⟨31530677411837721883617163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168163612863134516712624869 31530677411837721883617163)
  ·
    refine ⟨47296016117756582825425745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31530677411837721883617163 47296016117756582825425745)
    ·
      refine ⟨35472012088317437119069309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47296016117756582825425745 35472012088317437119069309)
      ·
        refine ⟨13302004533119038919650991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35472012088317437119069309 13302004533119038919650991)
        ·
          refine ⟨19953006799678558379476487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13302004533119038919650991 19953006799678558379476487)
          ·
            refine ⟨29929510199517837569214731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19953006799678558379476487 29929510199517837569214731)
            ·
              refine ⟨44894265299276756353822097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29929510199517837569214731 44894265299276756353822097)
              ·
                refine ⟨33670698974457567265366573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44894265299276756353822097 33670698974457567265366573)
                ·
                  refine ⟨12626512115421587724512465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33670698974457567265366573 12626512115421587724512465)
                  ·
                    refine ⟨9469884086566190793384349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12626512115421587724512465 9469884086566190793384349)
                    ·
                      refine ⟨3551206532462321547519131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9469884086566190793384349 3551206532462321547519131)
                      ·
                        rfl

theorem cell23_6915950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_6915950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915950 prefixEnd_6915950 := by exact prefixLift 6915950
  have htrace : WordTrace (prefixWord ++ tailWord_6915950) baseStart_6915950 baseEnd_6915950 := by
    simpa [prefixWord, tailWord_6915950, baseEnd_6915950] using wordTrace_append hprefix tailTrace_6915950
  have hstable : (prefixWord ++ tailWord_6915950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915950).length < 2 ^ (prefixWord ++ tailWord_6915950).sum := by decide
  have hdescent : baseEnd_6915950 < baseStart_6915950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915963 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 6, 1, 3]
def baseStart_6915963 : Nat := 118140960795 + 6915963 * 2 ^ 59
def prefixEnd_6915963 : Nat := 4983230072969 + 3 ^ 40 * 6915963 * 2
def baseEnd_6915963 : Nat := 3551213207710829996656571

theorem tailTrace_6915963 : CollatzResearch.WordTrace tailWord_6915963 prefixEnd_6915963 3551213207710829996656571 := by
  unfold tailWord_6915963
  simp only [CollatzResearch.WordTrace]
  refine ⟨252245893443654678289160543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168163928962436452192773695 252245893443654678289160543)
  ·
    refine ⟨378368840165482017433740815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252245893443654678289160543 378368840165482017433740815)
    ·
      refine ⟨567553260248223026150611223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378368840165482017433740815 567553260248223026150611223)
      ·
        refine ⟨851329890372334539225916835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567553260248223026150611223 851329890372334539225916835)
        ·
          refine ⟨1276994835558501808838875253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851329890372334539225916835 1276994835558501808838875253)
          ·
            refine ⟨119718265833609544578644555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1276994835558501808838875253 119718265833609544578644555)
            ·
              refine ⟨179577398750414316867966833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119718265833609544578644555 179577398750414316867966833)
              ·
                refine ⟨134683049062810737650975125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179577398750414316867966833 134683049062810737650975125)
                ·
                  refine ⟨6313267924819253327389459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134683049062810737650975125 6313267924819253327389459)
                  ·
                    refine ⟨9469901887228879991084189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6313267924819253327389459 9469901887228879991084189)
                    ·
                      refine ⟨3551213207710829996656571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9469901887228879991084189 3551213207710829996656571)
                      ·
                        rfl

theorem cell23_6915963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 1, 3].length) (baseStart_6915963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915963 prefixEnd_6915963 := by exact prefixLift 6915963
  have htrace : WordTrace (prefixWord ++ tailWord_6915963) baseStart_6915963 baseEnd_6915963 := by
    simpa [prefixWord, tailWord_6915963, baseEnd_6915963] using wordTrace_append hprefix tailTrace_6915963
  have hstable : (prefixWord ++ tailWord_6915963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915963).length < 2 ^ (prefixWord ++ tailWord_6915963).sum := by decide
  have hdescent : baseEnd_6915963 < baseStart_6915963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6915997 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_6915997 : Nat := 118140960795 + 6915997 * 2 ^ 59
def prefixEnd_6915997 : Nat := 4983230072969 + 3 ^ 40 * 6915997 * 2
def baseEnd_6915997 : Nat := 3551230666053082863631415

theorem tailTrace_6915997 : CollatzResearch.WordTrace tailWord_6915997 prefixEnd_6915997 3551230666053082863631415 := by
  unfold tailWord_6915997
  simp only [CollatzResearch.WordTrace]
  refine ⟨252247133525531502095898245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168164755683687668063932163 252247133525531502095898245)
  ·
    refine ⟨47296337536037156642980921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252247133525531502095898245 47296337536037156642980921)
    ·
      refine ⟨35472253152027867482235691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47296337536037156642980921 35472253152027867482235691)
      ·
        refine ⟨53208379728041801223353537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35472253152027867482235691 53208379728041801223353537)
        ·
          refine ⟨39906284796031350917515153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53208379728041801223353537 39906284796031350917515153)
          ·
            refine ⟨29929713597023513188136365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39906284796031350917515153 29929713597023513188136365)
            ·
              refine ⟨11223642598883817445551137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29929713597023513188136365 11223642598883817445551137)
              ·
                refine ⟨8417731949162863084163353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11223642598883817445551137 8417731949162863084163353)
                ·
                  refine ⟨6313298961872147313122515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8417731949162863084163353 6313298961872147313122515)
                  ·
                    refine ⟨9469948442808220969683773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6313298961872147313122515 9469948442808220969683773)
                    ·
                      refine ⟨3551230666053082863631415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9469948442808220969683773 3551230666053082863631415)
                      ·
                        rfl

theorem cell23_6915997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_6915997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6915997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6915997 prefixEnd_6915997 := by exact prefixLift 6915997
  have htrace : WordTrace (prefixWord ++ tailWord_6915997) baseStart_6915997 baseEnd_6915997 := by
    simpa [prefixWord, tailWord_6915997, baseEnd_6915997] using wordTrace_append hprefix tailTrace_6915997
  have hstable : (prefixWord ++ tailWord_6915997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6915997).length < 2 ^ (prefixWord ++ tailWord_6915997).sum := by decide
  have hdescent : baseEnd_6915997 < baseStart_6915997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6915997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916026 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 9]
def baseStart_6916026 : Nat := 118140960795 + 6916026 * 2 ^ 59
def prefixEnd_6916026 : Nat := 4983230072969 + 3 ^ 40 * 6916026 * 2
def baseEnd_6916026 : Nat := 394582839665784805574309

theorem tailTrace_6916026 : CollatzResearch.WordTrace tailWord_6916026 prefixEnd_6916026 394582839665784805574309 := by
  unfold tailWord_6916026
  simp only [CollatzResearch.WordTrace]
  refine ⟨63062047810606610012175983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168165460828284293365802621 63062047810606610012175983)
  ·
    refine ⟨94593071715909915018263975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63062047810606610012175983 94593071715909915018263975)
    ·
      refine ⟨141889607573864872527395963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94593071715909915018263975 141889607573864872527395963)
      ·
        refine ⟨212834411360797308791093945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141889607573864872527395963 212834411360797308791093945)
        ·
          refine ⟨159625808520597981593320459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212834411360797308791093945 159625808520597981593320459)
          ·
            refine ⟨239438712780896972389980689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159625808520597981593320459 239438712780896972389980689)
            ·
              refine ⟨179579034585672729292485517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239438712780896972389980689 179579034585672729292485517)
              ·
                refine ⟨67342137969627273484682069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179579034585672729292485517 67342137969627273484682069)
                ·
                  refine ⟨394582839665784805574309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67342137969627273484682069 394582839665784805574309)
                  ·
                    rfl

theorem cell23_6916026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_6916026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916026 prefixEnd_6916026 := by exact prefixLift 6916026
  have htrace : WordTrace (prefixWord ++ tailWord_6916026) baseStart_6916026 baseEnd_6916026 := by
    simpa [prefixWord, tailWord_6916026, baseEnd_6916026] using wordTrace_append hprefix tailTrace_6916026
  have hstable : (prefixWord ++ tailWord_6916026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916026).length < 2 ^ (prefixWord ++ tailWord_6916026).sum := by decide
  have hdescent : baseEnd_6916026 < baseStart_6916026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916093 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_6916093 : Nat := 118140960795 + 6916093 * 2 ^ 59
def prefixEnd_6916093 : Nat := 4983230072969 + 3 ^ 40 * 6916093 * 2
def baseEnd_6916093 : Nat := 3551279960195914488030973

theorem tailTrace_6916093 : CollatzResearch.WordTrace tailWord_6916093 prefixEnd_6916093 3551279960195914488030973 := by
  unfold tailWord_6916093
  simp only [CollatzResearch.WordTrace]
  refine ⟨252250634933183710491392933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168167089955455806994261955 252250634933183710491392933)
  ·
    refine ⟨47296994049971945717136175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252250634933183710491392933 47296994049971945717136175)
    ·
      refine ⟨70945491074957918575704263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47296994049971945717136175 70945491074957918575704263)
      ·
        refine ⟨106418236612436877863556395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70945491074957918575704263 106418236612436877863556395)
        ·
          refine ⟨159627354918655316795334593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106418236612436877863556395 159627354918655316795334593)
          ·
            refine ⟨119720516188991487596500945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159627354918655316795334593 119720516188991487596500945)
            ·
              refine ⟨89790387141743615697375709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119720516188991487596500945 89790387141743615697375709)
              ·
                refine ⟨33671395178153855886515891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89790387141743615697375709 33671395178153855886515891)
                ·
                  refine ⟨50507092767230783829773837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33671395178153855886515891 50507092767230783829773837)
                  ·
                    refine ⟨18940159787711543936165189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50507092767230783829773837 18940159787711543936165189)
                    ·
                      refine ⟨3551279960195914488030973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18940159787711543936165189 3551279960195914488030973)
                      ·
                        rfl

theorem cell23_6916093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_6916093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916093 prefixEnd_6916093 := by exact prefixLift 6916093
  have htrace : WordTrace (prefixWord ++ tailWord_6916093) baseStart_6916093 baseEnd_6916093 := by
    simpa [prefixWord, tailWord_6916093, baseEnd_6916093] using wordTrace_append hprefix tailTrace_6916093
  have hstable : (prefixWord ++ tailWord_6916093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916093).length < 2 ^ (prefixWord ++ tailWord_6916093).sum := by decide
  have hdescent : baseEnd_6916093 < baseStart_6916093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916110 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_6916110 : Nat := 118140960795 + 6916110 * 2 ^ 59
def prefixEnd_6916110 : Nat := 4983230072969 + 3 ^ 40 * 6916110 * 2
def baseEnd_6916110 : Nat := 3551288689367040921518395

theorem tailTrace_6916110 : CollatzResearch.WordTrace tailWord_6916110 prefixEnd_6916110 3551288689367040921518395 := by
  unfold tailWord_6916110
  simp only [CollatzResearch.WordTrace]
  refine ⟨31531406871765265299345223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168167503316081414929841189 31531406871765265299345223)
  ·
    refine ⟨47297110307647897949017835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31531406871765265299345223 47297110307647897949017835)
    ·
      refine ⟨70945665461471846923526753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47297110307647897949017835 70945665461471846923526753)
      ·
        refine ⟨53209249096103885192645065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70945665461471846923526753 53209249096103885192645065)
        ·
          refine ⟨39906936822077913894483799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53209249096103885192645065 39906936822077913894483799)
          ·
            refine ⟨59860405233116870841725699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39906936822077913894483799 59860405233116870841725699)
            ·
              refine ⟨89790607849675306262588549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59860405233116870841725699 89790607849675306262588549)
              ·
                refine ⟨16835738971814119924235353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89790607849675306262588549 16835738971814119924235353)
                ·
                  refine ⟨12626804228860589943176515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16835738971814119924235353 12626804228860589943176515)
                  ·
                    refine ⟨18940206343290884914764773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12626804228860589943176515 18940206343290884914764773)
                    ·
                      refine ⟨3551288689367040921518395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18940206343290884914764773 3551288689367040921518395)
                      ·
                        rfl

theorem cell23_6916110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_6916110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916110 prefixEnd_6916110 := by exact prefixLift 6916110
  have htrace : WordTrace (prefixWord ++ tailWord_6916110) baseStart_6916110 baseEnd_6916110 := by
    simpa [prefixWord, tailWord_6916110, baseEnd_6916110] using wordTrace_append hprefix tailTrace_6916110
  have hstable : (prefixWord ++ tailWord_6916110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916110).length < 2 ^ (prefixWord ++ tailWord_6916110).sum := by decide
  have hdescent : baseEnd_6916110 < baseStart_6916110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916113 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 3]
def baseStart_6916113 : Nat := 118140960795 + 6916113 * 2 ^ 59
def prefixEnd_6916113 : Nat := 4983230072969 + 3 ^ 40 * 6916113 * 2
def baseEnd_6916113 : Nat := 3551290229809004409780881

theorem tailTrace_6916113 : CollatzResearch.WordTrace tailWord_6916113 prefixEnd_6916113 3551290229809004409780881 := by
  unfold tailWord_6916113
  simp only [CollatzResearch.WordTrace]
  refine ⟨252251364393111253907120993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168167576262074169271413995 252251364393111253907120993)
  ·
    refine ⟨189188523294833440430340745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252251364393111253907120993 189188523294833440430340745)
    ·
      refine ⟨141891392471125080322755559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189188523294833440430340745 141891392471125080322755559)
      ·
        refine ⟨212837088706687620484133339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141891392471125080322755559 212837088706687620484133339)
        ·
          refine ⟨319255633060031430726200009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212837088706687620484133339 319255633060031430726200009)
          ·
            refine ⟨239441724795023573044650007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319255633060031430726200009 239441724795023573044650007)
            ·
              refine ⟨359162587192535359566975011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239441724795023573044650007 359162587192535359566975011)
              ·
                refine ⟨538743880788803039350462517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359162587192535359566975011 538743880788803039350462517)
                ·
                  refine ⟨50507238823950284939105861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 538743880788803039350462517 50507238823950284939105861)
                  ·
                    refine ⟨9470107279490678426082349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50507238823950284939105861 9470107279490678426082349)
                    ·
                      refine ⟨3551290229809004409780881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9470107279490678426082349 3551290229809004409780881)
                      ·
                        rfl

theorem cell23_6916113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_6916113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916113 prefixEnd_6916113 := by exact prefixLift 6916113
  have htrace : WordTrace (prefixWord ++ tailWord_6916113) baseStart_6916113 baseEnd_6916113 := by
    simpa [prefixWord, tailWord_6916113, baseEnd_6916113] using wordTrace_append hprefix tailTrace_6916113
  have hstable : (prefixWord ++ tailWord_6916113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916113).length < 2 ^ (prefixWord ++ tailWord_6916113).sum := by decide
  have hdescent : baseEnd_6916113 < baseStart_6916113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916120 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 3, 4]
def baseStart_6916120 : Nat := 118140960795 + 6916120 * 2 ^ 59
def prefixEnd_6916120 : Nat := 4983230072969 + 3 ^ 40 * 6916120 * 2
def baseEnd_6916120 : Nat := 1183764608057861960797783

theorem tailTrace_6916120 : CollatzResearch.WordTrace tailWord_6916120 prefixEnd_6916120 1183764608057861960797783 := by
  unfold tailWord_6916120
  simp only [CollatzResearch.WordTrace]
  refine ⟨126125809852042947051312907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168167746469390596068417209 126125809852042947051312907)
  ·
    refine ⟨189188714778064420576969361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126125809852042947051312907 189188714778064420576969361)
    ·
      refine ⟨141891536083548315432727021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189188714778064420576969361 141891536083548315432727021)
      ·
        refine ⟨53209326031330618287272633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141891536083548315432727021 53209326031330618287272633)
        ·
          refine ⟨39906994523497963715454475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53209326031330618287272633 39906994523497963715454475)
          ·
            refine ⟨59860491785246945573181713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39906994523497963715454475 59860491785246945573181713)
            ·
              refine ⟨44895368838935209179886285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59860491785246945573181713 44895368838935209179886285)
              ·
                refine ⟨16835763314600703442457357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44895368838935209179886285 16835763314600703442457357)
                ·
                  refine ⟨6313411242975263790921509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16835763314600703442457357 6313411242975263790921509)
                  ·
                    refine ⟨1183764608057861960797783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6313411242975263790921509 1183764608057861960797783)
                    ·
                      rfl

theorem cell23_6916120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_6916120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916120 prefixEnd_6916120 := by exact prefixLift 6916120
  have htrace : WordTrace (prefixWord ++ tailWord_6916120) baseStart_6916120 baseEnd_6916120 := by
    simpa [prefixWord, tailWord_6916120, baseEnd_6916120] using wordTrace_append hprefix tailTrace_6916120
  have hstable : (prefixWord ++ tailWord_6916120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916120).length < 2 ^ (prefixWord ++ tailWord_6916120).sum := by decide
  have hdescent : baseEnd_6916120 < baseStart_6916120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916130 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_6916130 : Nat := 118140960795 + 6916130 * 2 ^ 59
def prefixEnd_6916130 : Nat := 4983230072969 + 3 ^ 40 * 6916130 * 2
def baseEnd_6916130 : Nat := 3551298958980130843268303

theorem tailTrace_6916130 : CollatzResearch.WordTrace tailWord_6916130 prefixEnd_6916130 3551298958980130843268303 := by
  unfold tailWord_6916130
  simp only [CollatzResearch.WordTrace]
  refine ⟨63062996108512416452622461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168167989622699777206993229 63062996108512416452622461)
  ·
    refine ⟨23648623540692156169733423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63062996108512416452622461 23648623540692156169733423)
    ·
      refine ⟨35472935311038234254600135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23648623540692156169733423 35472935311038234254600135)
      ·
        refine ⟨53209402966557351381900203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35472935311038234254600135 53209402966557351381900203)
        ·
          refine ⟨79814104449836027072850305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53209402966557351381900203 79814104449836027072850305)
          ·
            refine ⟨59860578337377020304637729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79814104449836027072850305 59860578337377020304637729)
            ·
              refine ⟨44895433753032765228478297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59860578337377020304637729 44895433753032765228478297)
              ·
                refine ⟨33671575314774573921358723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44895433753032765228478297 33671575314774573921358723)
                ·
                  refine ⟨50507362972161860882038085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33671575314774573921358723 50507362972161860882038085)
                  ·
                    refine ⟨9470130557280348915382141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50507362972161860882038085 9470130557280348915382141)
                    ·
                      refine ⟨3551298958980130843268303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9470130557280348915382141 3551298958980130843268303)
                      ·
                        rfl

theorem cell23_6916130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_6916130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916130 prefixEnd_6916130 := by exact prefixLift 6916130
  have htrace : WordTrace (prefixWord ++ tailWord_6916130) baseStart_6916130 baseEnd_6916130 := by
    simpa [prefixWord, tailWord_6916130, baseEnd_6916130] using wordTrace_append hprefix tailTrace_6916130
  have hstable : (prefixWord ++ tailWord_6916130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916130).length < 2 ^ (prefixWord ++ tailWord_6916130).sum := by decide
  have hdescent : baseEnd_6916130 < baseStart_6916130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916143 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 3]
def baseStart_6916143 : Nat := 118140960795 + 6916143 * 2 ^ 59
def prefixEnd_6916143 : Nat := 4983230072969 + 3 ^ 40 * 6916143 * 2
def baseEnd_6916143 : Nat := 3551305634228639292405743

theorem tailTrace_6916143 : CollatzResearch.WordTrace tailWord_6916143 prefixEnd_6916143 3551305634228639292405743 := by
  unfold tailWord_6916143
  simp only [CollatzResearch.WordTrace]
  refine ⟨252252458583002569030713083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168168305722001712687142055 252252458583002569030713083)
  ·
    refine ⟨378378687874503853546069625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252252458583002569030713083 378378687874503853546069625)
    ·
      refine ⟨283784015905877890159552219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378378687874503853546069625 283784015905877890159552219)
      ·
        refine ⟨425676023858816835239328329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283784015905877890159552219 425676023858816835239328329)
        ·
          refine ⟨319257017894112626429496247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425676023858816835239328329 319257017894112626429496247)
          ·
            refine ⟨478885526841168939644244371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319257017894112626429496247 478885526841168939644244371)
            ·
              refine ⟨718328290261753409466366557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478885526841168939644244371 718328290261753409466366557)
              ·
                refine ⟨269373108848157528549887459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 718328290261753409466366557 269373108848157528549887459)
                ·
                  refine ⟨404059663272236292824831189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269373108848157528549887459 404059663272236292824831189)
                  ·
                    refine ⟨9470148357943038113081981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 404059663272236292824831189 9470148357943038113081981)
                    ·
                      refine ⟨3551305634228639292405743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9470148357943038113081981 3551305634228639292405743)
                      ·
                        rfl

theorem cell23_6916143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 3].length) (baseStart_6916143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916143 prefixEnd_6916143 := by exact prefixLift 6916143
  have htrace : WordTrace (prefixWord ++ tailWord_6916143) baseStart_6916143 baseEnd_6916143 := by
    simpa [prefixWord, tailWord_6916143, baseEnd_6916143] using wordTrace_append hprefix tailTrace_6916143
  have hstable : (prefixWord ++ tailWord_6916143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916143).length < 2 ^ (prefixWord ++ tailWord_6916143).sum := by decide
  have hdescent : baseEnd_6916143 < baseStart_6916143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916150 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_6916150 : Nat := 118140960795 + 6916150 * 2 ^ 59
def prefixEnd_6916150 : Nat := 4983230072969 + 3 ^ 40 * 6916150 * 2
def baseEnd_6916150 : Nat := 394589914288135640557579

theorem tailTrace_6916150 : CollatzResearch.WordTrace tailWord_6916150 prefixEnd_6916150 394589914288135640557579 := by
  unfold tailWord_6916150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15765794618373575576638619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168168475929318139484145269 15765794618373575576638619)
  ·
    refine ⟨23648691927560363364957929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15765794618373575576638619 23648691927560363364957929)
    ·
      refine ⟨17736518945670272523718447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23648691927560363364957929 17736518945670272523718447)
      ·
        refine ⟨26604778418505408785577671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17736518945670272523718447 26604778418505408785577671)
        ·
          refine ⟨39907167627758113178366507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26604778418505408785577671 39907167627758113178366507)
          ·
            refine ⟨59860751441637169767549761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39907167627758113178366507 59860751441637169767549761)
            ·
              refine ⟨44895563581227877325662321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59860751441637169767549761 44895563581227877325662321)
              ·
                refine ⟨33671672685920907994246741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44895563581227877325662321 33671672685920907994246741)
                ·
                  refine ⟨394589914288135640557579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33671672685920907994246741 394589914288135640557579)
                  ·
                    rfl

theorem cell23_6916150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_6916150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916150 prefixEnd_6916150 := by exact prefixLift 6916150
  have htrace : WordTrace (prefixWord ++ tailWord_6916150) baseStart_6916150 baseEnd_6916150 := by
    simpa [prefixWord, tailWord_6916150, baseEnd_6916150] using wordTrace_append hprefix tailTrace_6916150
  have hstable : (prefixWord ++ tailWord_6916150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916150).length < 2 ^ (prefixWord ++ tailWord_6916150).sum := by decide
  have hdescent : baseEnd_6916150 < baseStart_6916150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916163 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 5, 5]
def baseStart_6916163 : Nat := 118140960795 + 6916163 * 2 ^ 59
def prefixEnd_6916163 : Nat := 4983230072969 + 3 ^ 40 * 6916163 * 2
def baseEnd_6916163 : Nat := 1183771967947243071385217

theorem tailTrace_6916163 : CollatzResearch.WordTrace tailWord_6916163 prefixEnd_6916163 1183771967947243071385217 := by
  unfold tailWord_6916163
  simp only [CollatzResearch.WordTrace]
  refine ⟨252253188042930112446441143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168168792028620074964294095 252253188042930112446441143)
  ·
    refine ⟨378379782064395168669661715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252253188042930112446441143 378379782064395168669661715)
    ·
      refine ⟨567569673096592753004492573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378379782064395168669661715 567569673096592753004492573)
      ·
        refine ⟨212838627411222282376684715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 567569673096592753004492573 212838627411222282376684715)
        ·
          refine ⟨319257941116833423565027073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212838627411222282376684715 319257941116833423565027073)
          ·
            refine ⟨239443455837625067673770305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319257941116833423565027073 239443455837625067673770305)
            ·
              refine ⟨179582591878218800755327729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239443455837625067673770305 179582591878218800755327729)
              ·
                refine ⟨134686943908664100566495797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179582591878218800755327729 134686943908664100566495797)
                ·
                  refine ⟨12626900991437259428108981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134686943908664100566495797 12626900991437259428108981)
                  ·
                    refine ⟨1183771967947243071385217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12626900991437259428108981 1183771967947243071385217)
                    ·
                      rfl

theorem cell23_6916163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 5].length) (baseStart_6916163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916163 prefixEnd_6916163 := by exact prefixLift 6916163
  have htrace : WordTrace (prefixWord ++ tailWord_6916163) baseStart_6916163 baseEnd_6916163 := by
    simpa [prefixWord, tailWord_6916163, baseEnd_6916163] using wordTrace_append hprefix tailTrace_6916163
  have hstable : (prefixWord ++ tailWord_6916163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916163).length < 2 ^ (prefixWord ++ tailWord_6916163).sum := by decide
  have hdescent : baseEnd_6916163 < baseStart_6916163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916197 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 1, 5]
def baseStart_6916197 : Nat := 118140960795 + 6916197 * 2 ^ 59
def prefixEnd_6916197 : Nat := 4983230072969 + 3 ^ 40 * 6916197 * 2
def baseEnd_6916197 : Nat := 1183777787394660693710165

theorem tailTrace_6916197 : CollatzResearch.WordTrace tailWord_6916197 prefixEnd_6916197 1183777787394660693710165 := by
  unfold tailWord_6916197
  simp only [CollatzResearch.WordTrace]
  refine ⟨252254428124806936253178845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168169618749871290835452563 252254428124806936253178845)
  ·
    refine ⟨94595410546802601094942067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252254428124806936253178845 94595410546802601094942067)
    ·
      refine ⟨141893115820203901642413101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94595410546802601094942067 141893115820203901642413101)
      ·
        refine ⟨53209918432576463115904913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141893115820203901642413101 53209918432576463115904913)
        ·
          refine ⟨39907438824432347336928685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53209918432576463115904913 39907438824432347336928685)
          ·
            refine ⟨14965289559162130251348257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39907438824432347336928685 14965289559162130251348257)
            ·
              refine ⟨11223967169371597688511193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14965289559162130251348257 11223967169371597688511193)
              ·
                refine ⟨8417975377028698266383395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11223967169371597688511193 8417975377028698266383395)
                ·
                  refine ⟨12626963065543047399575093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8417975377028698266383395 12626963065543047399575093)
                  ·
                    refine ⟨1183777787394660693710165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12626963065543047399575093 1183777787394660693710165)
                    ·
                      rfl

theorem cell23_6916197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_6916197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916197 prefixEnd_6916197 := by exact prefixLift 6916197
  have htrace : WordTrace (prefixWord ++ tailWord_6916197) baseStart_6916197 baseEnd_6916197 := by
    simpa [prefixWord, tailWord_6916197, baseEnd_6916197] using wordTrace_append hprefix tailTrace_6916197
  have hstable : (prefixWord ++ tailWord_6916197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916197).length < 2 ^ (prefixWord ++ tailWord_6916197).sum := by decide
  have hdescent : baseEnd_6916197 < baseStart_6916197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916217 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 4]
def baseStart_6916217 : Nat := 118140960795 + 6916217 * 2 ^ 59
def prefixEnd_6916217 : Nat := 4983230072969 + 3 ^ 40 * 6916217 * 2
def baseEnd_6916217 : Nat := 3551343631797072002880403

theorem tailTrace_6916217 : CollatzResearch.WordTrace tailWord_6916217 prefixEnd_6916217 3551343631797072002880403 := by
  unfold tailWord_6916217
  simp only [CollatzResearch.WordTrace]
  refine ⟨252255157584734479668906905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168170105056489653112604603 252255157584734479668906905)
  ·
    refine ⟨189191368188550859751680179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252255157584734479668906905 189191368188550859751680179)
    ·
      refine ⟨283787052282826289627520269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189191368188550859751680179 283787052282826289627520269)
      ·
        refine ⟨106420144606059858610320101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283787052282826289627520269 106420144606059858610320101)
        ·
          refine ⟨19953777113636223489435019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106420144606059858610320101 19953777113636223489435019)
          ·
            refine ⟨29930665670454335234152529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19953777113636223489435019 29930665670454335234152529)
            ·
              refine ⟨22447999252840751425614397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29930665670454335234152529 22447999252840751425614397)
              ·
                refine ⟨8417999719815281784605399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22447999252840751425614397 8417999719815281784605399)
                ·
                  refine ⟨12626999579722922676908099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8417999719815281784605399 12626999579722922676908099)
                  ·
                    refine ⟨18940499369584384015362149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12626999579722922676908099 18940499369584384015362149)
                    ·
                      refine ⟨3551343631797072002880403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18940499369584384015362149 3551343631797072002880403)
                      ·
                        rfl

theorem cell23_6916217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_6916217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916217 prefixEnd_6916217 := by exact prefixLift 6916217
  have htrace : WordTrace (prefixWord ++ tailWord_6916217) baseStart_6916217 baseEnd_6916217 := by
    simpa [prefixWord, tailWord_6916217, baseEnd_6916217] using wordTrace_append hprefix tailTrace_6916217
  have hstable : (prefixWord ++ tailWord_6916217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916217).length < 2 ^ (prefixWord ++ tailWord_6916217).sum := by decide
  have hdescent : baseEnd_6916217 < baseStart_6916217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916220 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_6916220 : Nat := 118140960795 + 6916220 * 2 ^ 59
def prefixEnd_6916220 : Nat := 4983230072969 + 3 ^ 40 * 6916220 * 2
def baseEnd_6916220 : Nat := 3551345172239035491142889

theorem tailTrace_6916220 : CollatzResearch.WordTrace tailWord_6916220 prefixEnd_6916220 3551345172239035491142889 := by
  unfold tailWord_6916220
  simp only [CollatzResearch.WordTrace]
  refine ⟨126127633501861805590633057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168170178002482407454177409 126127633501861805590633057)
  ·
    refine ⟨94595725126396354192974793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126127633501861805590633057 94595725126396354192974793)
    ·
      refine ⟨70946793844797265644731095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94595725126396354192974793 70946793844797265644731095)
      ·
        refine ⟨106420190767195898467096643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70946793844797265644731095 106420190767195898467096643)
        ·
          refine ⟨159630286150793847700644965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106420190767195898467096643 159630286150793847700644965)
          ·
            refine ⟨29930678653273846443870931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159630286150793847700644965 29930678653273846443870931)
            ·
              refine ⟨44896017979910769665806397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29930678653273846443870931 44896017979910769665806397)
              ·
                refine ⟨16836006742466538624677399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44896017979910769665806397 16836006742466538624677399)
                ·
                  refine ⟨25254010113699807937016099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16836006742466538624677399 25254010113699807937016099)
                  ·
                    refine ⟨37881015170549711905524149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25254010113699807937016099 37881015170549711905524149)
                    ·
                      refine ⟨3551345172239035491142889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37881015170549711905524149 3551345172239035491142889)
                      ·
                        rfl

theorem cell23_6916220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_6916220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916220 prefixEnd_6916220 := by exact prefixLift 6916220
  have htrace : WordTrace (prefixWord ++ tailWord_6916220) baseStart_6916220 baseEnd_6916220 := by
    simpa [prefixWord, tailWord_6916220, baseEnd_6916220] using wordTrace_append hprefix tailTrace_6916220
  have hstable : (prefixWord ++ tailWord_6916220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916220).length < 2 ^ (prefixWord ++ tailWord_6916220).sum := by decide
  have hdescent : baseEnd_6916220 < baseStart_6916220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916243 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 6]
def baseStart_6916243 : Nat := 118140960795 + 6916243 * 2 ^ 59
def prefixEnd_6916243 : Nat := 4983230072969 + 3 ^ 40 * 6916243 * 2
def baseEnd_6916243 : Nat := 3551356982294088901155283

theorem tailTrace_6916243 : CollatzResearch.WordTrace tailWord_6916243 prefixEnd_6916243 3551356982294088901155283 := by
  unfold tailWord_6916243
  simp only [CollatzResearch.WordTrace]
  refine ⟨252256105882640286109353383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168170737255093524072902255 252256105882640286109353383)
  ·
    refine ⟨378384158823960429164030075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252256105882640286109353383 378384158823960429164030075)
    ·
      refine ⟨567576238235940643746045113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378384158823960429164030075 567576238235940643746045113)
      ·
        refine ⟨425682178676955482809533835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567576238235940643746045113 425682178676955482809533835)
        ·
          refine ⟨638523268015433224214300753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425682178676955482809533835 638523268015433224214300753)
          ·
            refine ⟨478892451011574918160725565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638523268015433224214300753 478892451011574918160725565)
            ·
              refine ⟨179584669129340594310272087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 478892451011574918160725565 179584669129340594310272087)
              ·
                refine ⟨269377003694010891465408131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179584669129340594310272087 269377003694010891465408131)
                ·
                  refine ⟨404065505541016337198112197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269377003694010891465408131 404065505541016337198112197)
                  ·
                    refine ⟨75762282288940563224646037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 404065505541016337198112197 75762282288940563224646037)
                    ·
                      refine ⟨3551356982294088901155283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75762282288940563224646037 3551356982294088901155283)
                      ·
                        rfl

theorem cell23_6916243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_6916243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916243 prefixEnd_6916243 := by exact prefixLift 6916243
  have htrace : WordTrace (prefixWord ++ tailWord_6916243) baseStart_6916243 baseEnd_6916243 := by
    simpa [prefixWord, tailWord_6916243, baseEnd_6916243] using wordTrace_append hprefix tailTrace_6916243
  have hstable : (prefixWord ++ tailWord_6916243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916243).length < 2 ^ (prefixWord ++ tailWord_6916243).sum := by decide
  have hdescent : baseEnd_6916243 < baseStart_6916243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916320 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 4]
def baseStart_6916320 : Nat := 118140960795 + 6916320 * 2 ^ 59
def prefixEnd_6916320 : Nat := 4983230072969 + 3 ^ 40 * 6916320 * 2
def baseEnd_6916320 : Nat := 3551396520304485099892429

theorem tailTrace_6916320 : CollatzResearch.WordTrace tailWord_6916320 prefixEnd_6916320 3551396520304485099892429 := by
  unfold tailWord_6916320
  simp only [CollatzResearch.WordTrace]
  refine ⟨126129457151680664129953207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168172609535574218839937609 126129457151680664129953207)
  ·
    refine ⟨189194185727520996194929811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126129457151680664129953207 189194185727520996194929811)
    ·
      refine ⟨283791278591281494292394717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189194185727520996194929811 283791278591281494292394717)
      ·
        refine ⟨106421729471730560359648019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283791278591281494292394717 106421729471730560359648019)
        ·
          refine ⟨159632594207595840539472029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106421729471730560359648019 159632594207595840539472029)
          ·
            refine ⟨59862222827848440202302011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159632594207595840539472029 59862222827848440202302011)
            ·
              refine ⟨89793334241772660303453017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59862222827848440202302011 89793334241772660303453017)
              ·
                refine ⟨67345000681329495227589763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89793334241772660303453017 67345000681329495227589763)
                ·
                  refine ⟨101017501021994242841384645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67345000681329495227589763 101017501021994242841384645)
                  ·
                    refine ⟨18940781441623920532759621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101017501021994242841384645 18940781441623920532759621)
                    ·
                      refine ⟨3551396520304485099892429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18940781441623920532759621 3551396520304485099892429)
                      ·
                        rfl

theorem cell23_6916320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_6916320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916320 prefixEnd_6916320 := by exact prefixLift 6916320
  have htrace : WordTrace (prefixWord ++ tailWord_6916320) baseStart_6916320 baseEnd_6916320 := by
    simpa [prefixWord, tailWord_6916320, baseEnd_6916320] using wordTrace_append hprefix tailTrace_6916320
  have hstable : (prefixWord ++ tailWord_6916320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916320).length < 2 ^ (prefixWord ++ tailWord_6916320).sum := by decide
  have hdescent : baseEnd_6916320 < baseStart_6916320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916322 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6916322 : Nat := 118140960795 + 6916322 * 2 ^ 59
def prefixEnd_6916322 : Nat := 4983230072969 + 3 ^ 40 * 6916322 * 2
def baseEnd_6916322 : Nat := 3551397547265794092067421

theorem tailTrace_6916322 : CollatzResearch.WordTrace tailWord_6916322 prefixEnd_6916322 3551397547265794092067421 := by
  unfold tailWord_6916322
  simp only [CollatzResearch.WordTrace]
  refine ⟨63064746812338520650369805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168172658166236055067652813 63064746812338520650369805)
  ·
    refine ⟨23649280054626945243888677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63064746812338520650369805 23649280054626945243888677)
    ·
      refine ⟨4434240010242552233229127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23649280054626945243888677 4434240010242552233229127)
      ·
        refine ⟨6651360015363828349843691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4434240010242552233229127 6651360015363828349843691)
        ·
          refine ⟨9977040023045742524765537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6651360015363828349843691 9977040023045742524765537)
          ·
            refine ⟨7482780017284306893574153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9977040023045742524765537 7482780017284306893574153)
            ·
              refine ⟨5612085012963230170180615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7482780017284306893574153 5612085012963230170180615)
              ·
                refine ⟨8418127519444845255270923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5612085012963230170180615 8418127519444845255270923)
                ·
                  refine ⟨12627191279167267882906385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8418127519444845255270923 12627191279167267882906385)
                  ·
                    refine ⟨9470393459375450912179789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12627191279167267882906385 9470393459375450912179789)
                    ·
                      refine ⟨3551397547265794092067421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9470393459375450912179789 3551397547265794092067421)
                      ·
                        rfl

theorem cell23_6916322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6916322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916322 prefixEnd_6916322 := by exact prefixLift 6916322
  have htrace : WordTrace (prefixWord ++ tailWord_6916322) baseStart_6916322 baseEnd_6916322 := by
    simpa [prefixWord, tailWord_6916322, baseEnd_6916322] using wordTrace_append hprefix tailTrace_6916322
  have hstable : (prefixWord ++ tailWord_6916322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916322).length < 2 ^ (prefixWord ++ tailWord_6916322).sum := by decide
  have hdescent : baseEnd_6916322 < baseStart_6916322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916324 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 4, 2, 2]
def baseStart_6916324 : Nat := 118140960795 + 6916324 * 2 ^ 59
def prefixEnd_6916324 : Nat := 4983230072969 + 3 ^ 40 * 6916324 * 2
def baseEnd_6916324 : Nat := 3551398574227103084242411

theorem tailTrace_6916324 : CollatzResearch.WordTrace tailWord_6916324 prefixEnd_6916324 3551398574227103084242411 := by
  unfold tailWord_6916324
  simp only [CollatzResearch.WordTrace]
  refine ⟨126129530097673418471526013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168172706796897891295368017 126129530097673418471526013)
  ·
    refine ⟨47298573786627531926822255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126129530097673418471526013 47298573786627531926822255)
    ·
      refine ⟨70947860679941297890233383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47298573786627531926822255 70947860679941297890233383)
      ·
        refine ⟨106421791019911946835350075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70947860679941297890233383 106421791019911946835350075)
        ·
          refine ⟨159632686529867920253025113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106421791019911946835350075 159632686529867920253025113)
          ·
            refine ⟨119724514897400940189768835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159632686529867920253025113 119724514897400940189768835)
            ·
              refine ⟨179586772346101410284653253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119724514897400940189768835 179586772346101410284653253)
              ·
                refine ⟨33672519814894014428372485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179586772346101410284653253 33672519814894014428372485)
                ·
                  refine ⟨6313597465292627705319841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33672519814894014428372485 6313597465292627705319841)
                  ·
                    refine ⟨4735198098969470778989881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6313597465292627705319841 4735198098969470778989881)
                    ·
                      refine ⟨3551398574227103084242411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735198098969470778989881 3551398574227103084242411)
                      ·
                        rfl

theorem cell23_6916324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_6916324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916324 prefixEnd_6916324 := by exact prefixLift 6916324
  have htrace : WordTrace (prefixWord ++ tailWord_6916324) baseStart_6916324 baseEnd_6916324 := by
    simpa [prefixWord, tailWord_6916324, baseEnd_6916324] using wordTrace_append hprefix tailTrace_6916324
  have hstable : (prefixWord ++ tailWord_6916324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916324).length < 2 ^ (prefixWord ++ tailWord_6916324).sum := by decide
  have hdescent : baseEnd_6916324 < baseStart_6916324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916328 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_6916328 : Nat := 118140960795 + 6916328 * 2 ^ 59
def prefixEnd_6916328 : Nat := 4983230072969 + 3 ^ 40 * 6916328 * 2
def baseEnd_6916328 : Nat := 3551400628149721068592393

theorem tailTrace_6916328 : CollatzResearch.WordTrace tailWord_6916328 prefixEnd_6916328 3551400628149721068592393 := by
  unfold tailWord_6916328
  simp only [CollatzResearch.WordTrace]
  refine ⟨126129603043666172813098819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168172804058221563750798425 126129603043666172813098819)
  ·
    refine ⟨189194404565499259219648229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126129603043666172813098819 189194404565499259219648229)
    ·
      refine ⟨35473950856031111103684043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189194404565499259219648229 35473950856031111103684043)
      ·
        refine ⟨53210926284046666655526065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35473950856031111103684043 53210926284046666655526065)
        ·
          refine ⟨39908194713034999991644549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53210926284046666655526065 39908194713034999991644549)
          ·
            refine ⟨7482786508694062498433353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39908194713034999991644549 7482786508694062498433353)
            ·
              refine ⟨5612089881520546873825015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7482786508694062498433353 5612089881520546873825015)
              ·
                refine ⟨8418134822280820310737523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5612089881520546873825015 8418134822280820310737523)
                ·
                  refine ⟨12627202233421230466106285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8418134822280820310737523 12627202233421230466106285)
                  ·
                    refine ⟨4735200837532961424789857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12627202233421230466106285 4735200837532961424789857)
                    ·
                      refine ⟨3551400628149721068592393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735200837532961424789857 3551400628149721068592393)
                      ·
                        rfl

theorem cell23_6916328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_6916328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916328 prefixEnd_6916328 := by exact prefixLift 6916328
  have htrace : WordTrace (prefixWord ++ tailWord_6916328) baseStart_6916328 baseEnd_6916328 := by
    simpa [prefixWord, tailWord_6916328, baseEnd_6916328] using wordTrace_append hprefix tailTrace_6916328
  have hstable : (prefixWord ++ tailWord_6916328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916328).length < 2 ^ (prefixWord ++ tailWord_6916328).sum := by decide
  have hdescent : baseEnd_6916328 < baseStart_6916328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916330 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 9]
def baseStart_6916330 : Nat := 118140960795 + 6916330 * 2 ^ 59
def prefixEnd_6916330 : Nat := 4983230072969 + 3 ^ 40 * 6916330 * 2
def baseEnd_6916330 : Nat := 394600183901225562307487

theorem tailTrace_6916330 : CollatzResearch.WordTrace tailWord_6916330 prefixEnd_6916330 394600183901225562307487 := by
  unfold tailWord_6916330
  simp only [CollatzResearch.WordTrace]
  refine ⟨63064819758331274991942611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168172852688883399978513629 63064819758331274991942611)
  ·
    refine ⟨94597229637496912487913917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63064819758331274991942611 94597229637496912487913917)
    ·
      refine ⟨35473961114061342182967719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94597229637496912487913917 35473961114061342182967719)
      ·
        refine ⟨53210941671092013274451579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35473961114061342182967719 53210941671092013274451579)
        ·
          refine ⟨79816412506638019911677369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53210941671092013274451579 79816412506638019911677369)
          ·
            refine ⟨59862309379978514933758027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79816412506638019911677369 59862309379978514933758027)
            ·
              refine ⟨89793464069967772400637041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59862309379978514933758027 89793464069967772400637041)
              ·
                refine ⟨67345098052475829300477781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89793464069967772400637041 67345098052475829300477781)
                ·
                  refine ⟨394600183901225562307487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67345098052475829300477781 394600183901225562307487)
                  ·
                    rfl

theorem cell23_6916330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_6916330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916330 prefixEnd_6916330 := by exact prefixLift 6916330
  have htrace : WordTrace (prefixWord ++ tailWord_6916330) baseStart_6916330 baseEnd_6916330 := by
    simpa [prefixWord, tailWord_6916330, baseEnd_6916330] using wordTrace_append hprefix tailTrace_6916330
  have hstable : (prefixWord ++ tailWord_6916330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916330).length < 2 ^ (prefixWord ++ tailWord_6916330).sum := by decide
  have hdescent : baseEnd_6916330 < baseStart_6916330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916354 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_6916354 : Nat := 118140960795 + 6916354 * 2 ^ 59
def prefixEnd_6916354 : Nat := 4983230072969 + 3 ^ 40 * 6916354 * 2
def baseEnd_6916354 : Nat := 3551413978646737966867273

theorem tailTrace_6916354 : CollatzResearch.WordTrace tailWord_6916354 prefixEnd_6916354 3551413978646737966867273 := by
  unfold tailWord_6916354
  simp only [CollatzResearch.WordTrace]
  refine ⟨63065038596309538016661029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168173436256825434711096077 63065038596309538016661029)
  ·
    refine ⟨11824694736808038378123943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63065038596309538016661029 11824694736808038378123943)
    ·
      refine ⟨17737042105212057567185915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11824694736808038378123943 17737042105212057567185915)
      ·
        refine ⟨26605563157818086350778873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17737042105212057567185915 26605563157818086350778873)
        ·
          refine ⟨19954172368363564763084155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26605563157818086350778873 19954172368363564763084155)
          ·
            refine ⟨29931258552545347144626233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19954172368363564763084155 29931258552545347144626233)
            ·
              refine ⟨22448443914409010358469675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29931258552545347144626233 22448443914409010358469675)
              ·
                refine ⟨33672665871613515537704513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22448443914409010358469675 33672665871613515537704513)
                ·
                  refine ⟨25254499403710136653278385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33672665871613515537704513 25254499403710136653278385)
                  ·
                    refine ⟨18940874552782602489958789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25254499403710136653278385 18940874552782602489958789)
                    ·
                      refine ⟨3551413978646737966867273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18940874552782602489958789 3551413978646737966867273)
                      ·
                        rfl

theorem cell23_6916354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_6916354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916354 prefixEnd_6916354 := by exact prefixLift 6916354
  have htrace : WordTrace (prefixWord ++ tailWord_6916354) baseStart_6916354 baseEnd_6916354 := by
    simpa [prefixWord, tailWord_6916354, baseEnd_6916354] using wordTrace_append hprefix tailTrace_6916354
  have hstable : (prefixWord ++ tailWord_6916354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916354).length < 2 ^ (prefixWord ++ tailWord_6916354).sum := by decide
  have hdescent : baseEnd_6916354 < baseStart_6916354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916367 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 2, 5, 2]
def baseStart_6916367 : Nat := 118140960795 + 6916367 * 2 ^ 59
def prefixEnd_6916367 : Nat := 4983230072969 + 3 ^ 40 * 6916367 * 2
def baseEnd_6916367 : Nat := 3551420653895246416004713

theorem tailTrace_6916367 : CollatzResearch.WordTrace tailWord_6916367 prefixEnd_6916367 3551420653895246416004713 := by
  unfold tailWord_6916367
  simp only [CollatzResearch.WordTrace]
  refine ⟨252260628534191055286867355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168173752356127370191244903 252260628534191055286867355)
  ·
    refine ⟨378390942801286582930301033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252260628534191055286867355 378390942801286582930301033)
    ·
      refine ⟨283793207100964937197725775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378390942801286582930301033 283793207100964937197725775)
      ·
        refine ⟨425689810651447405796588663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283793207100964937197725775 425689810651447405796588663)
        ·
          refine ⟨638534715977171108694882995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425689810651447405796588663 638534715977171108694882995)
          ·
            refine ⟨957802073965756663042324493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638534715977171108694882995 957802073965756663042324493)
            ·
              refine ⟨359175777737158748640871685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 957802073965756663042324493 359175777737158748640871685)
              ·
                refine ⟨67345458325717265370163441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359175777737158748640871685 67345458325717265370163441)
                ·
                  refine ⟨50509093744287949027622581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67345458325717265370163441 50509093744287949027622581)
                  ·
                    refine ⟨4735227538526995221339617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50509093744287949027622581 4735227538526995221339617)
                    ·
                      refine ⟨3551420653895246416004713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735227538526995221339617 3551420653895246416004713)
                      ·
                        rfl

theorem cell23_6916367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 5, 2].length) (baseStart_6916367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916367 prefixEnd_6916367 := by exact prefixLift 6916367
  have htrace : WordTrace (prefixWord ++ tailWord_6916367) baseStart_6916367 baseEnd_6916367 := by
    simpa [prefixWord, tailWord_6916367, baseEnd_6916367] using wordTrace_append hprefix tailTrace_6916367
  have hstable : (prefixWord ++ tailWord_6916367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916367).length < 2 ^ (prefixWord ++ tailWord_6916367).sum := by decide
  have hdescent : baseEnd_6916367 < baseStart_6916367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916398 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_6916398 : Nat := 118140960795 + 6916398 * 2 ^ 59
def prefixEnd_6916398 : Nat := 4983230072969 + 3 ^ 40 * 6916398 * 2
def baseEnd_6916398 : Nat := 394604063532837310524119

theorem tailTrace_6916398 : CollatzResearch.WordTrace tailWord_6916398 prefixEnd_6916398 394604063532837310524119 := by
  unfold tailWord_6916398
  simp only [CollatzResearch.WordTrace]
  refine ⟨31532719899634843447655731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168174506131385831720830565 31532719899634843447655731)
  ·
    refine ⟨47299079849452265171483597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31532719899634843447655731 47299079849452265171483597)
    ·
      refine ⟨17737154943544599439306349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47299079849452265171483597 17737154943544599439306349)
      ·
        refine ⟨6651433103829224789739881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17737154943544599439306349 6651433103829224789739881)
        ·
          refine ⟨4988574827871918592304911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6651433103829224789739881 4988574827871918592304911)
          ·
            refine ⟨7482862241807877888457367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988574827871918592304911 7482862241807877888457367)
            ·
              refine ⟨11224293362711816832686051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7482862241807877888457367 11224293362711816832686051)
              ·
                refine ⟨16836440044067725249029077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11224293362711816832686051 16836440044067725249029077)
                ·
                  refine ⟨394604063532837310524119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16836440044067725249029077 394604063532837310524119)
                  ·
                    rfl

theorem cell23_6916398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_6916398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916398 prefixEnd_6916398 := by exact prefixLift 6916398
  have htrace : WordTrace (prefixWord ++ tailWord_6916398) baseStart_6916398 baseEnd_6916398 := by
    simpa [prefixWord, tailWord_6916398, baseEnd_6916398] using wordTrace_append hprefix tailTrace_6916398
  have hstable : (prefixWord ++ tailWord_6916398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916398).length < 2 ^ (prefixWord ++ tailWord_6916398).sum := by decide
  have hdescent : baseEnd_6916398 < baseStart_6916398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916400 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_6916400 : Nat := 118140960795 + 6916400 * 2 ^ 59
def prefixEnd_6916400 : Nat := 4983230072969 + 3 ^ 40 * 6916400 * 2
def baseEnd_6916400 : Nat := 3551437598756844786892061

theorem tailTrace_6916400 : CollatzResearch.WordTrace tailWord_6916400 prefixEnd_6916400 3551437598756844786892061 := by
  unfold tailWord_6916400
  simp only [CollatzResearch.WordTrace]
  refine ⟨126130916071535750961409327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168174554762047667948545769 126130916071535750961409327)
  ·
    refine ⟨189196374107303626442113991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126130916071535750961409327 189196374107303626442113991)
    ·
      refine ⟨283794561160955439663170987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189196374107303626442113991 283794561160955439663170987)
      ·
        refine ⟨425691841741433159494756481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283794561160955439663170987 425691841741433159494756481)
        ·
          refine ⟨319268881306074869621067361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425691841741433159494756481 319268881306074869621067361)
          ·
            refine ⟨239451660979556152215800521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319268881306074869621067361 239451660979556152215800521)
            ·
              refine ⟨179588745734667114161850391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239451660979556152215800521 179588745734667114161850391)
              ·
                refine ⟨269383118602000671242775587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179588745734667114161850391 269383118602000671242775587)
                ·
                  refine ⟨404074677903001006864163381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269383118602000671242775587 404074677903001006864163381)
                  ·
                    refine ⟨37882001053406344393515317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 404074677903001006864163381 37882001053406344393515317)
                    ·
                      refine ⟨3551437598756844786892061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37882001053406344393515317 3551437598756844786892061)
                      ·
                        rfl

theorem cell23_6916400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_6916400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916400 prefixEnd_6916400 := by exact prefixLift 6916400
  have htrace : WordTrace (prefixWord ++ tailWord_6916400) baseStart_6916400 baseEnd_6916400 := by
    simpa [prefixWord, tailWord_6916400, baseEnd_6916400] using wordTrace_append hprefix tailTrace_6916400
  have hstable : (prefixWord ++ tailWord_6916400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916400).length < 2 ^ (prefixWord ++ tailWord_6916400).sum := by decide
  have hdescent : baseEnd_6916400 < baseStart_6916400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916404 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_6916404 : Nat := 118140960795 + 6916404 * 2 ^ 59
def prefixEnd_6916404 : Nat := 4983230072969 + 3 ^ 40 * 6916404 * 2
def baseEnd_6916404 : Nat := 3551439652679462771242043

theorem tailTrace_6916404 : CollatzResearch.WordTrace tailWord_6916404 prefixEnd_6916404 3551439652679462771242043 := by
  unfold tailWord_6916404
  simp only [CollatzResearch.WordTrace]
  refine ⟨126130989017528505302982133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168174652023371340403976177 126130989017528505302982133)
  ·
    refine ⟨11824780220393297372154575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126130989017528505302982133 11824780220393297372154575)
    ·
      refine ⟨17737170330589946058231863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11824780220393297372154575 17737170330589946058231863)
      ·
        refine ⟨26605755495884919087347795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17737170330589946058231863 26605755495884919087347795)
        ·
          refine ⟨39908633243827378631021693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26605755495884919087347795 39908633243827378631021693)
          ·
            refine ⟨14965737466435266986633135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39908633243827378631021693 14965737466435266986633135)
            ·
              refine ⟨22448606199652900479949703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14965737466435266986633135 22448606199652900479949703)
              ·
                refine ⟨33672909299479350719924555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22448606199652900479949703 33672909299479350719924555)
                ·
                  refine ⟨50509363949219026079886833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33672909299479350719924555 50509363949219026079886833)
                  ·
                    refine ⟨37882022961914269559915125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50509363949219026079886833 37882022961914269559915125)
                    ·
                      refine ⟨3551439652679462771242043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37882022961914269559915125 3551439652679462771242043)
                      ·
                        rfl

theorem cell23_6916404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_6916404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916404 prefixEnd_6916404 := by exact prefixLift 6916404
  have htrace : WordTrace (prefixWord ++ tailWord_6916404) baseStart_6916404 baseEnd_6916404 := by
    simpa [prefixWord, tailWord_6916404, baseEnd_6916404] using wordTrace_append hprefix tailTrace_6916404
  have hstable : (prefixWord ++ tailWord_6916404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916404).length < 2 ^ (prefixWord ++ tailWord_6916404).sum := by decide
  have hdescent : baseEnd_6916404 < baseStart_6916404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916434 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_6916434 : Nat := 118140960795 + 6916434 * 2 ^ 59
def prefixEnd_6916434 : Nat := 4983230072969 + 3 ^ 40 * 6916434 * 2
def baseEnd_6916434 : Nat := 3551455057099097653866905

theorem tailTrace_6916434 : CollatzResearch.WordTrace tailWord_6916434 prefixEnd_6916434 3551455057099097653866905 := by
  unfold tailWord_6916434
  simp only [CollatzResearch.WordTrace]
  refine ⟨63065768056237081432389089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168175381483298883819704237 63065768056237081432389089)
  ·
    refine ⟨47299326042177811074291817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63065768056237081432389089 47299326042177811074291817)
    ·
      refine ⟨35474494531633358305718863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47299326042177811074291817 35474494531633358305718863)
      ·
        refine ⟨53211741797450037458578295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35474494531633358305718863 53211741797450037458578295)
        ·
          refine ⟨79817612696175056187867443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53211741797450037458578295 79817612696175056187867443)
          ·
            refine ⟨119726419044262584281801165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79817612696175056187867443 119726419044262584281801165)
            ·
              refine ⟨44897407141598469105675437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119726419044262584281801165 44897407141598469105675437)
              ·
                refine ⟨16836527678099425914628289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44897407141598469105675437 16836527678099425914628289)
                ·
                  refine ⟨12627395758574569435971217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16836527678099425914628289 12627395758574569435971217)
                  ·
                    refine ⟨9470546818930927076978413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12627395758574569435971217 9470546818930927076978413)
                    ·
                      refine ⟨3551455057099097653866905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9470546818930927076978413 3551455057099097653866905)
                      ·
                        rfl

theorem cell23_6916434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_6916434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916434 prefixEnd_6916434 := by exact prefixLift 6916434
  have htrace : WordTrace (prefixWord ++ tailWord_6916434) baseStart_6916434 baseEnd_6916434 := by
    simpa [prefixWord, tailWord_6916434, baseEnd_6916434] using wordTrace_append hprefix tailTrace_6916434
  have hstable : (prefixWord ++ tailWord_6916434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916434).length < 2 ^ (prefixWord ++ tailWord_6916434).sum := by decide
  have hdescent : baseEnd_6916434 < baseStart_6916434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916458 : List Nat := [3, 1, 3, 3, 1, 2, 1, 4, 1, 4]
def baseStart_6916458 : Nat := 118140960795 + 6916458 * 2 ^ 59
def prefixEnd_6916458 : Nat := 4983230072969 + 3 ^ 40 * 6916458 * 2
def baseEnd_6916458 : Nat := 1183822460211601853322265

theorem tailTrace_6916458 : CollatzResearch.WordTrace tailWord_6916458 prefixEnd_6916458 1183822460211601853322265 := by
  unfold tailWord_6916458
  simp only [CollatzResearch.WordTrace]
  refine ⟨63065986894215344457107507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168175965051240918552286685 63065986894215344457107507)
  ·
    refine ⟨94598980341323016685661261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63065986894215344457107507 94598980341323016685661261)
    ·
      refine ⟨35474617627996131257122973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94598980341323016685661261 35474617627996131257122973)
      ·
        refine ⟨13302981610498549221421115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35474617627996131257122973 13302981610498549221421115)
        ·
          refine ⟨19954472415747823832131673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13302981610498549221421115 19954472415747823832131673)
          ·
            refine ⟨14965854311810867874098755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19954472415747823832131673 14965854311810867874098755)
            ·
              refine ⟨22448781467716301811148133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14965854311810867874098755 22448781467716301811148133)
              ·
                refine ⟨4209146525196806589590275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22448781467716301811148133 4209146525196806589590275)
                ·
                  refine ⟨6313719787795209884385413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209146525196806589590275 6313719787795209884385413)
                  ·
                    refine ⟨1183822460211601853322265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6313719787795209884385413 1183822460211601853322265)
                    ·
                      rfl

theorem cell23_6916458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_6916458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916458 prefixEnd_6916458 := by exact prefixLift 6916458
  have htrace : WordTrace (prefixWord ++ tailWord_6916458) baseStart_6916458 baseEnd_6916458 := by
    simpa [prefixWord, tailWord_6916458, baseEnd_6916458] using wordTrace_append hprefix tailTrace_6916458
  have hstable : (prefixWord ++ tailWord_6916458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916458).length < 2 ^ (prefixWord ++ tailWord_6916458).sum := by decide
  have hdescent : baseEnd_6916458 < baseStart_6916458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916481 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_6916481 : Nat := 118140960795 + 6916481 * 2 ^ 59
def prefixEnd_6916481 : Nat := 4983230072969 + 3 ^ 40 * 6916481 * 2
def baseEnd_6916481 : Nat := 3551479190689858969979189

theorem tailTrace_6916481 : CollatzResearch.WordTrace tailWord_6916481 prefixEnd_6916481 3551479190689858969979189 := by
  unfold tailWord_6916481
  simp only [CollatzResearch.WordTrace]
  refine ⟨252264786455778052756517297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168176524303852035171011531 252264786455778052756517297)
  ·
    refine ⟨189198589841833539567387973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252264786455778052756517297 189198589841833539567387973)
    ·
      refine ⟨35474735595343788668885245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189198589841833539567387973 35474735595343788668885245)
      ·
        refine ⟨13303025848253920750831967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35474735595343788668885245 13303025848253920750831967)
        ·
          refine ⟨19954538772380881126247951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13303025848253920750831967 19954538772380881126247951)
          ·
            refine ⟨29931808158571321689371927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19954538772380881126247951 29931808158571321689371927)
            ·
              refine ⟨44897712237856982534057891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29931808158571321689371927 44897712237856982534057891)
              ·
                refine ⟨67346568356785473801086837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44897712237856982534057891 67346568356785473801086837)
                ·
                  refine ⟨6313740783448638168851891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67346568356785473801086837 6313740783448638168851891)
                  ·
                    refine ⟨9470611175172957253277837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6313740783448638168851891 9470611175172957253277837)
                    ·
                      refine ⟨3551479190689858969979189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9470611175172957253277837 3551479190689858969979189)
                      ·
                        rfl

theorem cell23_6916481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_6916481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916481 prefixEnd_6916481 := by exact prefixLift 6916481
  have htrace : WordTrace (prefixWord ++ tailWord_6916481) baseStart_6916481 baseEnd_6916481 := by
    simpa [prefixWord, tailWord_6916481, baseEnd_6916481] using wordTrace_append hprefix tailTrace_6916481
  have hstable : (prefixWord ++ tailWord_6916481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916481).length < 2 ^ (prefixWord ++ tailWord_6916481).sum := by decide
  have hdescent : baseEnd_6916481 < baseStart_6916481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916484 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_6916484 : Nat := 118140960795 + 6916484 * 2 ^ 59
def prefixEnd_6916484 : Nat := 4983230072969 + 3 ^ 40 * 6916484 * 2
def baseEnd_6916484 : Nat := 1183826910377274152747225

theorem tailTrace_6916484 : CollatzResearch.WordTrace tailWord_6916484 prefixEnd_6916484 1183826910377274152747225 := by
  unfold tailWord_6916484
  simp only [CollatzResearch.WordTrace]
  refine ⟨126132447937383592134438253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168176597249844789512584337 126132447937383592134438253)
  ·
    refine ⟨47299667976518847050414345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126132447937383592134438253 47299667976518847050414345)
    ·
      refine ⟨35474750982389135287810759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47299667976518847050414345 35474750982389135287810759)
      ·
        refine ⟨53212126473583702931716139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35474750982389135287810759 53212126473583702931716139)
        ·
          refine ⟨79818189710375554397574209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53212126473583702931716139 79818189710375554397574209)
          ·
            refine ⟨59863642282781665798180657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79818189710375554397574209 59863642282781665798180657)
            ·
              refine ⟨44897731712086249348635493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59863642282781665798180657 44897731712086249348635493)
              ·
                refine ⟨8418324696016171752869155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44897731712086249348635493 8418324696016171752869155)
                ·
                  refine ⟨12627487044024257629303733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8418324696016171752869155 12627487044024257629303733)
                  ·
                    refine ⟨1183826910377274152747225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12627487044024257629303733 1183826910377274152747225)
                    ·
                      rfl

theorem cell23_6916484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_6916484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916484 prefixEnd_6916484 := by exact prefixLift 6916484
  have htrace : WordTrace (prefixWord ++ tailWord_6916484) baseStart_6916484 baseEnd_6916484 := by
    simpa [prefixWord, tailWord_6916484, baseEnd_6916484] using wordTrace_append hprefix tailTrace_6916484
  have hstable : (prefixWord ++ tailWord_6916484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916484).length < 2 ^ (prefixWord ++ tailWord_6916484).sum := by decide
  have hdescent : baseEnd_6916484 < baseStart_6916484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916491 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 2, 3, 2]
def baseStart_6916491 : Nat := 118140960795 + 6916491 * 2 ^ 59
def prefixEnd_6916491 : Nat := 4983230072969 + 3 ^ 40 * 6916491 * 2
def baseEnd_6916491 : Nat := 3551484325496403930854143

theorem tailTrace_6916491 : CollatzResearch.WordTrace tailWord_6916491 prefixEnd_6916491 3551484325496403930854143 := by
  unfold tailWord_6916491
  simp only [CollatzResearch.WordTrace]
  refine ⟨252265151185741824464381327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168176767457161216309587551 252265151185741824464381327)
  ·
    refine ⟨378397726778612736696571991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252265151185741824464381327 378397726778612736696571991)
    ·
      refine ⟨567596590167919105044857987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378397726778612736696571991 567596590167919105044857987)
      ·
        refine ⟨851394885251878657567286981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567596590167919105044857987 851394885251878657567286981)
        ·
          refine ⟨159636540984727248293866309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 851394885251878657567286981 159636540984727248293866309)
          ·
            refine ⟨29931851434636359055099933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159636540984727248293866309 29931851434636359055099933)
            ·
              refine ⟨11224444287988634645662475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29931851434636359055099933 11224444287988634645662475)
              ·
                refine ⟨16836666431982951968493713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11224444287988634645662475 16836666431982951968493713)
                ·
                  refine ⟨12627499823987213976370285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16836666431982951968493713 12627499823987213976370285)
                  ·
                    refine ⟨4735312433995205241138857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12627499823987213976370285 4735312433995205241138857)
                    ·
                      refine ⟨3551484325496403930854143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735312433995205241138857 3551484325496403930854143)
                      ·
                        rfl

theorem cell23_6916491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 3, 2].length) (baseStart_6916491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916491 prefixEnd_6916491 := by exact prefixLift 6916491
  have htrace : WordTrace (prefixWord ++ tailWord_6916491) baseStart_6916491 baseEnd_6916491 := by
    simpa [prefixWord, tailWord_6916491, baseEnd_6916491] using wordTrace_append hprefix tailTrace_6916491
  have hstable : (prefixWord ++ tailWord_6916491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916491).length < 2 ^ (prefixWord ++ tailWord_6916491).sum := by decide
  have hdescent : baseEnd_6916491 < baseStart_6916491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916517 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_6916517 : Nat := 118140960795 + 6916517 * 2 ^ 59
def prefixEnd_6916517 : Nat := 4983230072969 + 3 ^ 40 * 6916517 * 2
def baseEnd_6916517 : Nat := 3551497675993420829129023

theorem tailTrace_6916517 : CollatzResearch.WordTrace tailWord_6916517 prefixEnd_6916517 3551497675993420829129023 := by
  unfold tailWord_6916517
  simp only [CollatzResearch.WordTrace]
  refine ⟨252266099483647630904827805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168177399655765087269885203 252266099483647630904827805)
  ·
    refine ⟨94599787306367861589310427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252266099483647630904827805 94599787306367861589310427)
    ·
      refine ⟨141899680959551792383965641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94599787306367861589310427 141899680959551792383965641)
      ·
        refine ⟨106424760719663844287974231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141899680959551792383965641 106424760719663844287974231)
        ·
          refine ⟨159637141079495766431961347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106424760719663844287974231 159637141079495766431961347)
          ·
            refine ⟨239455711619243649647942021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159637141079495766431961347 239455711619243649647942021)
            ·
              refine ⟨44897945928608184308989129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239455711619243649647942021 44897945928608184308989129)
              ·
                refine ⟨33673459446456138231741847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44897945928608184308989129 33673459446456138231741847)
                ·
                  refine ⟨50510189169684207347612771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33673459446456138231741847 50510189169684207347612771)
                  ·
                    refine ⟨75765283754526311021419157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50510189169684207347612771 75765283754526311021419157)
                    ·
                      refine ⟨3551497675993420829129023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75765283754526311021419157 3551497675993420829129023)
                      ·
                        rfl

theorem cell23_6916517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_6916517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916517 prefixEnd_6916517 := by exact prefixLift 6916517
  have htrace : WordTrace (prefixWord ++ tailWord_6916517) baseStart_6916517 baseEnd_6916517 := by
    simpa [prefixWord, tailWord_6916517, baseEnd_6916517] using wordTrace_append hprefix tailTrace_6916517
  have hstable : (prefixWord ++ tailWord_6916517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916517).length < 2 ^ (prefixWord ++ tailWord_6916517).sum := by decide
  have hdescent : baseEnd_6916517 < baseStart_6916517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916541 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_6916541 : Nat := 118140960795 + 6916541 * 2 ^ 59
def prefixEnd_6916541 : Nat := 4983230072969 + 3 ^ 40 * 6916541 * 2
def baseEnd_6916541 : Nat := 3551509999529128735228913

theorem tailTrace_6916541 : CollatzResearch.WordTrace tailWord_6916541 prefixEnd_6916541 3551509999529128735228913 := by
  unfold tailWord_6916541
  simp only [CollatzResearch.WordTrace]
  refine ⟨252266974835560683003701477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168177983223707122002467651 252266974835560683003701477)
  ·
    refine ⟨47300057781667628063194027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252266974835560683003701477 47300057781667628063194027)
    ·
      refine ⟨70950086672501442094791041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47300057781667628063194027 70950086672501442094791041)
      ·
        refine ⟨53212565004376081571093281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70950086672501442094791041 53212565004376081571093281)
        ·
          refine ⟨39909423753282061178319961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53212565004376081571093281 39909423753282061178319961)
          ·
            refine ⟨29932067814961545883739971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39909423753282061178319961 29932067814961545883739971)
            ·
              refine ⟨44898101722442318825609957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29932067814961545883739971 44898101722442318825609957)
              ·
                refine ⟨8418394072957934779801867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44898101722442318825609957 8418394072957934779801867)
                ·
                  refine ⟨12627591109436902169702801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8418394072957934779801867 12627591109436902169702801)
                  ·
                    refine ⟨9470693332077676627277101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12627591109436902169702801 9470693332077676627277101)
                    ·
                      refine ⟨3551509999529128735228913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9470693332077676627277101 3551509999529128735228913)
                      ·
                        rfl

theorem cell23_6916541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_6916541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916541 prefixEnd_6916541 := by exact prefixLift 6916541
  have htrace : WordTrace (prefixWord ++ tailWord_6916541) baseStart_6916541 baseEnd_6916541 := by
    simpa [prefixWord, tailWord_6916541, baseEnd_6916541] using wordTrace_append hprefix tailTrace_6916541
  have hstable : (prefixWord ++ tailWord_6916541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916541).length < 2 ^ (prefixWord ++ tailWord_6916541).sum := by decide
  have hdescent : baseEnd_6916541 < baseStart_6916541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916554 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_6916554 : Nat := 118140960795 + 6916554 * 2 ^ 59
def prefixEnd_6916554 : Nat := 4983230072969 + 3 ^ 40 * 6916554 * 2
def baseEnd_6916554 : Nat := 3551516674777637184366353

theorem tailTrace_6916554 : CollatzResearch.WordTrace tailWord_6916554 prefixEnd_6916554 3551516674777637184366353 := by
  unfold tailWord_6916554
  simp only [CollatzResearch.WordTrace]
  refine ⟨63066862246128396555981179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168178299323009057482616477 63066862246128396555981179)
  ·
    refine ⟨94600293369192594833971769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63066862246128396555981179 94600293369192594833971769)
    ·
      refine ⟨70950220026894446125478827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94600293369192594833971769 70950220026894446125478827)
      ·
        refine ⟨106425330040341669188218241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70950220026894446125478827 106425330040341669188218241)
        ·
          refine ⟨79818997530256251891163681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106425330040341669188218241 79818997530256251891163681)
          ·
            refine ⟨59864248147692188918372761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79818997530256251891163681 59864248147692188918372761)
            ·
              refine ⟨44898186110769141688779571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59864248147692188918372761 44898186110769141688779571)
              ·
                refine ⟨67347279166153712533169357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44898186110769141688779571 67347279166153712533169357)
                ·
                  refine ⟨25255229687307642199938509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67347279166153712533169357 25255229687307642199938509)
                  ·
                    refine ⟨9470711132740365824976941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25255229687307642199938509 9470711132740365824976941)
                    ·
                      refine ⟨3551516674777637184366353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9470711132740365824976941 3551516674777637184366353)
                      ·
                        rfl

theorem cell23_6916554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_6916554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916554 prefixEnd_6916554 := by exact prefixLift 6916554
  have htrace : WordTrace (prefixWord ++ tailWord_6916554) baseStart_6916554 baseEnd_6916554 := by
    simpa [prefixWord, tailWord_6916554, baseEnd_6916554] using wordTrace_append hprefix tailTrace_6916554
  have hstable : (prefixWord ++ tailWord_6916554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916554).length < 2 ^ (prefixWord ++ tailWord_6916554).sum := by decide
  have hdescent : baseEnd_6916554 < baseStart_6916554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916578 : List Nat := [3, 3, 3, 2, 1, 1, 2, 8]
def baseStart_6916578 : Nat := 118140960795 + 6916578 * 2 ^ 59
def prefixEnd_6916578 : Nat := 4983230072969 + 3 ^ 40 * 6916578 * 2
def baseEnd_6916578 : Nat := 131538111048642410758009

theorem tailTrace_6916578 : CollatzResearch.WordTrace tailWord_6916578 prefixEnd_6916578 131538111048642410758009 := by
  unfold tailWord_6916578
  simp only [CollatzResearch.WordTrace]
  refine ⟨63067081084106659580699597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168178882890951092215198925 63067081084106659580699597)
  ·
    refine ⟨23650155406539997342762349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63067081084106659580699597 23650155406539997342762349)
    ·
      refine ⟨8868808277452499003535881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23650155406539997342762349 8868808277452499003535881)
      ·
        refine ⟨6651606208089374252651911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8868808277452499003535881 6651606208089374252651911)
        ·
          refine ⟨9977409312134061378977867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6651606208089374252651911 9977409312134061378977867)
          ·
            refine ⟨14966113968201092068466801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9977409312134061378977867 14966113968201092068466801)
            ·
              refine ⟨11224585476150819051350101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14966113968201092068466801 11224585476150819051350101)
              ·
                refine ⟨131538111048642410758009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11224585476150819051350101 131538111048642410758009)
                ·
                  rfl

theorem cell23_6916578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 8].length) (baseStart_6916578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916578 prefixEnd_6916578 := by exact prefixLift 6916578
  have htrace : WordTrace (prefixWord ++ tailWord_6916578) baseStart_6916578 baseEnd_6916578 := by
    simpa [prefixWord, tailWord_6916578, baseEnd_6916578] using wordTrace_append hprefix tailTrace_6916578
  have hstable : (prefixWord ++ tailWord_6916578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916578).length < 2 ^ (prefixWord ++ tailWord_6916578).sum := by decide
  have hdescent : baseEnd_6916578 < baseStart_6916578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916587 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 1, 8]
def baseStart_6916587 : Nat := 118140960795 + 6916587 * 2 ^ 59
def prefixEnd_6916587 : Nat := 4983230072969 + 3 ^ 40 * 6916587 * 2
def baseEnd_6916587 : Nat := 1183844539879745185084567

theorem tailTrace_6916587 : CollatzResearch.WordTrace tailWord_6916587 prefixEnd_6916587 1183844539879745185084567 := by
  unfold tailWord_6916587
  simp only [CollatzResearch.WordTrace]
  refine ⟨252268652593394032859876015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168179101728929355239917343 252268652593394032859876015)
  ·
    refine ⟨378402978890091049289814023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252268652593394032859876015 378402978890091049289814023)
    ·
      refine ⟨567604468335136573934721035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378402978890091049289814023 567604468335136573934721035)
      ·
        refine ⟨851406702502704860902081553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567604468335136573934721035 851406702502704860902081553)
        ·
          refine ⟨638555026877028645676561165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851406702502704860902081553 638555026877028645676561165)
          ·
            refine ⟨239458135078885742128710437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 638555026877028645676561165 239458135078885742128710437)
            ·
              refine ⟨44898400327291076649133207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239458135078885742128710437 44898400327291076649133207)
              ·
                refine ⟨67347600490936614973699811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44898400327291076649133207 67347600490936614973699811)
                ·
                  refine ⟨101021400736404922460549717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67347600490936614973699811 101021400736404922460549717)
                  ·
                    refine ⟨1183844539879745185084567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101021400736404922460549717 1183844539879745185084567)
                    ·
                      rfl

theorem cell23_6916587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 8].length) (baseStart_6916587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916587 prefixEnd_6916587 := by exact prefixLift 6916587
  have htrace : WordTrace (prefixWord ++ tailWord_6916587) baseStart_6916587 baseEnd_6916587 := by
    simpa [prefixWord, tailWord_6916587, baseEnd_6916587] using wordTrace_append hprefix tailTrace_6916587
  have hstable : (prefixWord ++ tailWord_6916587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916587).length < 2 ^ (prefixWord ++ tailWord_6916587).sum := by decide
  have hdescent : baseEnd_6916587 < baseStart_6916587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916598 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_6916598 : Nat := 118140960795 + 6916598 * 2 ^ 59
def prefixEnd_6916598 : Nat := 4983230072969 + 3 ^ 40 * 6916598 * 2
def baseEnd_6916598 : Nat := 3551539267926435012216151

theorem tailTrace_6916598 : CollatzResearch.WordTrace tailWord_6916598 prefixEnd_6916598 3551539267926435012216151 := by
  unfold tailWord_6916598
  simp only [CollatzResearch.WordTrace]
  refine ⟨15766815862272136358657903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168179369197569454492350965 15766815862272136358657903)
  ·
    refine ⟨23650223793408204537986855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15766815862272136358657903 23650223793408204537986855)
    ·
      refine ⟨35475335690112306806980283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23650223793408204537986855 35475335690112306806980283)
      ·
        refine ⟨53213003535168460210470425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35475335690112306806980283 53213003535168460210470425)
        ·
          refine ⟨39909752651376345157852819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53213003535168460210470425 39909752651376345157852819)
          ·
            refine ⟨59864628977064517736779229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39909752651376345157852819 59864628977064517736779229)
            ·
              refine ⟨22449235866399194151292211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59864628977064517736779229 22449235866399194151292211)
              ·
                refine ⟨33673853799598791226938317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22449235866399194151292211 33673853799598791226938317)
                ·
                  refine ⟨12627695174849546710101869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33673853799598791226938317 12627695174849546710101869)
                  ·
                    refine ⟨4735385690568580016288201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12627695174849546710101869 4735385690568580016288201)
                    ·
                      refine ⟨3551539267926435012216151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735385690568580016288201 3551539267926435012216151)
                      ·
                        rfl

theorem cell23_6916598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_6916598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916598 prefixEnd_6916598 := by exact prefixLift 6916598
  have htrace : WordTrace (prefixWord ++ tailWord_6916598) baseStart_6916598 baseEnd_6916598 := by
    simpa [prefixWord, tailWord_6916598, baseEnd_6916598] using wordTrace_append hprefix tailTrace_6916598
  have hstable : (prefixWord ++ tailWord_6916598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916598).length < 2 ^ (prefixWord ++ tailWord_6916598).sum := by decide
  have hdescent : baseEnd_6916598 < baseStart_6916598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916611 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 1, 4, 2]
def baseStart_6916611 : Nat := 118140960795 + 6916611 * 2 ^ 59
def prefixEnd_6916611 : Nat := 4983230072969 + 3 ^ 40 * 6916611 * 2
def baseEnd_6916611 : Nat := 3551545943174943461353591

theorem tailTrace_6916611 : CollatzResearch.WordTrace tailWord_6916611 prefixEnd_6916611 3551545943174943461353591 := by
  unfold tailWord_6916611
  simp only [CollatzResearch.WordTrace]
  refine ⟨252269527945307084958749687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168179685296871389972499791 252269527945307084958749687)
  ·
    refine ⟨378404291917960627438124531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252269527945307084958749687 378404291917960627438124531)
    ·
      refine ⟨567606437876940941157186797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378404291917960627438124531 567606437876940941157186797)
      ·
        refine ⟨212852414203852852933945049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 567606437876940941157186797 212852414203852852933945049)
        ·
          refine ⟨159639310652889639700458787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212852414203852852933945049 159639310652889639700458787)
          ·
            refine ⟨239458965979334459550688181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159639310652889639700458787 239458965979334459550688181)
            ·
              refine ⟨22449278060562605582877017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239458965979334459550688181 22449278060562605582877017)
              ·
                refine ⟨16836958545421954187157763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22449278060562605582877017 16836958545421954187157763)
                ·
                  refine ⟨25255437818132931280736645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16836958545421954187157763 25255437818132931280736645)
                  ·
                    refine ⟨4735394590899924615138121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25255437818132931280736645 4735394590899924615138121)
                    ·
                      refine ⟨3551545943174943461353591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735394590899924615138121 3551545943174943461353591)
                      ·
                        rfl

theorem cell23_6916611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 4, 2].length) (baseStart_6916611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916611 prefixEnd_6916611 := by exact prefixLift 6916611
  have htrace : WordTrace (prefixWord ++ tailWord_6916611) baseStart_6916611 baseEnd_6916611 := by
    simpa [prefixWord, tailWord_6916611, baseEnd_6916611] using wordTrace_append hprefix tailTrace_6916611
  have hstable : (prefixWord ++ tailWord_6916611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916611).length < 2 ^ (prefixWord ++ tailWord_6916611).sum := by decide
  have hdescent : baseEnd_6916611 < baseStart_6916611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916617 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 11]
def baseStart_6916617 : Nat := 118140960795 + 6916617 * 2 ^ 59
def prefixEnd_6916617 : Nat := 4983230072969 + 3 ^ 40 * 6916617 * 2
def baseEnd_6916617 : Nat := 394616558228763381986507

theorem tailTrace_6916617 : CollatzResearch.WordTrace tailWord_6916617 prefixEnd_6916617 394616558228763381986507 := by
  unfold tailWord_6916617
  simp only [CollatzResearch.WordTrace]
  refine ⟨252269746783285347983468105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168179831188856898655645403 252269746783285347983468105)
  ·
    refine ⟨189202310087464010987601079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252269746783285347983468105 189202310087464010987601079)
    ·
      refine ⟨283803465131196016481401619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189202310087464010987601079 283803465131196016481401619)
      ·
        refine ⟨425705197696794024722102429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283803465131196016481401619 425705197696794024722102429)
        ·
          refine ⟨159639449136297759270788411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425705197696794024722102429 159639449136297759270788411)
          ·
            refine ⟨239459173704446638906182617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159639449136297759270788411 239459173704446638906182617)
            ·
              refine ⟨179594380278334979179636963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239459173704446638906182617 179594380278334979179636963)
              ·
                refine ⟨269391570417502468769455445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179594380278334979179636963 269391570417502468769455445)
                ·
                  refine ⟨394616558228763381986507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 269391570417502468769455445 394616558228763381986507)
                  ·
                    rfl

theorem cell23_6916617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 11].length) (baseStart_6916617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916617 prefixEnd_6916617 := by exact prefixLift 6916617
  have htrace : WordTrace (prefixWord ++ tailWord_6916617) baseStart_6916617 baseEnd_6916617 := by
    simpa [prefixWord, tailWord_6916617, baseEnd_6916617] using wordTrace_append hprefix tailTrace_6916617
  have hstable : (prefixWord ++ tailWord_6916617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916617).length < 2 ^ (prefixWord ++ tailWord_6916617).sum := by decide
  have hdescent : baseEnd_6916617 < baseStart_6916617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916664 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 1, 7]
def baseStart_6916664 : Nat := 118140960795 + 6916664 * 2 ^ 59
def prefixEnd_6916664 : Nat := 4983230072969 + 3 ^ 40 * 6916664 * 2
def baseEnd_6916664 : Nat := 1183857719216543917996949

theorem tailTrace_6916664 : CollatzResearch.WordTrace tailWord_6916664 prefixEnd_6916664 1183857719216543917996949 := by
  unfold tailWord_6916664
  simp only [CollatzResearch.WordTrace]
  refine ⟨126135730507057537505214523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168180974009410050006952697 126135730507057537505214523)
  ·
    refine ⟨189203595760586306257821785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126135730507057537505214523 189203595760586306257821785)
    ·
      refine ⟨141902696820439729693366339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189203595760586306257821785 141902696820439729693366339)
      ·
        refine ⟨212854045230659594540049509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141902696820439729693366339 212854045230659594540049509)
        ·
          refine ⟨39910133480748673976259283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212854045230659594540049509 39910133480748673976259283)
          ·
            refine ⟨59865200221123010964388925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39910133480748673976259283 59865200221123010964388925)
            ·
              refine ⟨22449450082921129111645847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59865200221123010964388925 22449450082921129111645847)
              ·
                refine ⟨33674175124381693667468771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22449450082921129111645847 33674175124381693667468771)
                ·
                  refine ⟨50511262686572540501203157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33674175124381693667468771 50511262686572540501203157)
                  ·
                    refine ⟨1183857719216543917996949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50511262686572540501203157 1183857719216543917996949)
                    ·
                      rfl

theorem cell23_6916664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_6916664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916664 prefixEnd_6916664 := by exact prefixLift 6916664
  have htrace : WordTrace (prefixWord ++ tailWord_6916664) baseStart_6916664 baseEnd_6916664 := by
    simpa [prefixWord, tailWord_6916664, baseEnd_6916664] using wordTrace_append hprefix tailTrace_6916664
  have hstable : (prefixWord ++ tailWord_6916664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916664).length < 2 ^ (prefixWord ++ tailWord_6916664).sum := by decide
  have hdescent : baseEnd_6916664 < baseStart_6916664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916668 : List Nat := [2, 2, 2, 2, 3, 2, 2, 3, 5]
def baseStart_6916668 : Nat := 118140960795 + 6916668 * 2 ^ 59
def prefixEnd_6916668 : Nat := 4983230072969 + 3 ^ 40 * 6916668 * 2
def baseEnd_6916668 : Nat := 394619467952472193148981

theorem tailTrace_6916668 : CollatzResearch.WordTrace tailWord_6916668 prefixEnd_6916668 394619467952472193148981 := by
  unfold tailWord_6916668
  simp only [CollatzResearch.WordTrace]
  refine ⟨126135803453050291846787329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168181071270733722462383105 126135803453050291846787329)
  ·
    refine ⟨94601852589787718885090497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126135803453050291846787329 94601852589787718885090497)
    ·
      refine ⟨70951389442340789163817873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94601852589787718885090497 70951389442340789163817873)
      ·
        refine ⟨53213542081755591872863405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70951389442340789163817873 53213542081755591872863405)
        ·
          refine ⟨19955078280658346952323777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53213542081755591872863405 19955078280658346952323777)
          ·
            refine ⟨14966308710493760214242833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19955078280658346952323777 14966308710493760214242833)
            ·
              refine ⟨11224731532870320160682125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14966308710493760214242833 11224731532870320160682125)
              ·
                refine ⟨4209274324826370060255797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11224731532870320160682125 4209274324826370060255797)
                ·
                  refine ⟨394619467952472193148981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4209274324826370060255797 394619467952472193148981)
                  ·
                    rfl

theorem cell23_6916668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_6916668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916668 prefixEnd_6916668 := by exact prefixLift 6916668
  have htrace : WordTrace (prefixWord ++ tailWord_6916668) baseStart_6916668 baseEnd_6916668 := by
    simpa [prefixWord, tailWord_6916668, baseEnd_6916668] using wordTrace_append hprefix tailTrace_6916668
  have hstable : (prefixWord ++ tailWord_6916668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916668).length < 2 ^ (prefixWord ++ tailWord_6916668).sum := by decide
  have hdescent : baseEnd_6916668 < baseStart_6916668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916771 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 1, 5]
def baseStart_6916771 : Nat := 118140960795 + 6916771 * 2 ^ 59
def prefixEnd_6916771 : Nat := 4983230072969 + 3 ^ 40 * 6916771 * 2
def baseEnd_6916771 : Nat := 1183876033359887611784285

theorem tailTrace_6916771 : CollatzResearch.WordTrace tailWord_6916771 prefixEnd_6916771 1183876033359887611784285 := by
  unfold tailWord_6916771
  simp only [CollatzResearch.WordTrace]
  refine ⟨252275363624727432284574167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168183575749818288189716111 252275363624727432284574167)
  ·
    refine ⟨378413045437091148426861251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252275363624727432284574167 378413045437091148426861251)
    ·
      refine ⟨567619568155636722640291877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378413045437091148426861251 567619568155636722640291877)
      ·
        refine ⟨106428669029181885495054727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 567619568155636722640291877 106428669029181885495054727)
        ·
          refine ⟨159643003543772828242582091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106428669029181885495054727 159643003543772828242582091)
          ·
            refine ⟨239464505315659242363873137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159643003543772828242582091 239464505315659242363873137)
            ·
              refine ⟨179598378986744431772904853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239464505315659242363873137 179598378986744431772904853)
              ·
                refine ⟨8418674015003645239354915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179598378986744431772904853 8418674015003645239354915)
                ·
                  refine ⟨12628011022505467859032373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8418674015003645239354915 12628011022505467859032373)
                  ·
                    refine ⟨1183876033359887611784285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12628011022505467859032373 1183876033359887611784285)
                    ·
                      rfl

theorem cell23_6916771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 5].length) (baseStart_6916771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916771 prefixEnd_6916771 := by exact prefixLift 6916771
  have htrace : WordTrace (prefixWord ++ tailWord_6916771) baseStart_6916771 baseEnd_6916771 := by
    simpa [prefixWord, tailWord_6916771, baseEnd_6916771] using wordTrace_append hprefix tailTrace_6916771
  have hstable : (prefixWord ++ tailWord_6916771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916771).length < 2 ^ (prefixWord ++ tailWord_6916771).sum := by decide
  have hdescent : baseEnd_6916771 < baseStart_6916771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916825 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 2]
def baseStart_6916825 : Nat := 118140960795 + 6916825 * 2 ^ 59
def prefixEnd_6916825 : Nat := 4983230072969 + 3 ^ 40 * 6916825 * 2
def baseEnd_6916825 : Nat := 3551655828035005624077607

theorem tailTrace_6916825 : CollatzResearch.WordTrace tailWord_6916825 prefixEnd_6916825 3551655828035005624077607 := by
  unfold tailWord_6916825
  simp only [CollatzResearch.WordTrace]
  refine ⟨252277333166531799507039929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168184888777687866338026619 252277333166531799507039929)
  ·
    refine ⟨189207999874898849630279947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252277333166531799507039929 189207999874898849630279947)
    ·
      refine ⟨283811999812348274445419921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189207999874898849630279947 283811999812348274445419921)
      ·
        refine ⟨212858999859261205834064941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283811999812348274445419921 212858999859261205834064941)
        ·
          refine ⟨79822124947222952187774353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212858999859261205834064941 79822124947222952187774353)
          ·
            refine ⟨59866593710417214140830765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79822124947222952187774353 59866593710417214140830765)
            ·
              refine ⟨22449972641406455302811537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59866593710417214140830765 22449972641406455302811537)
              ·
                refine ⟨16837479481054841477108653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22449972641406455302811537 16837479481054841477108653)
                ·
                  refine ⟨6314054805395565553915745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16837479481054841477108653 6314054805395565553915745)
                  ·
                    refine ⟨4735541104046674165436809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6314054805395565553915745 4735541104046674165436809)
                    ·
                      refine ⟨3551655828035005624077607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735541104046674165436809 3551655828035005624077607)
                      ·
                        rfl

theorem cell23_6916825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 2].length) (baseStart_6916825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916825 prefixEnd_6916825 := by exact prefixLift 6916825
  have htrace : WordTrace (prefixWord ++ tailWord_6916825) baseStart_6916825 baseEnd_6916825 := by
    simpa [prefixWord, tailWord_6916825, baseEnd_6916825] using wordTrace_append hprefix tailTrace_6916825
  have hstable : (prefixWord ++ tailWord_6916825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916825).length < 2 ^ (prefixWord ++ tailWord_6916825).sum := by decide
  have hdescent : baseEnd_6916825 < baseStart_6916825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916845 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_6916845 : Nat := 118140960795 + 6916845 * 2 ^ 59
def prefixEnd_6916845 : Nat := 4983230072969 + 3 ^ 40 * 6916845 * 2
def baseEnd_6916845 : Nat := 3551666097648095545827515

theorem tailTrace_6916845 : CollatzResearch.WordTrace tailWord_6916845 prefixEnd_6916845 3551666097648095545827515 := by
  unfold tailWord_6916845
  simp only [CollatzResearch.WordTrace]
  refine ⟨252278062626459342922767989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168185375084306228615178659 252278062626459342922767989)
  ·
    refine ⟨23651068371230563399009499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252278062626459342922767989 23651068371230563399009499)
    ·
      refine ⟨35476602556845845098514249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23651068371230563399009499 35476602556845845098514249)
      ·
        refine ⟨26607451917634383823885687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35476602556845845098514249 26607451917634383823885687)
        ·
          refine ⟨39911177876451575735828531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26607451917634383823885687 39911177876451575735828531)
          ·
            refine ⟨59866766814677363603742797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39911177876451575735828531 59866766814677363603742797)
            ·
              refine ⟨22450037555504011351403549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59866766814677363603742797 22450037555504011351403549)
              ·
                refine ⟨8418764083314004256776331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22450037555504011351403549 8418764083314004256776331)
                ·
                  refine ⟨12628146124971006385164497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8418764083314004256776331 12628146124971006385164497)
                  ·
                    refine ⟨9471109593728254788873373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12628146124971006385164497 9471109593728254788873373)
                    ·
                      refine ⟨3551666097648095545827515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9471109593728254788873373 3551666097648095545827515)
                      ·
                        rfl

theorem cell23_6916845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_6916845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916845 prefixEnd_6916845 := by exact prefixLift 6916845
  have htrace : WordTrace (prefixWord ++ tailWord_6916845) baseStart_6916845 baseEnd_6916845 := by
    simpa [prefixWord, tailWord_6916845, baseEnd_6916845] using wordTrace_append hprefix tailTrace_6916845
  have hstable : (prefixWord ++ tailWord_6916845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916845).length < 2 ^ (prefixWord ++ tailWord_6916845).sum := by decide
  have hdescent : baseEnd_6916845 < baseStart_6916845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916881 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_6916881 : Nat := 118140960795 + 6916881 * 2 ^ 59
def prefixEnd_6916881 : Nat := 4983230072969 + 3 ^ 40 * 6916881 * 2
def baseEnd_6916881 : Nat := 3551684582951657404977349

theorem tailTrace_6916881 : CollatzResearch.WordTrace tailWord_6916881 prefixEnd_6916881 3551684582951657404977349 := by
  unfold tailWord_6916881
  simp only [CollatzResearch.WordTrace]
  refine ⟨252279375654328921071078497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168186250436219280714052331 252279375654328921071078497)
  ·
    refine ⟨189209531740746690803308873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252279375654328921071078497 189209531740746690803308873)
    ·
      refine ⟨141907148805560018102481655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189209531740746690803308873 141907148805560018102481655)
      ·
        refine ⟨212860723208340027153722483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141907148805560018102481655 212860723208340027153722483)
        ·
          refine ⟨319291084812510040730583725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212860723208340027153722483 319291084812510040730583725)
          ·
            refine ⟨119734156804691265273968897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319291084812510040730583725 119734156804691265273968897)
            ·
              refine ⟨89800617603518448955476673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119734156804691265273968897 89800617603518448955476673)
              ·
                refine ⟨67350463202638836716607505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89800617603518448955476673 67350463202638836716607505)
                ·
                  refine ⟨50512847401979127537455629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67350463202638836716607505 50512847401979127537455629)
                  ·
                    refine ⟨18942317775742172826545861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50512847401979127537455629 18942317775742172826545861)
                    ·
                      refine ⟨3551684582951657404977349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18942317775742172826545861 3551684582951657404977349)
                      ·
                        rfl

theorem cell23_6916881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_6916881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916881 prefixEnd_6916881 := by exact prefixLift 6916881
  have htrace : WordTrace (prefixWord ++ tailWord_6916881) baseStart_6916881 baseEnd_6916881 := by
    simpa [prefixWord, tailWord_6916881, baseEnd_6916881] using wordTrace_append hprefix tailTrace_6916881
  have hstable : (prefixWord ++ tailWord_6916881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916881).length < 2 ^ (prefixWord ++ tailWord_6916881).sum := by decide
  have hdescent : baseEnd_6916881 < baseStart_6916881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916882 : List Nat := [3, 2, 4, 1, 2, 2, 2, 7]
def baseStart_6916882 : Nat := 118140960795 + 6916882 * 2 ^ 59
def prefixEnd_6916882 : Nat := 4983230072969 + 3 ^ 40 * 6916882 * 2
def baseEnd_6916882 : Nat := 131543892460455996335735

theorem tailTrace_6916882 : CollatzResearch.WordTrace tailWord_6916882 prefixEnd_6916882 131543892460455996335735 := by
  unfold tailWord_6916882
  simp only [CollatzResearch.WordTrace]
  refine ⟨63069853031831324560466225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168186274751550198827909933 63069853031831324560466225)
  ·
    refine ⟨47302389773873493420349669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63069853031831324560466225 47302389773873493420349669)
    ·
      refine ⟨8869198082601280016315563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47302389773873493420349669 8869198082601280016315563)
      ·
        refine ⟨13303797123901920024473345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8869198082601280016315563 13303797123901920024473345)
        ·
          refine ⟨9977847842926440018355009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13303797123901920024473345 9977847842926440018355009)
          ·
            refine ⟨7483385882194830013766257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9977847842926440018355009 7483385882194830013766257)
            ·
              refine ⟨5612539411646122510324693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7483385882194830013766257 5612539411646122510324693)
              ·
                refine ⟨131543892460455996335735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5612539411646122510324693 131543892460455996335735)
                ·
                  rfl

theorem cell23_6916882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 7].length) (baseStart_6916882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916882 prefixEnd_6916882 := by exact prefixLift 6916882
  have htrace : WordTrace (prefixWord ++ tailWord_6916882) baseStart_6916882 baseEnd_6916882 := by
    simpa [prefixWord, tailWord_6916882, baseEnd_6916882] using wordTrace_append hprefix tailTrace_6916882
  have hstable : (prefixWord ++ tailWord_6916882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916882).length < 2 ^ (prefixWord ++ tailWord_6916882).sum := by decide
  have hdescent : baseEnd_6916882 < baseStart_6916882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916893 : List Nat := [1, 4, 2, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_6916893 : Nat := 118140960795 + 6916893 * 2 ^ 59
def prefixEnd_6916893 : Nat := 4983230072969 + 3 ^ 40 * 6916893 * 2
def baseEnd_6916893 : Nat := 3551690744719511358027295

theorem tailTrace_6916893 : CollatzResearch.WordTrace tailWord_6916893 prefixEnd_6916893 3551690744719511358027295 := by
  unfold tailWord_6916893
  simp only [CollatzResearch.WordTrace]
  refine ⟨252279813330285447120515333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168186542220190298080343555 252279813330285447120515333)
  ·
    refine ⟨47302464999428521335096625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252279813330285447120515333 47302464999428521335096625)
    ·
      refine ⟨35476848749571391001322469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47302464999428521335096625 35476848749571391001322469)
      ·
        refine ⟨6651909140544635812747963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35476848749571391001322469 6651909140544635812747963)
        ·
          refine ⟨9977863710816953719121945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6651909140544635812747963 9977863710816953719121945)
          ·
            refine ⟨7483397783112715289341459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9977863710816953719121945 7483397783112715289341459)
            ·
              refine ⟨11225096674669072934012189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7483397783112715289341459 11225096674669072934012189)
              ·
                refine ⟨4209411253000902350254571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11225096674669072934012189 4209411253000902350254571)
                ·
                  refine ⟨6314116879501353525381857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209411253000902350254571 6314116879501353525381857)
                  ·
                    refine ⟨4735587659626015144036393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6314116879501353525381857 4735587659626015144036393)
                    ·
                      refine ⟨3551690744719511358027295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735587659626015144036393 3551690744719511358027295)
                      ·
                        rfl

theorem cell23_6916893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_6916893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916893 prefixEnd_6916893 := by exact prefixLift 6916893
  have htrace : WordTrace (prefixWord ++ tailWord_6916893) baseStart_6916893 baseEnd_6916893 := by
    simpa [prefixWord, tailWord_6916893, baseEnd_6916893] using wordTrace_append hprefix tailTrace_6916893
  have hstable : (prefixWord ++ tailWord_6916893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916893).length < 2 ^ (prefixWord ++ tailWord_6916893).sum := by decide
  have hdescent : baseEnd_6916893 < baseStart_6916893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916926 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_6916926 : Nat := 118140960795 + 6916926 * 2 ^ 59
def prefixEnd_6916926 : Nat := 4983230072969 + 3 ^ 40 * 6916926 * 2
def baseEnd_6916926 : Nat := 3551707689581109728914643

theorem tailTrace_6916926 : CollatzResearch.WordTrace tailWord_6916926 prefixEnd_6916926 3551707689581109728914643 := by
  unfold tailWord_6916926
  simp only [CollatzResearch.WordTrace]
  refine ⟨31535127117395736719558329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168187344626110595837644421 31535127117395736719558329)
  ·
    refine ⟨23651345338046802539668747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31535127117395736719558329 23651345338046802539668747)
    ·
      refine ⟨35477018007070203809503121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23651345338046802539668747 35477018007070203809503121)
      ·
        refine ⟨26607763505302652857127341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35477018007070203809503121 26607763505302652857127341)
        ·
          refine ⟨9977911314488494821422753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26607763505302652857127341 9977911314488494821422753)
          ·
            refine ⟨7483433485866371116067065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9977911314488494821422753 7483433485866371116067065)
            ·
              refine ⟨5612575114399778337050299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7483433485866371116067065 5612575114399778337050299)
              ·
                refine ⟨8418862671599667505575449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5612575114399778337050299 8418862671599667505575449)
                ·
                  refine ⟨6314147003699750629181587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8418862671599667505575449 6314147003699750629181587)
                  ·
                    refine ⟨9471220505549625943772381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6314147003699750629181587 9471220505549625943772381)
                    ·
                      refine ⟨3551707689581109728914643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9471220505549625943772381 3551707689581109728914643)
                      ·
                        rfl

theorem cell23_6916926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_6916926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916926 prefixEnd_6916926 := by exact prefixLift 6916926
  have htrace : WordTrace (prefixWord ++ tailWord_6916926) baseStart_6916926 baseEnd_6916926 := by
    simpa [prefixWord, tailWord_6916926, baseEnd_6916926] using wordTrace_append hprefix tailTrace_6916926
  have hstable : (prefixWord ++ tailWord_6916926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916926).length < 2 ^ (prefixWord ++ tailWord_6916926).sum := by decide
  have hdescent : baseEnd_6916926 < baseStart_6916926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916978 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_6916978 : Nat := 118140960795 + 6916978 * 2 ^ 59
def prefixEnd_6916978 : Nat := 4983230072969 + 3 ^ 40 * 6916978 * 2
def baseEnd_6916978 : Nat := 3551734390575143525464403

theorem tailTrace_6916978 : CollatzResearch.WordTrace tailWord_6916978 prefixEnd_6916978 3551734390575143525464403 := by
  unfold tailWord_6916978
  simp only [CollatzResearch.WordTrace]
  refine ⟨63070728383744376659339897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168188609023318337758239725 63070728383744376659339897)
  ·
    refine ⟨47303046287808282494504923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63070728383744376659339897 47303046287808282494504923)
    ·
      refine ⟨70954569431712423741757385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47303046287808282494504923 70954569431712423741757385)
      ·
        refine ⟨53215927073784317806318039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70954569431712423741757385 53215927073784317806318039)
        ·
          refine ⟨79823890610676476709477059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53215927073784317806318039 79823890610676476709477059)
          ·
            refine ⟨119735835916014715064215589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79823890610676476709477059 119735835916014715064215589)
            ·
              refine ⟨22450469234252759074540423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119735835916014715064215589 22450469234252759074540423)
              ·
                refine ⟨33675703851379138611810635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22450469234252759074540423 33675703851379138611810635)
                ·
                  refine ⟨50513555777068707917715953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33675703851379138611810635 50513555777068707917715953)
                  ·
                    refine ⟨37885166832801530938286965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50513555777068707917715953 37885166832801530938286965)
                    ·
                      refine ⟨3551734390575143525464403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37885166832801530938286965 3551734390575143525464403)
                      ·
                        rfl

theorem cell23_6916978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_6916978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916978 prefixEnd_6916978 := by exact prefixLift 6916978
  have htrace : WordTrace (prefixWord ++ tailWord_6916978) baseStart_6916978 baseEnd_6916978 := by
    simpa [prefixWord, tailWord_6916978, baseEnd_6916978] using wordTrace_append hprefix tailTrace_6916978
  have hstable : (prefixWord ++ tailWord_6916978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916978).length < 2 ^ (prefixWord ++ tailWord_6916978).sum := by decide
  have hdescent : baseEnd_6916978 < baseStart_6916978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916982 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_6916982 : Nat := 118140960795 + 6916982 * 2 ^ 59
def prefixEnd_6916982 : Nat := 4983230072969 + 3 ^ 40 * 6916982 * 2
def baseEnd_6916982 : Nat := 3551736444497761509814385

theorem tailTrace_6916982 : CollatzResearch.WordTrace tailWord_6916982 prefixEnd_6916982 3551736444497761509814385 := by
  unfold tailWord_6916982
  simp only [CollatzResearch.WordTrace]
  refine ⟨15767691214185188457531575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168188706284642010213670133 15767691214185188457531575)
  ·
    refine ⟨23651536821277782686297363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15767691214185188457531575 23651536821277782686297363)
    ·
      refine ⟨35477305231916674029446045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23651536821277782686297363 35477305231916674029446045)
      ·
        refine ⟨13303989461968752761042267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35477305231916674029446045 13303989461968752761042267)
        ·
          refine ⟨19955984192953129141563401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13303989461968752761042267 19955984192953129141563401)
          ·
            refine ⟨14966988144714846856172551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19955984192953129141563401 14966988144714846856172551)
            ·
              refine ⟨22450482217072270284258827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14966988144714846856172551 22450482217072270284258827)
              ·
                refine ⟨33675723325608405426388241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22450482217072270284258827 33675723325608405426388241)
                ·
                  refine ⟨25256792494206304069791181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33675723325608405426388241 25256792494206304069791181)
                  ·
                    refine ⟨9471297185327364026171693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25256792494206304069791181 9471297185327364026171693)
                    ·
                      refine ⟨3551736444497761509814385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9471297185327364026171693 3551736444497761509814385)
                      ·
                        rfl

theorem cell23_6916982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_6916982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916982 prefixEnd_6916982 := by exact prefixLift 6916982
  have htrace : WordTrace (prefixWord ++ tailWord_6916982) baseStart_6916982 baseEnd_6916982 := by
    simpa [prefixWord, tailWord_6916982, baseEnd_6916982] using wordTrace_append hprefix tailTrace_6916982
  have hstable : (prefixWord ++ tailWord_6916982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916982).length < 2 ^ (prefixWord ++ tailWord_6916982).sum := by decide
  have hdescent : baseEnd_6916982 < baseStart_6916982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6916988 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_6916988 : Nat := 118140960795 + 6916988 * 2 ^ 59
def prefixEnd_6916988 : Nat := 4983230072969 + 3 ^ 40 * 6916988 * 2
def baseEnd_6916988 : Nat := 3551739525381688486339357

theorem tailTrace_6916988 : CollatzResearch.WordTrace tailWord_6916988 prefixEnd_6916988 3551739525381688486339357 := by
  unfold tailWord_6916988
  simp only [CollatzResearch.WordTrace]
  refine ⟨126141639132470639172611809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168188852176627518896815745 126141639132470639172611809)
  ·
    refine ⟨94606229349352979379458857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126141639132470639172611809 94606229349352979379458857)
    ·
      refine ⟨70954672012014734534594143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94606229349352979379458857 70954672012014734534594143)
      ·
        refine ⟨106432008018022101801891215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70954672012014734534594143 106432008018022101801891215)
        ·
          refine ⟨159648012027033152702836823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106432008018022101801891215 159648012027033152702836823)
          ·
            refine ⟨239472018040549729054255235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159648012027033152702836823 239472018040549729054255235)
            ·
              refine ⟨359208027060824593581382853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239472018040549729054255235 359208027060824593581382853)
              ·
                refine ⟨67351505073904611296509285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359208027060824593581382853 67351505073904611296509285)
                ·
                  refine ⟨12628407201357114618095491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67351505073904611296509285 12628407201357114618095491)
                  ·
                    refine ⟨18942610802035671927143237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12628407201357114618095491 18942610802035671927143237)
                    ·
                      refine ⟨3551739525381688486339357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18942610802035671927143237 3551739525381688486339357)
                      ·
                        rfl

theorem cell23_6916988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_6916988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6916988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6916988 prefixEnd_6916988 := by exact prefixLift 6916988
  have htrace : WordTrace (prefixWord ++ tailWord_6916988) baseStart_6916988 baseEnd_6916988 := by
    simpa [prefixWord, tailWord_6916988, baseEnd_6916988] using wordTrace_append hprefix tailTrace_6916988
  have hstable : (prefixWord ++ tailWord_6916988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6916988).length < 2 ^ (prefixWord ++ tailWord_6916988).sum := by decide
  have hdescent : baseEnd_6916988 < baseStart_6916988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6916988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917002 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 2, 5]
def baseStart_6917002 : Nat := 118140960795 + 6917002 * 2 ^ 59
def prefixEnd_6917002 : Nat := 4983230072969 + 3 ^ 40 * 6917002 * 2
def baseEnd_6917002 : Nat := 1183915571370283810521431

theorem tailTrace_6917002 : CollatzResearch.WordTrace tailWord_6917002 prefixEnd_6917002 1183915571370283810521431 := by
  unfold tailWord_6917002
  simp only [CollatzResearch.WordTrace]
  refine ⟨63070947221722639684058315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168189192591260372490822173 63070947221722639684058315)
  ·
    refine ⟨94606420832583959526087473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63070947221722639684058315 94606420832583959526087473)
    ·
      refine ⟨70954815624437969644565605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94606420832583959526087473 70954815624437969644565605)
      ·
        refine ⟨13304027929582119308356051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70954815624437969644565605 13304027929582119308356051)
        ·
          refine ⟨19956041894373178962534077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13304027929582119308356051 19956041894373178962534077)
          ·
            refine ⟨7483515710389942110950279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19956041894373178962534077 7483515710389942110950279)
            ·
              refine ⟨11225273565584913166425419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7483515710389942110950279 11225273565584913166425419)
              ·
                refine ⟨16837910348377369749638129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11225273565584913166425419 16837910348377369749638129)
                ·
                  refine ⟨12628432761283027312228597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16837910348377369749638129 12628432761283027312228597)
                  ·
                    refine ⟨1183915571370283810521431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12628432761283027312228597 1183915571370283810521431)
                    ·
                      rfl

theorem cell23_6917002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_6917002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917002 prefixEnd_6917002 := by exact prefixLift 6917002
  have htrace : WordTrace (prefixWord ++ tailWord_6917002) baseStart_6917002 baseEnd_6917002 := by
    simpa [prefixWord, tailWord_6917002, baseEnd_6917002] using wordTrace_append hprefix tailTrace_6917002
  have hstable : (prefixWord ++ tailWord_6917002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917002).length < 2 ^ (prefixWord ++ tailWord_6917002).sum := by decide
  have hdescent : baseEnd_6917002 < baseStart_6917002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917028 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 8]
def baseStart_6917028 : Nat := 118140960795 + 6917028 * 2 ^ 59
def prefixEnd_6917028 : Nat := 4983230072969 + 3 ^ 40 * 6917028 * 2
def baseEnd_6917028 : Nat := 394640007178652036648797

theorem tailTrace_6917028 : CollatzResearch.WordTrace tailWord_6917028 prefixEnd_6917028 394640007178652036648797 := by
  unfold tailWord_6917028
  simp only [CollatzResearch.WordTrace]
  refine ⟨126142368592398182588339869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168189824789864243451119825 126142368592398182588339869)
  ·
    refine ⟨47303388222149318470627451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126142368592398182588339869 47303388222149318470627451)
    ·
      refine ⟨70955082333223977705941177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47303388222149318470627451 70955082333223977705941177)
      ·
        refine ⟨53216311749917983279455883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70955082333223977705941177 53216311749917983279455883)
        ·
          refine ⟨79824467624876974919183825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53216311749917983279455883 79824467624876974919183825)
          ·
            refine ⟨59868350718657731189387869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79824467624876974919183825 59868350718657731189387869)
            ·
              refine ⟨22450631519496649196020451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59868350718657731189387869 22450631519496649196020451)
              ·
                refine ⟨33675947279244973794030677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22450631519496649196020451 33675947279244973794030677)
                ·
                  refine ⟨394640007178652036648797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33675947279244973794030677 394640007178652036648797)
                  ·
                    rfl

theorem cell23_6917028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_6917028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917028 prefixEnd_6917028 := by exact prefixLift 6917028
  have htrace : WordTrace (prefixWord ++ tailWord_6917028) baseStart_6917028 baseEnd_6917028 := by
    simpa [prefixWord, tailWord_6917028, baseEnd_6917028] using wordTrace_append hprefix tailTrace_6917028
  have hstable : (prefixWord ++ tailWord_6917028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917028).length < 2 ^ (prefixWord ++ tailWord_6917028).sum := by decide
  have hdescent : baseEnd_6917028 < baseStart_6917028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917055 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 5, 1, 3]
def baseStart_6917055 : Nat := 118140960795 + 6917055 * 2 ^ 59
def prefixEnd_6917055 : Nat := 4983230072969 + 3 ^ 40 * 6917055 * 2
def baseEnd_6917055 : Nat := 3551773928585539724201549

theorem tailTrace_6917055 : CollatzResearch.WordTrace tailWord_6917055 prefixEnd_6917055 3551773928585539724201549 := by
  unfold tailWord_6917055
  simp only [CollatzResearch.WordTrace]
  refine ⟨252285721955698548787912619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168190481303799032525275079 252285721955698548787912619)
  ·
    refine ⟨378428582933547823181868929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252285721955698548787912619 378428582933547823181868929)
    ·
      refine ⟨283821437200160867386401697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378428582933547823181868929 283821437200160867386401697)
      ·
        refine ⟨212866077900120650539801273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283821437200160867386401697 212866077900120650539801273)
        ·
          refine ⟨159649558425090487904850955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212866077900120650539801273 159649558425090487904850955)
          ·
            refine ⟨239474337637635731857276433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159649558425090487904850955 239474337637635731857276433)
            ·
              refine ⟨179605753228226798892957325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239474337637635731857276433 179605753228226798892957325)
              ·
                refine ⟨67352157460585049584858997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179605753228226798892957325 67352157460585049584858997)
                ·
                  refine ⟨6314264761929848398580531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67352157460585049584858997 6314264761929848398580531)
                  ·
                    refine ⟨9471397142894772597870797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6314264761929848398580531 9471397142894772597870797)
                    ·
                      refine ⟨3551773928585539724201549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9471397142894772597870797 3551773928585539724201549)
                      ·
                        rfl

theorem cell23_6917055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_6917055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917055 prefixEnd_6917055 := by exact prefixLift 6917055
  have htrace : WordTrace (prefixWord ++ tailWord_6917055) baseStart_6917055 baseEnd_6917055 := by
    simpa [prefixWord, tailWord_6917055, baseEnd_6917055] using wordTrace_append hprefix tailTrace_6917055
  have hstable : (prefixWord ++ tailWord_6917055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917055).length < 2 ^ (prefixWord ++ tailWord_6917055).sum := by decide
  have hdescent : baseEnd_6917055 < baseStart_6917055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917082 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2]
def baseStart_6917082 : Nat := 118140960795 + 6917082 * 2 ^ 59
def prefixEnd_6917082 : Nat := 4983230072969 + 3 ^ 40 * 6917082 * 2
def baseEnd_6917082 : Nat := 3551787792563211118563925

theorem tailTrace_6917082 : CollatzResearch.WordTrace tailWord_6917082 prefixEnd_6917082 3551787792563211118563925 := by
  unfold tailWord_6917082
  simp only [CollatzResearch.WordTrace]
  refine ⟨63071676681650183099786375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168191137817733821599430333 63071676681650183099786375)
  ·
    refine ⟨94607515022475274649679563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63071676681650183099786375 94607515022475274649679563)
    ·
      refine ⟨141911272533712911974519345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94607515022475274649679563 141911272533712911974519345)
      ·
        refine ⟨106433454400284683980889509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141911272533712911974519345 106433454400284683980889509)
        ·
          refine ⟨19956272700053378246416783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106433454400284683980889509 19956272700053378246416783)
          ·
            refine ⟨29934409050080067369625175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19956272700053378246416783 29934409050080067369625175)
            ·
              refine ⟨44901613575120101054437763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29934409050080067369625175 44901613575120101054437763)
              ·
                refine ⟨67352420362680151581656645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44901613575120101054437763 67352420362680151581656645)
                ·
                  refine ⟨12628578818002528421560621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67352420362680151581656645 12628578818002528421560621)
                  ·
                    refine ⟨4735717056750948158085233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12628578818002528421560621 4735717056750948158085233)
                    ·
                      refine ⟨3551787792563211118563925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735717056750948158085233 3551787792563211118563925)
                      ·
                        rfl

theorem cell23_6917082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_6917082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917082 prefixEnd_6917082 := by exact prefixLift 6917082
  have htrace : WordTrace (prefixWord ++ tailWord_6917082) baseStart_6917082 baseEnd_6917082 := by
    simpa [prefixWord, tailWord_6917082, baseEnd_6917082] using wordTrace_append hprefix tailTrace_6917082
  have hstable : (prefixWord ++ tailWord_6917082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917082).length < 2 ^ (prefixWord ++ tailWord_6917082).sum := by decide
  have hdescent : baseEnd_6917082 < baseStart_6917082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917109 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 3, 5]
def baseStart_6917109 : Nat := 118140960795 + 6917109 * 2 ^ 59
def prefixEnd_6917109 : Nat := 4983230072969 + 3 ^ 40 * 6917109 * 2
def baseEnd_6917109 : Nat := 1183933885513627504308767

theorem tailTrace_6917109 : CollatzResearch.WordTrace tailWord_6917109 prefixEnd_6917109 1183933885513627504308767 := by
  unfold tailWord_6917109
  simp only [CollatzResearch.WordTrace]
  refine ⟨252287691497502916010378381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168191794331668610673585587 252287691497502916010378381)
  ·
    refine ⟨94607884311563593503891893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252287691497502916010378381 94607884311563593503891893)
    ·
      refine ⟨8869489154209086890989865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94607884311563593503891893 8869489154209086890989865)
      ·
        refine ⟨6652116865656815168242399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8869489154209086890989865 6652116865656815168242399)
        ·
          refine ⟨9978175298485222752363599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6652116865656815168242399 9978175298485222752363599)
          ·
            refine ⟨14967262947727834128545399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9978175298485222752363599 14967262947727834128545399)
            ·
              refine ⟨22450894421591751192818099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14967262947727834128545399 22450894421591751192818099)
              ·
                refine ⟨33676341632387626789227149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22450894421591751192818099 33676341632387626789227149)
                ·
                  refine ⟨12628628112145360045960181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33676341632387626789227149 12628628112145360045960181)
                  ·
                    refine ⟨1183933885513627504308767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12628628112145360045960181 1183933885513627504308767)
                    ·
                      rfl

theorem cell23_6917109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_6917109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917109 prefixEnd_6917109 := by exact prefixLift 6917109
  have htrace : WordTrace (prefixWord ++ tailWord_6917109) baseStart_6917109 baseEnd_6917109 := by
    simpa [prefixWord, tailWord_6917109, baseEnd_6917109] using wordTrace_append hprefix tailTrace_6917109
  have hstable : (prefixWord ++ tailWord_6917109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917109).length < 2 ^ (prefixWord ++ tailWord_6917109).sum := by decide
  have hdescent : baseEnd_6917109 < baseStart_6917109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917112 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 5, 2, 2]
def baseStart_6917112 : Nat := 118140960795 + 6917112 * 2 ^ 59
def prefixEnd_6917112 : Nat := 4983230072969 + 3 ^ 40 * 6917112 * 2
def baseEnd_6917112 : Nat := 3551803196982846001188787

theorem tailTrace_6917112 : CollatzResearch.WordTrace tailWord_6917112 prefixEnd_6917112 3551803196982846001188787 := by
  unfold tailWord_6917112
  simp only [CollatzResearch.WordTrace]
  refine ⟨126143900458246023761368795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168191867277661365015158393 126143900458246023761368795)
  ·
    refine ⟨189215850687369035642053193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126143900458246023761368795 189215850687369035642053193)
    ·
      refine ⟨141911888015526776731539895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189215850687369035642053193 141911888015526776731539895)
      ·
        refine ⟨212867832023290165097309843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141911888015526776731539895 212867832023290165097309843)
        ·
          refine ⟨319301748034935247645964765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212867832023290165097309843 319301748034935247645964765)
          ·
            refine ⟨119738155513100717867236787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319301748034935247645964765 119738155513100717867236787)
            ·
              refine ⟨179607233269651076800855181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119738155513100717867236787 179607233269651076800855181)
              ·
                refine ⟨67352712476119153800320693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179607233269651076800855181 67352712476119153800320693)
                ·
                  refine ⟨6314316794636170668780065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67352712476119153800320693 6314316794636170668780065)
                  ·
                    refine ⟨4735737595977128001585049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6314316794636170668780065 4735737595977128001585049)
                    ·
                      refine ⟨3551803196982846001188787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735737595977128001585049 3551803196982846001188787)
                      ·
                        rfl

theorem cell23_6917112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5, 2, 2].length) (baseStart_6917112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917112 prefixEnd_6917112 := by exact prefixLift 6917112
  have htrace : WordTrace (prefixWord ++ tailWord_6917112) baseStart_6917112 baseEnd_6917112 := by
    simpa [prefixWord, tailWord_6917112, baseEnd_6917112] using wordTrace_append hprefix tailTrace_6917112
  have hstable : (prefixWord ++ tailWord_6917112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917112).length < 2 ^ (prefixWord ++ tailWord_6917112).sum := by decide
  have hdescent : baseEnd_6917112 < baseStart_6917112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917125 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_6917125 : Nat := 118140960795 + 6917125 * 2 ^ 59
def prefixEnd_6917125 : Nat := 4983230072969 + 3 ^ 40 * 6917125 * 2
def baseEnd_6917125 : Nat := 3551809872231354450326227

theorem tailTrace_6917125 : CollatzResearch.WordTrace tailWord_6917125 prefixEnd_6917125 3551809872231354450326227 := by
  unfold tailWord_6917125
  simp only [CollatzResearch.WordTrace]
  refine ⟨252288275065444950742960829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168192183376963300495307219 252288275065444950742960829)
  ·
    refine ⟨94608103149541856528610311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252288275065444950742960829 94608103149541856528610311)
    ·
      refine ⟨141912154724312784792915467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94608103149541856528610311 141912154724312784792915467)
      ·
        refine ⟨212868232086469177189373201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141912154724312784792915467 212868232086469177189373201)
        ·
          refine ⟨159651174064851882892029901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212868232086469177189373201 159651174064851882892029901)
          ·
            refine ⟨59869190274319456084511213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159651174064851882892029901 59869190274319456084511213)
            ·
              refine ⟨22450946352869796031691705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59869190274319456084511213 22450946352869796031691705)
              ·
                refine ⟨16838209764652347023768779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22450946352869796031691705 16838209764652347023768779)
                ·
                  refine ⟨25257314646978520535653169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16838209764652347023768779 25257314646978520535653169)
                  ·
                    refine ⟨18942985985233890401739877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25257314646978520535653169 18942985985233890401739877)
                    ·
                      refine ⟨3551809872231354450326227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18942985985233890401739877 3551809872231354450326227)
                      ·
                        rfl

theorem cell23_6917125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_6917125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917125 prefixEnd_6917125 := by exact prefixLift 6917125
  have htrace : WordTrace (prefixWord ++ tailWord_6917125) baseStart_6917125 baseEnd_6917125 := by
    simpa [prefixWord, tailWord_6917125, baseEnd_6917125] using wordTrace_append hprefix tailTrace_6917125
  have hstable : (prefixWord ++ tailWord_6917125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917125).length < 2 ^ (prefixWord ++ tailWord_6917125).sum := by decide
  have hdescent : baseEnd_6917125 < baseStart_6917125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917132 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 1, 1, 5]
def baseStart_6917132 : Nat := 118140960795 + 6917132 * 2 ^ 59
def prefixEnd_6917132 : Nat := 4983230072969 + 3 ^ 40 * 6917132 * 2
def baseEnd_6917132 : Nat := 3551813466595935922938695

theorem tailTrace_6917132 : CollatzResearch.WordTrace tailWord_6917132 prefixEnd_6917132 3551813466595935922938695 := by
  unfold tailWord_6917132
  simp only [CollatzResearch.WordTrace]
  refine ⟨126144265188209795469232825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168192353584279727292310433 126144265188209795469232825)
  ·
    refine ⟨94608198891157346601924619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126144265188209795469232825 94608198891157346601924619)
    ·
      refine ⟨141912298336736019902886929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94608198891157346601924619 141912298336736019902886929)
      ·
        refine ⟨106434223752552014927165197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141912298336736019902886929 106434223752552014927165197)
        ·
          refine ⟨39912833907207005597686949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106434223752552014927165197 39912833907207005597686949)
          ·
            refine ⟨7483656357601313549566303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39912833907207005597686949 7483656357601313549566303)
            ·
              refine ⟨11225484536401970324349455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7483656357601313549566303 11225484536401970324349455)
              ·
                refine ⟨16838226804602955486524183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11225484536401970324349455 16838226804602955486524183)
                ·
                  refine ⟨25257340206904433229786275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16838226804602955486524183 25257340206904433229786275)
                  ·
                    refine ⟨37886010310356649844679413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25257340206904433229786275 37886010310356649844679413)
                    ·
                      refine ⟨3551813466595935922938695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37886010310356649844679413 3551813466595935922938695)
                      ·
                        rfl

theorem cell23_6917132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_6917132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917132 prefixEnd_6917132 := by exact prefixLift 6917132
  have htrace : WordTrace (prefixWord ++ tailWord_6917132) baseStart_6917132 baseEnd_6917132 := by
    simpa [prefixWord, tailWord_6917132, baseEnd_6917132] using wordTrace_append hprefix tailTrace_6917132
  have hstable : (prefixWord ++ tailWord_6917132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917132).length < 2 ^ (prefixWord ++ tailWord_6917132).sum := by decide
  have hdescent : baseEnd_6917132 < baseStart_6917132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917146 : List Nat := [3, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2]
def baseStart_6917146 : Nat := 118140960795 + 6917146 * 2 ^ 59
def prefixEnd_6917146 : Nat := 4983230072969 + 3 ^ 40 * 6917146 * 2
def baseEnd_6917146 : Nat := 3551820655325098868163631

theorem tailTrace_6917146 : CollatzResearch.WordTrace tailWord_6917146 prefixEnd_6917146 3551820655325098868163631 := by
  unfold tailWord_6917146
  simp only [CollatzResearch.WordTrace]
  refine ⟨63072260249592217832368823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168192693998912580886316861 63072260249592217832368823)
  ·
    refine ⟨94608390374388326748553235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63072260249592217832368823 94608390374388326748553235)
    ·
      refine ⟨141912585561582490122829853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94608390374388326748553235 141912585561582490122829853)
      ·
        refine ⟨53217219585593433796061195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141912585561582490122829853 53217219585593433796061195)
        ·
          refine ⟨79825829378390150694091793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53217219585593433796061195 79825829378390150694091793)
          ·
            refine ⟨59869372033792613020568845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79825829378390150694091793 59869372033792613020568845)
            ·
              refine ⟨22451014512672229882713317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59869372033792613020568845 22451014512672229882713317)
              ·
                refine ⟨4209565221126043103008747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22451014512672229882713317 4209565221126043103008747)
                ·
                  refine ⟨6314347831689064654513121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209565221126043103008747 6314347831689064654513121)
                  ·
                    refine ⟨4735760873766798490884841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6314347831689064654513121 4735760873766798490884841)
                    ·
                      refine ⟨3551820655325098868163631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735760873766798490884841 3551820655325098868163631)
                      ·
                        rfl

theorem cell23_6917146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_6917146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917146 prefixEnd_6917146 := by exact prefixLift 6917146
  have htrace : WordTrace (prefixWord ++ tailWord_6917146) baseStart_6917146 baseEnd_6917146 := by
    simpa [prefixWord, tailWord_6917146, baseEnd_6917146] using wordTrace_append hprefix tailTrace_6917146
  have hstable : (prefixWord ++ tailWord_6917146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917146).length < 2 ^ (prefixWord ++ tailWord_6917146).sum := by decide
  have hdescent : baseEnd_6917146 < baseStart_6917146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917159 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_6917159 : Nat := 118140960795 + 6917159 * 2 ^ 59
def prefixEnd_6917159 : Nat := 4983230072969 + 3 ^ 40 * 6917159 * 2
def baseEnd_6917159 : Nat := 3551827330573607317301071

theorem tailTrace_6917159 : CollatzResearch.WordTrace tailWord_6917159 prefixEnd_6917159 3551827330573607317301071 := by
  unfold tailWord_6917159
  simp only [CollatzResearch.WordTrace]
  refine ⟨252289515147321774549698531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168193010098214516366465687 252289515147321774549698531)
  ·
    refine ⟨378434272720982661824547797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252289515147321774549698531 378434272720982661824547797)
    ·
      refine ⟨8869553266898031136512839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 378434272720982661824547797 8869553266898031136512839)
      ·
        refine ⟨13304329900347046704769259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8869553266898031136512839 13304329900347046704769259)
        ·
          refine ⟨19956494850520570057153889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13304329900347046704769259 19956494850520570057153889)
          ·
            refine ⟨14967371137890427542865417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19956494850520570057153889 14967371137890427542865417)
            ·
              refine ⟨11225528353417820657149063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14967371137890427542865417 11225528353417820657149063)
              ·
                refine ⟨16838292530126730985723595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11225528353417820657149063 16838292530126730985723595)
                ·
                  refine ⟨25257438795190096478585393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16838292530126730985723595 25257438795190096478585393)
                  ·
                    refine ⟨18943079096392572358939045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25257438795190096478585393 18943079096392572358939045)
                    ·
                      refine ⟨3551827330573607317301071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18943079096392572358939045 3551827330573607317301071)
                      ·
                        rfl

theorem cell23_6917159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_6917159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917159 prefixEnd_6917159 := by exact prefixLift 6917159
  have htrace : WordTrace (prefixWord ++ tailWord_6917159) baseStart_6917159 baseEnd_6917159 := by
    simpa [prefixWord, tailWord_6917159, baseEnd_6917159] using wordTrace_append hprefix tailTrace_6917159
  have hstable : (prefixWord ++ tailWord_6917159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917159).length < 2 ^ (prefixWord ++ tailWord_6917159).sum := by decide
  have hdescent : baseEnd_6917159 < baseStart_6917159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917213 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6917213 : Nat := 118140960795 + 6917213 * 2 ^ 59
def prefixEnd_6917213 : Nat := 4983230072969 + 3 ^ 40 * 6917213 * 2
def baseEnd_6917213 : Nat := 3551855058528950106025823

theorem tailTrace_6917213 : CollatzResearch.WordTrace tailWord_6917213 prefixEnd_6917213 3551855058528950106025823 := by
  unfold tailWord_6917213
  simp only [CollatzResearch.WordTrace]
  refine ⟨252291484689126141772164293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168194323126084094514776195 252291484689126141772164293)
  ·
    refine ⟨47304653379211151582280805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252291484689126141772164293 47304653379211151582280805)
    ·
      refine ⟨8869622508602090921677651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47304653379211151582280805 8869622508602090921677651)
      ·
        refine ⟨13304433762903136382516477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8869622508602090921677651 13304433762903136382516477)
        ·
          refine ⟨4989162661088676143443679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13304433762903136382516477 4989162661088676143443679)
          ·
            refine ⟨7483743991633014215165519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989162661088676143443679 7483743991633014215165519)
            ·
              refine ⟨11225615987449521322748279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7483743991633014215165519 11225615987449521322748279)
              ·
                refine ⟨16838423981174281984122419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11225615987449521322748279 16838423981174281984122419)
                ·
                  refine ⟨25257635971761422976183629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16838423981174281984122419 25257635971761422976183629)
                  ·
                    refine ⟨9471613489410533616068861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25257635971761422976183629 9471613489410533616068861)
                    ·
                      refine ⟨3551855058528950106025823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9471613489410533616068861 3551855058528950106025823)
                      ·
                        rfl

theorem cell23_6917213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6917213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917213 prefixEnd_6917213 := by exact prefixLift 6917213
  have htrace : WordTrace (prefixWord ++ tailWord_6917213) baseStart_6917213 baseEnd_6917213 := by
    simpa [prefixWord, tailWord_6917213, baseEnd_6917213] using wordTrace_append hprefix tailTrace_6917213
  have hstable : (prefixWord ++ tailWord_6917213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917213).length < 2 ^ (prefixWord ++ tailWord_6917213).sum := by decide
  have hdescent : baseEnd_6917213 < baseStart_6917213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917215 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 4]
def baseStart_6917215 : Nat := 118140960795 + 6917215 * 2 ^ 59
def prefixEnd_6917215 : Nat := 4983230072969 + 3 ^ 40 * 6917215 * 2
def baseEnd_6917215 : Nat := 3551856085490259098200813

theorem tailTrace_6917215 : CollatzResearch.WordTrace tailWord_6917215 prefixEnd_6917215 3551856085490259098200813 := by
  unfold tailWord_6917215
  simp only [CollatzResearch.WordTrace]
  refine ⟨252291557635118896113737099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168194371756745930742491399 252291557635118896113737099)
  ·
    refine ⟨378437336452678344170605649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252291557635118896113737099 378437336452678344170605649)
    ·
      refine ⟨283828002339508758127954237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378437336452678344170605649 283828002339508758127954237)
      ·
        refine ⟨106435500877315784297982839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283828002339508758127954237 106435500877315784297982839)
        ·
          refine ⟨159653251315973676446974259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106435500877315784297982839 159653251315973676446974259)
          ·
            refine ⟨239479876973960514670461389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159653251315973676446974259 239479876973960514670461389)
            ·
              refine ⟨89804953865235193001423021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239479876973960514670461389 89804953865235193001423021)
              ·
                refine ⟨33676857699463197375533633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89804953865235193001423021 33676857699463197375533633)
                ·
                  refine ⟨25257643274597398031650225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33676857699463197375533633 25257643274597398031650225)
                  ·
                    refine ⟨18943232455948048523737669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25257643274597398031650225 18943232455948048523737669)
                    ·
                      refine ⟨3551856085490259098200813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18943232455948048523737669 3551856085490259098200813)
                      ·
                        rfl

theorem cell23_6917215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_6917215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917215 prefixEnd_6917215 := by exact prefixLift 6917215
  have htrace : WordTrace (prefixWord ++ tailWord_6917215) baseStart_6917215 baseEnd_6917215 := by
    simpa [prefixWord, tailWord_6917215, baseEnd_6917215] using wordTrace_append hprefix tailTrace_6917215
  have hstable : (prefixWord ++ tailWord_6917215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917215).length < 2 ^ (prefixWord ++ tailWord_6917215).sum := by decide
  have hdescent : baseEnd_6917215 < baseStart_6917215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917225 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 7]
def baseStart_6917225 : Nat := 118140960795 + 6917225 * 2 ^ 59
def prefixEnd_6917225 : Nat := 4983230072969 + 3 ^ 40 * 6917225 * 2
def baseEnd_6917225 : Nat := 394651246699644895452863

theorem tailTrace_6917225 : CollatzResearch.WordTrace tailWord_6917225 prefixEnd_6917225 394651246699644895452863 := by
  unfold tailWord_6917225
  simp only [CollatzResearch.WordTrace]
  refine ⟨252291922365082667821601129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168194614910055111881067419 252291922365082667821601129)
  ·
    refine ⟨189218941773812000866200847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252291922365082667821601129 189218941773812000866200847)
    ·
      refine ⟨283828412660718001299301271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189218941773812000866200847 283828412660718001299301271)
      ·
        refine ⟨425742618991077001948951907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283828412660718001299301271 425742618991077001948951907)
        ·
          refine ⟨638613928486615502923427861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425742618991077001948951907 638613928486615502923427861)
          ·
            refine ⟨29935027897810101699535681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 638613928486615502923427861 29935027897810101699535681)
            ·
              refine ⟨22451270923357576274651761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29935027897810101699535681 22451270923357576274651761)
              ·
                refine ⟨16838453192518182205988821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22451270923357576274651761 16838453192518182205988821)
                ·
                  refine ⟨394651246699644895452863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16838453192518182205988821 394651246699644895452863)
                  ·
                    rfl

theorem cell23_6917225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 7].length) (baseStart_6917225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917225 prefixEnd_6917225 := by exact prefixLift 6917225
  have htrace : WordTrace (prefixWord ++ tailWord_6917225) baseStart_6917225 baseEnd_6917225 := by
    simpa [prefixWord, tailWord_6917225, baseEnd_6917225] using wordTrace_append hprefix tailTrace_6917225
  have hstable : (prefixWord ++ tailWord_6917225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917225).length < 2 ^ (prefixWord ++ tailWord_6917225).sum := by decide
  have hdescent : baseEnd_6917225 < baseStart_6917225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917292 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 3, 6, 2]
def baseStart_6917292 : Nat := 118140960795 + 6917292 * 2 ^ 59
def prefixEnd_6917292 : Nat := 4983230072969 + 3 ^ 40 * 6917292 * 2
def baseEnd_6917292 : Nat := 3551895623500655296937959

theorem tailTrace_6917292 : CollatzResearch.WordTrace tailWord_6917292 prefixEnd_6917292 3551895623500655296937959 := by
  unfold tailWord_6917292
  simp only [CollatzResearch.WordTrace]
  refine ⟨126147183027919969132145065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168196244037226625509526753 126147183027919969132145065)
  ·
    refine ⟨94610387270939976849108799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126147183027919969132145065 94610387270939976849108799)
    ·
      refine ⟨141915580906409965273663199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94610387270939976849108799 141915580906409965273663199)
      ·
        refine ⟨212873371359614947910494799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141915580906409965273663199 212873371359614947910494799)
        ·
          refine ⟨319310057039422421865742199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212873371359614947910494799 319310057039422421865742199)
          ·
            refine ⟨478965085559133632798613299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319310057039422421865742199 478965085559133632798613299)
            ·
              refine ⟨718447628338700449197919949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478965085559133632798613299 718447628338700449197919949)
              ·
                refine ⟨269417860627012668449219981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 718447628338700449197919949 269417860627012668449219981)
                ·
                  refine ⟨101031697735129750668457493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269417860627012668449219981 101031697735129750668457493)
                  ·
                    refine ⟨4735860831334207062583945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101031697735129750668457493 4735860831334207062583945)
                    ·
                      refine ⟨3551895623500655296937959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735860831334207062583945 3551895623500655296937959)
                      ·
                        rfl

theorem cell23_6917292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 6, 2].length) (baseStart_6917292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917292 prefixEnd_6917292 := by exact prefixLift 6917292
  have htrace : WordTrace (prefixWord ++ tailWord_6917292) baseStart_6917292 baseEnd_6917292 := by
    simpa [prefixWord, tailWord_6917292, baseEnd_6917292] using wordTrace_append hprefix tailTrace_6917292
  have hstable : (prefixWord ++ tailWord_6917292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917292).length < 2 ^ (prefixWord ++ tailWord_6917292).sum := by decide
  have hdescent : baseEnd_6917292 < baseStart_6917292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917326 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2]
def baseStart_6917326 : Nat := 118140960795 + 6917326 * 2 ^ 59
def prefixEnd_6917326 : Nat := 4983230072969 + 3 ^ 40 * 6917326 * 2
def baseEnd_6917326 : Nat := 3551913081842908163912803

theorem tailTrace_6917326 : CollatzResearch.WordTrace tailWord_6917326 prefixEnd_6917326 3551913081842908163912803 := by
  unfold tailWord_6917326
  simp only [CollatzResearch.WordTrace]
  refine ⟨31536950767214595258878479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168197070758477841380685221 31536950767214595258878479)
  ·
    refine ⟨47305426150821892888317719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31536950767214595258878479 47305426150821892888317719)
    ·
      refine ⟨70958139226232839332476579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47305426150821892888317719 70958139226232839332476579)
      ·
        refine ⟨106437208839349258998714869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70958139226232839332476579 106437208839349258998714869)
        ·
          refine ⟨9978488328688993031129519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106437208839349258998714869 9978488328688993031129519)
          ·
            refine ⟨14967732493033489546694279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9978488328688993031129519 14967732493033489546694279)
            ·
              refine ⟨22451598739550234320041419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14967732493033489546694279 22451598739550234320041419)
              ·
                refine ⟨33677398109325351480062129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22451598739550234320041419 33677398109325351480062129)
                ·
                  refine ⟨25258048581994013610046597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33677398109325351480062129 25258048581994013610046597)
                  ·
                    refine ⟨4735884109123877551883737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25258048581994013610046597 4735884109123877551883737)
                    ·
                      refine ⟨3551913081842908163912803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735884109123877551883737 3551913081842908163912803)
                      ·
                        rfl

theorem cell23_6917326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_6917326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917326 prefixEnd_6917326 := by exact prefixLift 6917326
  have htrace : WordTrace (prefixWord ++ tailWord_6917326) baseStart_6917326 baseEnd_6917326 := by
    simpa [prefixWord, tailWord_6917326, baseEnd_6917326] using wordTrace_append hprefix tailTrace_6917326
  have hstable : (prefixWord ++ tailWord_6917326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917326).length < 2 ^ (prefixWord ++ tailWord_6917326).sum := by decide
  have hdescent : baseEnd_6917326 < baseStart_6917326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917369 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 4, 3, 2]
def baseStart_6917369 : Nat := 118140960795 + 6917369 * 2 ^ 59
def prefixEnd_6917369 : Nat := 4983230072969 + 3 ^ 40 * 6917369 * 2
def baseEnd_6917369 : Nat := 3551935161511051495675105

theorem tailTrace_6917369 : CollatzResearch.WordTrace tailWord_6917369 prefixEnd_6917369 3551935161511051495675105 := by
  unfold tailWord_6917369
  simp only [CollatzResearch.WordTrace]
  refine ⟨252297174476560980414843161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168198116317707320276562107 252297174476560980414843161)
  ·
    refine ⟨189222880857420735311132371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252297174476560980414843161 189222880857420735311132371)
    ·
      refine ⟨283834321286131102966698557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189222880857420735311132371 283834321286131102966698557)
      ·
        refine ⟨106437870482299163612511959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283834321286131102966698557 106437870482299163612511959)
        ·
          refine ⟨159656805723448745418767939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106437870482299163612511959 159656805723448745418767939)
          ·
            refine ⟨239485208585173118128151909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159656805723448745418767939 239485208585173118128151909)
            ·
              refine ⟨44903476609719959649028483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239485208585173118128151909 44903476609719959649028483)
              ·
                refine ⟨67355214914579939473542725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44903476609719959649028483 67355214914579939473542725)
                ·
                  refine ⟨12629102796483738651289261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67355214914579939473542725 12629102796483738651289261)
                  ·
                    refine ⟨4735913548681401994233473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12629102796483738651289261 4735913548681401994233473)
                    ·
                      refine ⟨3551935161511051495675105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735913548681401994233473 3551935161511051495675105)
                      ·
                        rfl

theorem cell23_6917369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_6917369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917369 prefixEnd_6917369 := by exact prefixLift 6917369
  have htrace : WordTrace (prefixWord ++ tailWord_6917369) baseStart_6917369 baseEnd_6917369 := by
    simpa [prefixWord, tailWord_6917369, baseEnd_6917369] using wordTrace_append hprefix tailTrace_6917369
  have hstable : (prefixWord ++ tailWord_6917369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917369).length < 2 ^ (prefixWord ++ tailWord_6917369).sum := by decide
  have hdescent : baseEnd_6917369 < baseStart_6917369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917399 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 2, 6, 2]
def baseStart_6917399 : Nat := 118140960795 + 6917399 * 2 ^ 59
def prefixEnd_6917399 : Nat := 4983230072969 + 3 ^ 40 * 6917399 * 2
def baseEnd_6917399 : Nat := 3551950565930686378299967

theorem tailTrace_6917399 : CollatzResearch.WordTrace tailWord_6917399 prefixEnd_6917399 3551950565930686378299967 := by
  unfold tailWord_6917399
  simp only [CollatzResearch.WordTrace]
  refine ⟨252298268666452295538435251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168198845777634863692290167 252298268666452295538435251)
  ·
    refine ⟨378447402999678443307652877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252298268666452295538435251 378447402999678443307652877)
    ·
      refine ⟨141917776124879416240369829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378447402999678443307652877 141917776124879416240369829)
      ·
        refine ⟨26609583023414890545069343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141917776124879416240369829 26609583023414890545069343)
        ·
          refine ⟨39914374535122335817604015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26609583023414890545069343 39914374535122335817604015)
          ·
            refine ⟨59871561802683503726406023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39914374535122335817604015 59871561802683503726406023)
            ·
              refine ⟨89807342704025255589609035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59871561802683503726406023 89807342704025255589609035)
              ·
                refine ⟨134711014056037883384413553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89807342704025255589609035 134711014056037883384413553)
                ·
                  refine ⟨101033260542028412538310165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134711014056037883384413553 101033260542028412538310165)
                  ·
                    refine ⟨4735934087907581837733289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101033260542028412538310165 4735934087907581837733289)
                    ·
                      refine ⟨3551950565930686378299967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4735934087907581837733289 3551950565930686378299967)
                      ·
                        rfl

theorem cell23_6917399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_6917399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917399 prefixEnd_6917399 := by exact prefixLift 6917399
  have htrace : WordTrace (prefixWord ++ tailWord_6917399) baseStart_6917399 baseEnd_6917399 := by
    simpa [prefixWord, tailWord_6917399, baseEnd_6917399] using wordTrace_append hprefix tailTrace_6917399
  have hstable : (prefixWord ++ tailWord_6917399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917399).length < 2 ^ (prefixWord ++ tailWord_6917399).sum := by decide
  have hdescent : baseEnd_6917399 < baseStart_6917399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917416 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_6917416 : Nat := 118140960795 + 6917416 * 2 ^ 59
def prefixEnd_6917416 : Nat := 4983230072969 + 3 ^ 40 * 6917416 * 2
def baseEnd_6917416 : Nat := 3551959295101812811787389

theorem tailTrace_6917416 : CollatzResearch.WordTrace tailWord_6917416 prefixEnd_6917416 3551959295101812811787389 := by
  unfold tailWord_6917416
  simp only [CollatzResearch.WordTrace]
  refine ⟨126149444353695353720902051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168199259138260471627869401 126149444353695353720902051)
  ·
    refine ⟨189224166530543030581353077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126149444353695353720902051 189224166530543030581353077)
    ·
      refine ⟨17739765612238409117001851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189224166530543030581353077 17739765612238409117001851)
      ·
        refine ⟨26609648418357613675502777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17739765612238409117001851 26609648418357613675502777)
        ·
          refine ⟨19957236313768210256627083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26609648418357613675502777 19957236313768210256627083)
          ·
            refine ⟨29935854470652315384940625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19957236313768210256627083 29935854470652315384940625)
            ·
              refine ⟨22451890852989236538705469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29935854470652315384940625 22451890852989236538705469)
              ·
                refine ⟨8419459069870963702014551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22451890852989236538705469 8419459069870963702014551)
                ·
                  refine ⟨12629188604806445553021827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8419459069870963702014551 12629188604806445553021827)
                  ·
                    refine ⟨18943782907209668329532741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12629188604806445553021827 18943782907209668329532741)
                    ·
                      refine ⟨3551959295101812811787389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18943782907209668329532741 3551959295101812811787389)
                      ·
                        rfl

theorem cell23_6917416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_6917416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917416 prefixEnd_6917416 := by exact prefixLift 6917416
  have htrace : WordTrace (prefixWord ++ tailWord_6917416) baseStart_6917416 baseEnd_6917416 := by
    simpa [prefixWord, tailWord_6917416, baseEnd_6917416] using wordTrace_append hprefix tailTrace_6917416
  have hstable : (prefixWord ++ tailWord_6917416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917416).length < 2 ^ (prefixWord ++ tailWord_6917416).sum := by decide
  have hdescent : baseEnd_6917416 < baseStart_6917416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917534 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_6917534 : Nat := 118140960795 + 6917534 * 2 ^ 59
def prefixEnd_6917534 : Nat := 4983230072969 + 3 ^ 40 * 6917534 * 2
def baseEnd_6917534 : Nat := 3552019885819043350111847

theorem tailTrace_6917534 : CollatzResearch.WordTrace tailWord_6917534 prefixEnd_6917534 3552019885819043350111847 := by
  unfold tailWord_6917534
  simp only [CollatzResearch.WordTrace]
  refine ⟨31537899065120401699324957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168202128347308809063066437 31537899065120401699324957)
  ·
    refine ⟨11826712149420150637246859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31537899065120401699324957 11826712149420150637246859)
    ·
      refine ⟨17740068224130225955870289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11826712149420150637246859 17740068224130225955870289)
      ·
        refine ⟨13305051168097669466902717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17740068224130225955870289 13305051168097669466902717)
        ·
          refine ⟨4989394188036626050088519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13305051168097669466902717 4989394188036626050088519)
          ·
            refine ⟨7484091282054939075132779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989394188036626050088519 7484091282054939075132779)
            ·
              refine ⟨11226136923082408612699169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7484091282054939075132779 11226136923082408612699169)
              ·
                refine ⟨8419602692311806459524377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11226136923082408612699169 8419602692311806459524377)
                ·
                  refine ⟨6314702019233854844643283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8419602692311806459524377 6314702019233854844643283)
                  ·
                    refine ⟨9472053028850782266964925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6314702019233854844643283 9472053028850782266964925)
                    ·
                      refine ⟨3552019885819043350111847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9472053028850782266964925 3552019885819043350111847)
                      ·
                        rfl

theorem cell23_6917534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_6917534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917534 prefixEnd_6917534 := by exact prefixLift 6917534
  have htrace : WordTrace (prefixWord ++ tailWord_6917534) baseStart_6917534 baseEnd_6917534 := by
    simpa [prefixWord, tailWord_6917534, baseEnd_6917534] using wordTrace_append hprefix tailTrace_6917534
  have hstable : (prefixWord ++ tailWord_6917534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917534).length < 2 ^ (prefixWord ++ tailWord_6917534).sum := by decide
  have hdescent : baseEnd_6917534 < baseStart_6917534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917539 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 3]
def baseStart_6917539 : Nat := 118140960795 + 6917539 * 2 ^ 59
def prefixEnd_6917539 : Nat := 4983230072969 + 3 ^ 40 * 6917539 * 2
def baseEnd_6917539 : Nat := 3552022453222315830549323

theorem tailTrace_6917539 : CollatzResearch.WordTrace tailWord_6917539 prefixEnd_6917539 3552022453222315830549323 := by
  unfold tailWord_6917539
  simp only [CollatzResearch.WordTrace]
  refine ⟨252303374885945099448531671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168202249923963399632354447 252303374885945099448531671)
  ·
    refine ⟨378455062328917649172797507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252303374885945099448531671 378455062328917649172797507)
    ·
      refine ⟨567682593493376473759196261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378455062328917649172797507 567682593493376473759196261)
      ·
        refine ⟨106440486280008088829849299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 567682593493376473759196261 106440486280008088829849299)
        ·
          refine ⟨159660729420012133244773949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106440486280008088829849299 159660729420012133244773949)
          ·
            refine ⟨59872773532504549966790231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159660729420012133244773949 59872773532504549966790231)
            ·
              refine ⟨89809160298756824950185347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59872773532504549966790231 89809160298756824950185347)
              ·
                refine ⟨134713740448135237425278021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89809160298756824950185347 134713740448135237425278021)
                ·
                  refine ⟨25258826334025357017239629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134713740448135237425278021 25258826334025357017239629)
                  ·
                    refine ⟨9472059875259508881464861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25258826334025357017239629 9472059875259508881464861)
                    ·
                      refine ⟨3552022453222315830549323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9472059875259508881464861 3552022453222315830549323)
                      ·
                        rfl

theorem cell23_6917539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_6917539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917539 prefixEnd_6917539 := by exact prefixLift 6917539
  have htrace : WordTrace (prefixWord ++ tailWord_6917539) baseStart_6917539 baseEnd_6917539 := by
    simpa [prefixWord, tailWord_6917539, baseEnd_6917539] using wordTrace_append hprefix tailTrace_6917539
  have hstable : (prefixWord ++ tailWord_6917539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917539).length < 2 ^ (prefixWord ++ tailWord_6917539).sum := by decide
  have hdescent : baseEnd_6917539 < baseStart_6917539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917557 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_6917557 : Nat := 118140960795 + 6917557 * 2 ^ 59
def prefixEnd_6917557 : Nat := 4983230072969 + 3 ^ 40 * 6917557 * 2
def baseEnd_6917557 : Nat := 3552031695874096760124241

theorem tailTrace_6917557 : CollatzResearch.WordTrace tailWord_6917557 prefixEnd_6917557 3552031695874096760124241 := by
  unfold tailWord_6917557
  simp only [CollatzResearch.WordTrace]
  refine ⟨252304031399879888522686925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168202687599919925681791283 252304031399879888522686925)
  ·
    refine ⟨94614011774954958196007597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252304031399879888522686925 94614011774954958196007597)
    ·
      refine ⟨35480254415608109323502849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94614011774954958196007597 35480254415608109323502849)
      ·
        refine ⟨26610190811706081992627137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35480254415608109323502849 26610190811706081992627137)
        ·
          refine ⟨19957643108779561494470353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26610190811706081992627137 19957643108779561494470353)
          ·
            refine ⟨14968232331584671120852765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19957643108779561494470353 14968232331584671120852765)
            ·
              refine ⟨5613087124344251670319787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14968232331584671120852765 5613087124344251670319787)
              ·
                refine ⟨8419630686516377505479681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5613087124344251670319787 8419630686516377505479681)
                ·
                  refine ⟨6314723014887283129109761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8419630686516377505479681 6314723014887283129109761)
                  ·
                    refine ⟨4736042261165462346832321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6314723014887283129109761 4736042261165462346832321)
                    ·
                      refine ⟨3552031695874096760124241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4736042261165462346832321 3552031695874096760124241)
                      ·
                        rfl

theorem cell23_6917557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_6917557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917557 prefixEnd_6917557 := by exact prefixLift 6917557
  have htrace : WordTrace (prefixWord ++ tailWord_6917557) baseStart_6917557 baseEnd_6917557 := by
    simpa [prefixWord, tailWord_6917557, baseEnd_6917557] using wordTrace_append hprefix tailTrace_6917557
  have hstable : (prefixWord ++ tailWord_6917557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917557).length < 2 ^ (prefixWord ++ tailWord_6917557).sum := by decide
  have hdescent : baseEnd_6917557 < baseStart_6917557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917579 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 4]
def baseStart_6917579 : Nat := 118140960795 + 6917579 * 2 ^ 59
def prefixEnd_6917579 : Nat := 4983230072969 + 3 ^ 40 * 6917579 * 2
def baseEnd_6917579 : Nat := 3552042992448495674049139

theorem tailTrace_6917579 : CollatzResearch.WordTrace tailWord_6917579 prefixEnd_6917579 3552042992448495674049139 := by
  unfold tailWord_6917579
  simp only [CollatzResearch.WordTrace]
  refine ⟨252304833805800186279987791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168203222537200124186658527 252304833805800186279987791)
  ·
    refine ⟨378457250708700279419981687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252304833805800186279987791 378457250708700279419981687)
    ·
      refine ⟨567685876063050419129972531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378457250708700279419981687 567685876063050419129972531)
      ·
        refine ⟨851528814094575628694958797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567685876063050419129972531 851528814094575628694958797)
        ·
          refine ⟨319323305285465860760609549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 851528814094575628694958797 319323305285465860760609549)
          ·
            refine ⟨119746239482049697785228581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319323305285465860760609549 119746239482049697785228581)
            ·
              refine ⟨22452419902884318334730359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119746239482049697785228581 22452419902884318334730359)
              ·
                refine ⟨33678629854326477502095539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22452419902884318334730359 33678629854326477502095539)
                ·
                  refine ⟨50517944781489716253143309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33678629854326477502095539 50517944781489716253143309)
                  ·
                    refine ⟨18944229293058643594928741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50517944781489716253143309 18944229293058643594928741)
                    ·
                      refine ⟨3552042992448495674049139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18944229293058643594928741 3552042992448495674049139)
                      ·
                        rfl

theorem cell23_6917579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 4].length) (baseStart_6917579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917579 prefixEnd_6917579 := by exact prefixLift 6917579
  have htrace : WordTrace (prefixWord ++ tailWord_6917579) baseStart_6917579 baseEnd_6917579 := by
    simpa [prefixWord, tailWord_6917579, baseEnd_6917579] using wordTrace_append hprefix tailTrace_6917579
  have hstable : (prefixWord ++ tailWord_6917579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917579).length < 2 ^ (prefixWord ++ tailWord_6917579).sum := by decide
  have hdescent : baseEnd_6917579 < baseStart_6917579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917666 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_6917666 : Nat := 118140960795 + 6917666 * 2 ^ 59
def prefixEnd_6917666 : Nat := 4983230072969 + 3 ^ 40 * 6917666 * 2
def baseEnd_6917666 : Nat := 1184029221755145611220413

theorem tailTrace_6917666 : CollatzResearch.WordTrace tailWord_6917666 prefixEnd_6917666 1184029221755145611220413 := by
  unfold tailWord_6917666
  simp only [CollatzResearch.WordTrace]
  refine ⟨63077001739121250034601213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168205337970990000092269901 63077001739121250034601213)
  ·
    refine ⟨23653875652170468762975455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63077001739121250034601213 23653875652170468762975455)
    ·
      refine ⟨35480813478255703144463183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23653875652170468762975455 35480813478255703144463183)
      ·
        refine ⟨53221220217383554716694775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35480813478255703144463183 53221220217383554716694775)
        ·
          refine ⟨79831830326075332075042163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53221220217383554716694775 79831830326075332075042163)
          ·
            refine ⟨119747745489112998112563245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79831830326075332075042163 119747745489112998112563245)
            ·
              refine ⟨44905404558417374292211217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119747745489112998112563245 44905404558417374292211217)
              ·
                refine ⟨33679053418813030719158413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44905404558417374292211217 33679053418813030719158413)
                ·
                  refine ⟨12629645032054886519684405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33679053418813030719158413 12629645032054886519684405)
                  ·
                    refine ⟨1184029221755145611220413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12629645032054886519684405 1184029221755145611220413)
                    ·
                      rfl

theorem cell23_6917666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_6917666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917666 prefixEnd_6917666 := by exact prefixLift 6917666
  have htrace : WordTrace (prefixWord ++ tailWord_6917666) baseStart_6917666 baseEnd_6917666 := by
    simpa [prefixWord, tailWord_6917666, baseEnd_6917666] using wordTrace_append hprefix tailTrace_6917666
  have hstable : (prefixWord ++ tailWord_6917666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917666).length < 2 ^ (prefixWord ++ tailWord_6917666).sum := by decide
  have hdescent : baseEnd_6917666 < baseStart_6917666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917696 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 4, 4]
def baseStart_6917696 : Nat := 118140960795 + 6917696 * 2 ^ 59
def prefixEnd_6917696 : Nat := 4983230072969 + 3 ^ 40 * 6917696 * 2
def baseEnd_6917696 : Nat := 1184034356561690572095367

theorem tailTrace_6917696 : CollatzResearch.WordTrace tailWord_6917696 prefixEnd_6917696 1184034356561690572095367 := by
  unfold tailWord_6917696
  simp only [CollatzResearch.WordTrace]
  refine ⟨126154550573188157630998471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168206067430917543507997961 126154550573188157630998471)
  ·
    refine ⟨189231825859782236446497707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126154550573188157630998471 189231825859782236446497707)
    ·
      refine ⟨283847738789673354669746561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189231825859782236446497707 283847738789673354669746561)
      ·
        refine ⟨212885804092255016002309921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283847738789673354669746561 212885804092255016002309921)
        ·
          refine ⟨159664353069191262001732441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212885804092255016002309921 159664353069191262001732441)
          ·
            refine ⟨119748264801893446501299331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159664353069191262001732441 119748264801893446501299331)
            ·
              refine ⟨179622397202840169751948997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119748264801893446501299331 179622397202840169751948997)
              ·
                refine ⟨33679199475532531828490437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179622397202840169751948997 33679199475532531828490437)
                ·
                  refine ⟨6314849901662349717841957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33679199475532531828490437 6314849901662349717841957)
                  ·
                    refine ⟨1184034356561690572095367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6314849901662349717841957 1184034356561690572095367)
                    ·
                      rfl

theorem cell23_6917696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4, 4].length) (baseStart_6917696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917696 prefixEnd_6917696 := by exact prefixLift 6917696
  have htrace : WordTrace (prefixWord ++ tailWord_6917696) baseStart_6917696 baseEnd_6917696 := by
    simpa [prefixWord, tailWord_6917696, baseEnd_6917696] using wordTrace_append hprefix tailTrace_6917696
  have hstable : (prefixWord ++ tailWord_6917696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917696).length < 2 ^ (prefixWord ++ tailWord_6917696).sum := by decide
  have hdescent : baseEnd_6917696 < baseStart_6917696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917697 : List Nat := [1, 2, 5, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_6917697 : Nat := 118140960795 + 6917697 * 2 ^ 59
def prefixEnd_6917697 : Nat := 4983230072969 + 3 ^ 40 * 6917697 * 2
def baseEnd_6917697 : Nat := 3552103583165726212373597

theorem tailTrace_6917697 : CollatzResearch.WordTrace tailWord_6917697 prefixEnd_6917697 3552103583165726212373597 := by
  unfold tailWord_6917697
  simp only [CollatzResearch.WordTrace]
  refine ⟨252309137619372692432783345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168206091746248461621855563 252309137619372692432783345)
  ·
    refine ⟨189231853214529519324587509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252309137619372692432783345 189231853214529519324587509)
    ·
      refine ⟨17740486238862142436680079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189231853214529519324587509 17740486238862142436680079)
      ·
        refine ⟨26610729358293213655020119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17740486238862142436680079 26610729358293213655020119)
        ·
          refine ⟨39916094037439820482530179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26610729358293213655020119 39916094037439820482530179)
          ·
            refine ⟨59874141056159730723795269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39916094037439820482530179 59874141056159730723795269)
            ·
              refine ⟨11226401448029949510711613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59874141056159730723795269 11226401448029949510711613)
              ·
                refine ⟨4209900543011231066516855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11226401448029949510711613 4209900543011231066516855)
                ·
                  refine ⟨6314850814516846599775283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209900543011231066516855 6314850814516846599775283)
                  ·
                    refine ⟨9472276221775269899662925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6314850814516846599775283 9472276221775269899662925)
                    ·
                      refine ⟨3552103583165726212373597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9472276221775269899662925 3552103583165726212373597)
                      ·
                        rfl

theorem cell23_6917697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_6917697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917697 prefixEnd_6917697 := by exact prefixLift 6917697
  have htrace : WordTrace (prefixWord ++ tailWord_6917697) baseStart_6917697 baseEnd_6917697 := by
    simpa [prefixWord, tailWord_6917697, baseEnd_6917697] using wordTrace_append hprefix tailTrace_6917697
  have hstable : (prefixWord ++ tailWord_6917697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917697).length < 2 ^ (prefixWord ++ tailWord_6917697).sum := by decide
  have hdescent : baseEnd_6917697 < baseStart_6917697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917699 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 6]
def baseStart_6917699 : Nat := 118140960795 + 6917699 * 2 ^ 59
def prefixEnd_6917699 : Nat := 4983230072969 + 3 ^ 40 * 6917699 * 2
def baseEnd_6917699 : Nat := 3552104610127035204548587

theorem tailTrace_6917699 : CollatzResearch.WordTrace tailWord_6917699 prefixEnd_6917699 3552104610127035204548587 := by
  unfold tailWord_6917699
  simp only [CollatzResearch.WordTrace]
  refine ⟨252309210565365446774356151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168206140376910297849570767 252309210565365446774356151)
  ·
    refine ⟨378463815848048170161534227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252309210565365446774356151 378463815848048170161534227)
    ·
      refine ⟨567695723772072255242301341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378463815848048170161534227 567695723772072255242301341)
      ·
        refine ⟨212885896414527095715863003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 567695723772072255242301341 212885896414527095715863003)
        ·
          refine ⟨319328844621790643573794505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212885896414527095715863003 319328844621790643573794505)
          ·
            refine ⟨239496633466342982680345879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319328844621790643573794505 239496633466342982680345879)
            ·
              refine ⟨359244950199514474020518819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239496633466342982680345879 359244950199514474020518819)
              ·
                refine ⟨538867425299271711030778229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359244950199514474020518819 538867425299271711030778229)
                ·
                  refine ⟨50518821121806722909135459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 538867425299271711030778229 50518821121806722909135459)
                  ·
                    refine ⟨75778231682710084363703189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50518821121806722909135459 75778231682710084363703189)
                    ·
                      refine ⟨3552104610127035204548587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75778231682710084363703189 3552104610127035204548587)
                      ·
                        rfl

theorem cell23_6917699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_6917699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917699 prefixEnd_6917699 := by exact prefixLift 6917699
  have htrace : WordTrace (prefixWord ++ tailWord_6917699) baseStart_6917699 baseEnd_6917699 := by
    simpa [prefixWord, tailWord_6917699, baseEnd_6917699] using wordTrace_append hprefix tailTrace_6917699
  have hstable : (prefixWord ++ tailWord_6917699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917699).length < 2 ^ (prefixWord ++ tailWord_6917699).sum := by decide
  have hdescent : baseEnd_6917699 < baseStart_6917699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917706 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_6917706 : Nat := 118140960795 + 6917706 * 2 ^ 59
def prefixEnd_6917706 : Nat := 4983230072969 + 3 ^ 40 * 6917706 * 2
def baseEnd_6917706 : Nat := 3552108204491616677161055

theorem tailTrace_6917706 : CollatzResearch.WordTrace tailWord_6917706 prefixEnd_6917706 3552108204491616677161055 := by
  unfold tailWord_6917706
  simp only [CollatzResearch.WordTrace]
  refine ⟨63077366469085021742465243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168206310584226724646573981 63077366469085021742465243)
  ·
    refine ⟨94616049703627532613697865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63077366469085021742465243 94616049703627532613697865)
    ·
      refine ⟨70962037277720649460273399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94616049703627532613697865 70962037277720649460273399)
      ·
        refine ⟨106443055916580974190410099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70962037277720649460273399 106443055916580974190410099)
        ·
          refine ⟨159664583874871461285615149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106443055916580974190410099 159664583874871461285615149)
          ·
            refine ⟨59874218953076797982105681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159664583874871461285615149 59874218953076797982105681)
            ·
              refine ⟨44905664214807598486579261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59874218953076797982105681 44905664214807598486579261)
              ·
                refine ⟨16839624080552849432467223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44905664214807598486579261 16839624080552849432467223)
                ·
                  refine ⟨25259436120829274148700835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16839624080552849432467223 25259436120829274148700835)
                  ·
                    refine ⟨37889154181243911223051253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25259436120829274148700835 37889154181243911223051253)
                    ·
                      refine ⟨3552108204491616677161055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37889154181243911223051253 3552108204491616677161055)
                      ·
                        rfl

theorem cell23_6917706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_6917706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917706 prefixEnd_6917706 := by exact prefixLift 6917706
  have htrace : WordTrace (prefixWord ++ tailWord_6917706) baseStart_6917706 baseEnd_6917706 := by
    simpa [prefixWord, tailWord_6917706, baseEnd_6917706] using wordTrace_append hprefix tailTrace_6917706
  have hstable : (prefixWord ++ tailWord_6917706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917706).length < 2 ^ (prefixWord ++ tailWord_6917706).sum := by decide
  have hdescent : baseEnd_6917706 < baseStart_6917706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917716 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_6917716 : Nat := 118140960795 + 6917716 * 2 ^ 59
def prefixEnd_6917716 : Nat := 4983230072969 + 3 ^ 40 * 6917716 * 2
def baseEnd_6917716 : Nat := 3552113339298161638036009

theorem tailTrace_6917716 : CollatzResearch.WordTrace tailWord_6917716 prefixEnd_6917716 3552113339298161638036009 := by
  unfold tailWord_6917716
  simp only [CollatzResearch.WordTrace]
  refine ⟨126154915303151929338862501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168206553737535905785150001 126154915303151929338862501)
  ·
    refine ⟨23654046619340986751036719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126154915303151929338862501 23654046619340986751036719)
    ·
      refine ⟨35481069929011480126555079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23654046619340986751036719 35481069929011480126555079)
      ·
        refine ⟨53221604893517220189832619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35481069929011480126555079 53221604893517220189832619)
        ·
          refine ⟨79832407340275830284748929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53221604893517220189832619 79832407340275830284748929)
          ·
            refine ⟨59874305505206872713561697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79832407340275830284748929 59874305505206872713561697)
            ·
              refine ⟨44905729128905154535171273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59874305505206872713561697 44905729128905154535171273)
              ·
                refine ⟨33679296846678865901378455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44905729128905154535171273 33679296846678865901378455)
                ·
                  refine ⟨50518945270018298852067683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33679296846678865901378455 50518945270018298852067683)
                  ·
                    refine ⟨75778417905027448278101525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50518945270018298852067683 75778417905027448278101525)
                    ·
                      refine ⟨3552113339298161638036009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75778417905027448278101525 3552113339298161638036009)
                      ·
                        rfl

theorem cell23_6917716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_6917716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917716 prefixEnd_6917716 := by exact prefixLift 6917716
  have htrace : WordTrace (prefixWord ++ tailWord_6917716) baseStart_6917716 baseEnd_6917716 := by
    simpa [prefixWord, tailWord_6917716, baseEnd_6917716] using wordTrace_append hprefix tailTrace_6917716
  have hstable : (prefixWord ++ tailWord_6917716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917716).length < 2 ^ (prefixWord ++ tailWord_6917716).sum := by decide
  have hdescent : baseEnd_6917716 < baseStart_6917716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917733 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 4]
def baseStart_6917733 : Nat := 118140960795 + 6917733 * 2 ^ 59
def prefixEnd_6917733 : Nat := 4983230072969 + 3 ^ 40 * 6917733 * 2
def baseEnd_6917733 : Nat := 3552122068469288071523431

theorem tailTrace_6917733 : CollatzResearch.WordTrace tailWord_6917733 prefixEnd_6917733 3552122068469288071523431 := by
  unfold tailWord_6917733
  simp only [CollatzResearch.WordTrace]
  refine ⟨252310450647242270581093853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168206967098161513720729235 252310450647242270581093853)
  ·
    refine ⟨94616418992715851467910195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252310450647242270581093853 94616418992715851467910195)
    ·
      refine ⟨141924628489073777201865293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94616418992715851467910195 141924628489073777201865293)
      ·
        refine ⟨53221735683402666450699485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141924628489073777201865293 53221735683402666450699485)
        ·
          refine ⟨19958150881275999919012307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53221735683402666450699485 19958150881275999919012307)
          ·
            refine ⟨29937226321913999878518461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19958150881275999919012307 29937226321913999878518461)
            ·
              refine ⟨11226459870717749954444423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29937226321913999878518461 11226459870717749954444423)
              ·
                refine ⟨16839689806076624931666635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11226459870717749954444423 16839689806076624931666635)
                ·
                  refine ⟨25259534709114937397499953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16839689806076624931666635 25259534709114937397499953)
                  ·
                    refine ⟨18944651031836203048124965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25259534709114937397499953 18944651031836203048124965)
                    ·
                      refine ⟨3552122068469288071523431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18944651031836203048124965 3552122068469288071523431)
                      ·
                        rfl

theorem cell23_6917733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_6917733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917733 prefixEnd_6917733 := by exact prefixLift 6917733
  have htrace : WordTrace (prefixWord ++ tailWord_6917733) baseStart_6917733 baseEnd_6917733 := by
    simpa [prefixWord, tailWord_6917733, baseEnd_6917733] using wordTrace_append hprefix tailTrace_6917733
  have hstable : (prefixWord ++ tailWord_6917733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917733).length < 2 ^ (prefixWord ++ tailWord_6917733).sum := by decide
  have hdescent : baseEnd_6917733 < baseStart_6917733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917739 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 3, 9]
def baseStart_6917739 : Nat := 118140960795 + 6917739 * 2 ^ 59
def prefixEnd_6917739 : Nat := 4983230072969 + 3 ^ 40 * 6917739 * 2
def baseEnd_6917739 : Nat := 1184041716451071682682801

theorem tailTrace_6917739 : CollatzResearch.WordTrace tailWord_6917739 prefixEnd_6917739 1184041716451071682682801 := by
  unfold tailWord_6917739
  simp only [CollatzResearch.WordTrace]
  refine ⟨252310669485220533605812271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168207112990147022403874847 252310669485220533605812271)
  ·
    refine ⟨378466004227830800408718407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252310669485220533605812271 378466004227830800408718407)
    ·
      refine ⟨567699006341746200613077611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378466004227830800408718407 567699006341746200613077611)
      ·
        refine ⟨851548509512619300919616417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567699006341746200613077611 851548509512619300919616417)
        ·
          refine ⟨638661382134464475689712313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851548509512619300919616417 638661382134464475689712313)
          ·
            refine ⟨478996036600848356767284235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638661382134464475689712313 478996036600848356767284235)
            ·
              refine ⟨718494054901272535150926353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478996036600848356767284235 718494054901272535150926353)
              ·
                refine ⟨538870541175954401363194765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718494054901272535150926353 538870541175954401363194765)
                ·
                  refine ⟨202076452940982900511198037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538870541175954401363194765 202076452940982900511198037)
                  ·
                    refine ⟨1184041716451071682682801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 202076452940982900511198037 1184041716451071682682801)
                    ·
                      rfl

theorem cell23_6917739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 9].length) (baseStart_6917739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917739 prefixEnd_6917739 := by exact prefixLift 6917739
  have htrace : WordTrace (prefixWord ++ tailWord_6917739) baseStart_6917739 baseEnd_6917739 := by
    simpa [prefixWord, tailWord_6917739, baseEnd_6917739] using wordTrace_append hprefix tailTrace_6917739
  have hstable : (prefixWord ++ tailWord_6917739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917739).length < 2 ^ (prefixWord ++ tailWord_6917739).sum := by decide
  have hdescent : baseEnd_6917739 < baseStart_6917739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917753 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 6, 1, 3]
def baseStart_6917753 : Nat := 118140960795 + 6917753 * 2 ^ 59
def prefixEnd_6917753 : Nat := 4983230072969 + 3 ^ 40 * 6917753 * 2
def baseEnd_6917753 : Nat := 3552132338082377993273339

theorem tailTrace_6917753 : CollatzResearch.WordTrace tailWord_6917753 prefixEnd_6917753 3552132338082377993273339 := by
  unfold tailWord_6917753
  simp only [CollatzResearch.WordTrace]
  refine ⟨252311180107169813996821913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168207453404779875997881275 252311180107169813996821913)
  ·
    refine ⟨189233385080377360497616435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252311180107169813996821913 189233385080377360497616435)
    ·
      refine ⟨283850077620566040746424653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189233385080377360497616435 283850077620566040746424653)
      ·
        refine ⟨106443779107712265279909245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283850077620566040746424653 106443779107712265279909245)
        ·
          refine ⟨39916417165392099479965967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106443779107712265279909245 39916417165392099479965967)
          ·
            refine ⟨59874625748088149219948951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39916417165392099479965967 59874625748088149219948951)
            ·
              refine ⟨89811938622132223829923427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59874625748088149219948951 89811938622132223829923427)
              ·
                refine ⟨134717907933198335744885141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89811938622132223829923427 134717907933198335744885141)
                ·
                  refine ⟨6314901934368671988041491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134717907933198335744885141 6314901934368671988041491)
                  ·
                    refine ⟨9472352901553007982062237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6314901934368671988041491 9472352901553007982062237)
                    ·
                      refine ⟨3552132338082377993273339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9472352901553007982062237 3552132338082377993273339)
                      ·
                        rfl

theorem cell23_6917753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_6917753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917753 prefixEnd_6917753 := by exact prefixLift 6917753
  have htrace : WordTrace (prefixWord ++ tailWord_6917753) baseStart_6917753 baseEnd_6917753 := by
    simpa [prefixWord, tailWord_6917753, baseEnd_6917753] using wordTrace_append hprefix tailTrace_6917753
  have hstable : (prefixWord ++ tailWord_6917753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917753).length < 2 ^ (prefixWord ++ tailWord_6917753).sum := by decide
  have hdescent : baseEnd_6917753 < baseStart_6917753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917763 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 5, 3, 2]
def baseStart_6917763 : Nat := 118140960795 + 6917763 * 2 ^ 59
def prefixEnd_6917763 : Nat := 4983230072969 + 3 ^ 40 * 6917763 * 2
def baseEnd_6917763 : Nat := 3552137472888922954148293

theorem tailTrace_6917763 : CollatzResearch.WordTrace tailWord_6917763 prefixEnd_6917763 3552137472888922954148293 := by
  unfold tailWord_6917763
  simp only [CollatzResearch.WordTrace]
  refine ⟨252311544837133585704685943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168207696558089057136457295 252311544837133585704685943)
  ·
    refine ⟨378467317255700378557028915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252311544837133585704685943 378467317255700378557028915)
    ·
      refine ⟨567700975883550567835543373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378467317255700378557028915 567700975883550567835543373)
      ·
        refine ⟨212887865956331462938328765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 567700975883550567835543373 212887865956331462938328765)
        ·
          refine ⟨79832949733624298601873287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212887865956331462938328765 79832949733624298601873287)
          ·
            refine ⟨119749424600436447902809931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79832949733624298601873287 119749424600436447902809931)
            ·
              refine ⟨179624136900654671854214897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119749424600436447902809931 179624136900654671854214897)
              ·
                refine ⟨134718102675491003890661173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179624136900654671854214897 134718102675491003890661173)
                ·
                  refine ⟨12629822125827281614749485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134718102675491003890661173 12629822125827281614749485)
                  ·
                    refine ⟨4736183297185230605531057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12629822125827281614749485 4736183297185230605531057)
                    ·
                      refine ⟨3552137472888922954148293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4736183297185230605531057 3552137472888922954148293)
                      ·
                        rfl

theorem cell23_6917763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 3, 2].length) (baseStart_6917763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917763 prefixEnd_6917763 := by exact prefixLift 6917763
  have htrace : WordTrace (prefixWord ++ tailWord_6917763) baseStart_6917763 baseEnd_6917763 := by
    simpa [prefixWord, tailWord_6917763, baseEnd_6917763] using wordTrace_append hprefix tailTrace_6917763
  have hstable : (prefixWord ++ tailWord_6917763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917763).length < 2 ^ (prefixWord ++ tailWord_6917763).sum := by decide
  have hdescent : baseEnd_6917763 < baseStart_6917763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917770 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_6917770 : Nat := 118140960795 + 6917770 * 2 ^ 59
def prefixEnd_6917770 : Nat := 4983230072969 + 3 ^ 40 * 6917770 * 2
def baseEnd_6917770 : Nat := 3552141067253504426760761

theorem tailTrace_6917770 : CollatzResearch.WordTrace tailWord_6917770 prefixEnd_6917770 3552141067253504426760761 := by
  unfold tailWord_6917770
  simp only [CollatzResearch.WordTrace]
  refine ⟨63077950037027056475047691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168207866765405483933460509 63077950037027056475047691)
  ·
    refine ⟨94616925055540584712571537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63077950037027056475047691 94616925055540584712571537)
    ·
      refine ⟨70962693791655438534428653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94616925055540584712571537 70962693791655438534428653)
      ·
        refine ⟨26611010171870789450410745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70962693791655438534428653 26611010171870789450410745)
        ·
          refine ⟨19958257628903092087808059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26611010171870789450410745 19958257628903092087808059)
          ·
            refine ⟨29937386443354638131712089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19958257628903092087808059 29937386443354638131712089)
            ·
              refine ⟨22453039832515978598784067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29937386443354638131712089 22453039832515978598784067)
              ·
                refine ⟨33679559748773967898176101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22453039832515978598784067 33679559748773967898176101)
                ·
                  refine ⟨6314917452895118980908019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33679559748773967898176101 6314917452895118980908019)
                  ·
                    refine ⟨9472376179342678471362029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6314917452895118980908019 9472376179342678471362029)
                    ·
                      refine ⟨3552141067253504426760761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9472376179342678471362029 3552141067253504426760761)
                      ·
                        rfl

theorem cell23_6917770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_6917770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917770 prefixEnd_6917770 := by exact prefixLift 6917770
  have htrace : WordTrace (prefixWord ++ tailWord_6917770) baseStart_6917770 baseEnd_6917770 := by
    simpa [prefixWord, tailWord_6917770, baseEnd_6917770] using wordTrace_append hprefix tailTrace_6917770
  have hstable : (prefixWord ++ tailWord_6917770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917770).length < 2 ^ (prefixWord ++ tailWord_6917770).sum := by decide
  have hdescent : baseEnd_6917770 < baseStart_6917770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917810 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2]
def baseStart_6917810 : Nat := 118140960795 + 6917810 * 2 ^ 59
def prefixEnd_6917810 : Nat := 4983230072969 + 3 ^ 40 * 6917810 * 2
def baseEnd_6917810 : Nat := 3552161606479684270260577

theorem tailTrace_6917810 : CollatzResearch.WordTrace tailWord_6917810 prefixEnd_6917810 3552161606479684270260577 := by
  unfold tailWord_6917810
  simp only [CollatzResearch.WordTrace]
  refine ⟨63078314766990828182911721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168208839378642208487764589 63078314766990828182911721)
  ·
    refine ⟨47308736075243121137183791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63078314766990828182911721 47308736075243121137183791)
    ·
      refine ⟨70963104112864681705775687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47308736075243121137183791 70963104112864681705775687)
      ·
        refine ⟨106444656169297022558663531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70963104112864681705775687 106444656169297022558663531)
        ·
          refine ⟨159666984253945533837995297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106444656169297022558663531 159666984253945533837995297)
          ·
            refine ⟨119750238190459150378496473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159666984253945533837995297 119750238190459150378496473)
            ·
              refine ⟨89812678642844362783872355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119750238190459150378496473 89812678642844362783872355)
              ·
                refine ⟨134719017964266544175808533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89812678642844362783872355 134719017964266544175808533)
                ·
                  refine ⟨6314953967074994258241025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134719017964266544175808533 6314953967074994258241025)
                  ·
                    refine ⟨4736215475306245693680769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6314953967074994258241025 4736215475306245693680769)
                    ·
                      refine ⟨3552161606479684270260577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4736215475306245693680769 3552161606479684270260577)
                      ·
                        rfl

theorem cell23_6917810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_6917810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917810 prefixEnd_6917810 := by exact prefixLift 6917810
  have htrace : WordTrace (prefixWord ++ tailWord_6917810) baseStart_6917810 baseEnd_6917810 := by
    simpa [prefixWord, tailWord_6917810, baseEnd_6917810] using wordTrace_append hprefix tailTrace_6917810
  have hstable : (prefixWord ++ tailWord_6917810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917810).length < 2 ^ (prefixWord ++ tailWord_6917810).sum := by decide
  have hdescent : baseEnd_6917810 < baseStart_6917810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917844 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_6917844 : Nat := 118140960795 + 6917844 * 2 ^ 59
def prefixEnd_6917844 : Nat := 4983230072969 + 3 ^ 40 * 6917844 * 2
def baseEnd_6917844 : Nat := 3552179064821937137235421

theorem tailTrace_6917844 : CollatzResearch.WordTrace tailWord_6917844 prefixEnd_6917844 3552179064821937137235421 := by
  unfold tailWord_6917844
  simp only [CollatzResearch.WordTrace]
  refine ⟨126157249574920068269192293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168209666099893424358923057 126157249574920068269192293)
  ·
    refine ⟨23654484295297512800473555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126157249574920068269192293 23654484295297512800473555)
    ·
      refine ⟨35481726442946269200710333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23654484295297512800473555 35481726442946269200710333)
      ·
        refine ⟨13305647416104850950266375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35481726442946269200710333 13305647416104850950266375)
        ·
          refine ⟨19958471124157276425399563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13305647416104850950266375 19958471124157276425399563)
          ·
            refine ⟨29937706686235914638099345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19958471124157276425399563 29937706686235914638099345)
            ·
              refine ⟨22453280014676935978574509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29937706686235914638099345 22453280014676935978574509)
              ·
                refine ⟨8419980005503850991965441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22453280014676935978574509 8419980005503850991965441)
                ·
                  refine ⟨6314985004127888243974081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8419980005503850991965441 6314985004127888243974081)
                  ·
                    refine ⟨4736238753095916182980561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6314985004127888243974081 4736238753095916182980561)
                    ·
                      refine ⟨3552179064821937137235421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4736238753095916182980561 3552179064821937137235421)
                      ·
                        rfl

theorem cell23_6917844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_6917844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917844 prefixEnd_6917844 := by exact prefixLift 6917844
  have htrace : WordTrace (prefixWord ++ tailWord_6917844) baseStart_6917844 baseEnd_6917844 := by
    simpa [prefixWord, tailWord_6917844, baseEnd_6917844] using wordTrace_append hprefix tailTrace_6917844
  have hstable : (prefixWord ++ tailWord_6917844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917844).length < 2 ^ (prefixWord ++ tailWord_6917844).sum := by decide
  have hdescent : baseEnd_6917844 < baseStart_6917844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917856 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_6917856 : Nat := 118140960795 + 6917856 * 2 ^ 59
def prefixEnd_6917856 : Nat := 4983230072969 + 3 ^ 40 * 6917856 * 2
def baseEnd_6917856 : Nat := 3552185226589791090285365

theorem tailTrace_6917856 : CollatzResearch.WordTrace tailWord_6917856 prefixEnd_6917856 3552185226589791090285365 := by
  unfold tailWord_6917856
  simp only [CollatzResearch.WordTrace]
  refine ⟨126157468412898331293910711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168209957883864441725214281 126157468412898331293910711)
  ·
    refine ⟨189236202619347496940866067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126157468412898331293910711 189236202619347496940866067)
    ·
      refine ⟨283854303929021245411299101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189236202619347496940866067 283854303929021245411299101)
      ·
        refine ⟨106445363973382967029237163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283854303929021245411299101 106445363973382967029237163)
        ·
          refine ⟨159668045960074450543855745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106445363973382967029237163 159668045960074450543855745)
          ·
            refine ⟨119751034470055837907891809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159668045960074450543855745 119751034470055837907891809)
            ·
              refine ⟨89813275852541878430918857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119751034470055837907891809 89813275852541878430918857)
              ·
                refine ⟨67359956889406408823189143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89813275852541878430918857 67359956889406408823189143)
                ·
                  refine ⟨101039935334109613234783715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67359956889406408823189143 101039935334109613234783715)
                  ·
                    refine ⟨151559903001164419852175573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101039935334109613234783715 151559903001164419852175573)
                    ·
                      refine ⟨3552185226589791090285365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151559903001164419852175573 3552185226589791090285365)
                      ·
                        rfl

theorem cell23_6917856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_6917856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917856 prefixEnd_6917856 := by exact prefixLift 6917856
  have htrace : WordTrace (prefixWord ++ tailWord_6917856) baseStart_6917856 baseEnd_6917856 := by
    simpa [prefixWord, tailWord_6917856, baseEnd_6917856] using wordTrace_append hprefix tailTrace_6917856
  have hstable : (prefixWord ++ tailWord_6917856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917856).length < 2 ^ (prefixWord ++ tailWord_6917856).sum := by decide
  have hdescent : baseEnd_6917856 < baseStart_6917856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917900 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 2, 4, 2]
def baseStart_6917900 : Nat := 118140960795 + 6917900 * 2 ^ 59
def prefixEnd_6917900 : Nat := 4983230072969 + 3 ^ 40 * 6917900 * 2
def baseEnd_6917900 : Nat := 3552207819738588918135163

theorem tailTrace_6917900 : CollatzResearch.WordTrace tailWord_6917900 prefixEnd_6917900 3552207819738588918135163 := by
  unfold tailWord_6917900
  simp only [CollatzResearch.WordTrace]
  refine ⟨126158270818818629051211577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168211027758424838734948769 126158270818818629051211577)
  ·
    refine ⟨94618703114113971788408683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126158270818818629051211577 94618703114113971788408683)
    ·
      refine ⟨141928054671170957682613025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94618703114113971788408683 141928054671170957682613025)
      ·
        refine ⟨106446041003378218261959769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141928054671170957682613025 106446041003378218261959769)
        ·
          refine ⟨79834530752533663696469827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106446041003378218261959769 79834530752533663696469827)
          ·
            refine ⟨119751796128800495544704741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79834530752533663696469827 119751796128800495544704741)
            ·
              refine ⟨22453461774150092914632139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119751796128800495544704741 22453461774150092914632139)
              ·
                refine ⟨33680192661225139371948209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22453461774150092914632139 33680192661225139371948209)
                ·
                  refine ⟨25260144495918854528961157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33680192661225139371948209 25260144495918854528961157)
                  ·
                    refine ⟨4736277092984785224180217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25260144495918854528961157 4736277092984785224180217)
                    ·
                      refine ⟨3552207819738588918135163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4736277092984785224180217 3552207819738588918135163)
                      ·
                        rfl

theorem cell23_6917900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_6917900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917900 prefixEnd_6917900 := by exact prefixLift 6917900
  have htrace : WordTrace (prefixWord ++ tailWord_6917900) baseStart_6917900 baseEnd_6917900 := by
    simpa [prefixWord, tailWord_6917900, baseEnd_6917900] using wordTrace_append hprefix tailTrace_6917900
  have hstable : (prefixWord ++ tailWord_6917900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917900).length < 2 ^ (prefixWord ++ tailWord_6917900).sum := by decide
  have hdescent : baseEnd_6917900 < baseStart_6917900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917903 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 3]
def baseStart_6917903 : Nat := 118140960795 + 6917903 * 2 ^ 59
def prefixEnd_6917903 : Nat := 4983230072969 + 3 ^ 40 * 6917903 * 2
def baseEnd_6917903 : Nat := 3552209360180552406397649

theorem tailTrace_6917903 : CollatzResearch.WordTrace tailWord_6917903 prefixEnd_6917903 3552209360180552406397649 := by
  unfold tailWord_6917903
  simp only [CollatzResearch.WordTrace]
  refine ⟨252316651056626389614782363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168211100704417593076521575 252316651056626389614782363)
  ·
    refine ⟨378474976584939584422173545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252316651056626389614782363 378474976584939584422173545)
    ·
      refine ⟨283856232438704688316630159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378474976584939584422173545 283856232438704688316630159)
      ·
        refine ⟨425784348658057032474945239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283856232438704688316630159 425784348658057032474945239)
        ·
          refine ⟨638676522987085548712417859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425784348658057032474945239 638676522987085548712417859)
          ·
            refine ⟨958014784480628323068626789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638676522987085548712417859 958014784480628323068626789)
            ·
              refine ⟨179627772090117810575367523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 958014784480628323068626789 179627772090117810575367523)
              ·
                refine ⟨269441658135176715863051285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179627772090117810575367523 269441658135176715863051285)
                ·
                  refine ⟨12630077725086408556080529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 269441658135176715863051285 12630077725086408556080529)
                  ·
                    refine ⟨9472558293814806417060397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12630077725086408556080529 9472558293814806417060397)
                    ·
                      refine ⟨3552209360180552406397649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9472558293814806417060397 3552209360180552406397649)
                      ·
                        rfl

theorem cell23_6917903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 3].length) (baseStart_6917903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917903 prefixEnd_6917903 := by exact prefixLift 6917903
  have htrace : WordTrace (prefixWord ++ tailWord_6917903) baseStart_6917903 baseEnd_6917903 := by
    simpa [prefixWord, tailWord_6917903, baseEnd_6917903] using wordTrace_append hprefix tailTrace_6917903
  have hstable : (prefixWord ++ tailWord_6917903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917903).length < 2 ^ (prefixWord ++ tailWord_6917903).sum := by decide
  have hdescent : baseEnd_6917903 < baseStart_6917903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917918 : List Nat := [4, 3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_6917918 : Nat := 118140960795 + 6917918 * 2 ^ 59
def prefixEnd_6917918 : Nat := 4983230072969 + 3 ^ 40 * 6917918 * 2
def baseEnd_6917918 : Nat := 394690784710041094190009

theorem tailTrace_6917918 : CollatzResearch.WordTrace tailWord_6917918 prefixEnd_6917918 394690784710041094190009 := by
  unfold tailWord_6917918
  simp only [CollatzResearch.WordTrace]
  refine ⟨31539649768946505897072301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168211465434381364784385605 31539649768946505897072301)
  ·
    refine ⟨11827368663354939711402113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31539649768946505897072301 11827368663354939711402113)
    ·
      refine ⟨8870526497516204783551585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11827368663354939711402113 8870526497516204783551585)
      ·
        refine ⟨6652894873137153587663689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8870526497516204783551585 6652894873137153587663689)
        ·
          refine ⟨4989671154852865190747767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6652894873137153587663689 4989671154852865190747767)
          ·
            refine ⟨7484506732279297786121651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989671154852865190747767 7484506732279297786121651)
            ·
              refine ⟨11226760098418946679182477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7484506732279297786121651 11226760098418946679182477)
              ·
                refine ⟨4210035036907105004693429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11226760098418946679182477 4210035036907105004693429)
                ·
                  refine ⟨394690784710041094190009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4210035036907105004693429 394690784710041094190009)
                  ·
                    rfl

theorem cell23_6917918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_6917918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917918 prefixEnd_6917918 := by exact prefixLift 6917918
  have htrace : WordTrace (prefixWord ++ tailWord_6917918) baseStart_6917918 baseEnd_6917918 := by
    simpa [prefixWord, tailWord_6917918, baseEnd_6917918] using wordTrace_append hprefix tailTrace_6917918
  have hstable : (prefixWord ++ tailWord_6917918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917918).length < 2 ^ (prefixWord ++ tailWord_6917918).sum := by decide
  have hdescent : baseEnd_6917918 < baseStart_6917918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917920 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 3]
def baseStart_6917920 : Nat := 118140960795 + 6917920 * 2 ^ 59
def prefixEnd_6917920 : Nat := 4983230072969 + 3 ^ 40 * 6917920 * 2
def baseEnd_6917920 : Nat := 3552218089351678839885071

theorem tailTrace_6917920 : CollatzResearch.WordTrace tailWord_6917920 prefixEnd_6917920 3552218089351678839885071 := by
  unfold tailWord_6917920
  simp only [CollatzResearch.WordTrace]
  refine ⟨126158635548782400759075607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168211514065043201012100809 126158635548782400759075607)
  ·
    refine ⟨189237953323173601138613411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126158635548782400759075607 189237953323173601138613411)
    ·
      refine ⟨283856929984760401707920117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189237953323173601138613411 283856929984760401707920117)
      ·
        refine ⟨26611587186071287660117511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283856929984760401707920117 26611587186071287660117511)
        ·
          refine ⟨39917380779106931490176267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26611587186071287660117511 39917380779106931490176267)
          ·
            refine ⟨59876071168660397235264401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39917380779106931490176267 59876071168660397235264401)
            ·
              refine ⟨44907053376495297926448301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59876071168660397235264401 44907053376495297926448301)
              ·
                refine ⟨16840145016185736722418113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44907053376495297926448301 16840145016185736722418113)
                ·
                  refine ⟨12630108762139302541813585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16840145016185736722418113 12630108762139302541813585)
                  ·
                    refine ⟨9472581571604476906360189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12630108762139302541813585 9472581571604476906360189)
                    ·
                      refine ⟨3552218089351678839885071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9472581571604476906360189 3552218089351678839885071)
                      ·
                        rfl

theorem cell23_6917920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_6917920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917920 prefixEnd_6917920 := by exact prefixLift 6917920
  have htrace : WordTrace (prefixWord ++ tailWord_6917920) baseStart_6917920 baseEnd_6917920 := by
    simpa [prefixWord, tailWord_6917920, baseEnd_6917920] using wordTrace_append hprefix tailTrace_6917920
  have hstable : (prefixWord ++ tailWord_6917920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917920).length < 2 ^ (prefixWord ++ tailWord_6917920).sum := by decide
  have hdescent : baseEnd_6917920 < baseStart_6917920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917940 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 8]
def baseStart_6917940 : Nat := 118140960795 + 6917940 * 2 ^ 59
def prefixEnd_6917940 : Nat := 4983230072969 + 3 ^ 40 * 6917940 * 2
def baseEnd_6917940 : Nat := 394692039884974306848331

theorem tailTrace_6917940 : CollatzResearch.WordTrace tailWord_6917940 prefixEnd_6917940 394692039884974306848331 := by
  unfold tailWord_6917940
  simp only [CollatzResearch.WordTrace]
  refine ⟨126159000278746172466939637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168212000371661563289252849 126159000278746172466939637)
  ·
    refine ⟨11827406276132453668775591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126159000278746172466939637 11827406276132453668775591)
    ·
      refine ⟨17741109414198680503163387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11827406276132453668775591 17741109414198680503163387)
      ·
        refine ⟨26611664121298020754745081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17741109414198680503163387 26611664121298020754745081)
        ·
          refine ⟨19958748090973515566058811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26611664121298020754745081 19958748090973515566058811)
          ·
            refine ⟨29938122136460273349088217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19958748090973515566058811 29938122136460273349088217)
            ·
              refine ⟨22453591602345205011816163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29938122136460273349088217 22453591602345205011816163)
              ·
                refine ⟨33680387403517807517724245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22453591602345205011816163 33680387403517807517724245)
                ·
                  refine ⟨394692039884974306848331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33680387403517807517724245 394692039884974306848331)
                  ·
                    rfl

theorem cell23_6917940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_6917940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917940 prefixEnd_6917940 := by exact prefixLift 6917940
  have htrace : WordTrace (prefixWord ++ tailWord_6917940) baseStart_6917940 baseEnd_6917940 := by
    simpa [prefixWord, tailWord_6917940, baseEnd_6917940] using wordTrace_append hprefix tailTrace_6917940
  have hstable : (prefixWord ++ tailWord_6917940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917940).length < 2 ^ (prefixWord ++ tailWord_6917940).sum := by decide
  have hdescent : baseEnd_6917940 < baseStart_6917940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917944 : List Nat := [2, 1, 2, 1, 3, 4, 3, 2, 1, 4]
def baseStart_6917944 : Nat := 118140960795 + 6917944 * 2 ^ 59
def prefixEnd_6917944 : Nat := 4983230072969 + 3 ^ 40 * 6917944 * 2
def baseEnd_6917944 : Nat := 1184076804295795581994987

theorem tailTrace_6917944 : CollatzResearch.WordTrace tailWord_6917944 prefixEnd_6917944 1184076804295795581994987 := by
  unfold tailWord_6917944
  simp only [CollatzResearch.WordTrace]
  refine ⟨126159073224738926808512443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168212097632985235744683257 126159073224738926808512443)
  ·
    refine ⟨189238609837108390212768665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126159073224738926808512443 189238609837108390212768665)
    ·
      refine ⟨141928957377831292659576499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189238609837108390212768665 141928957377831292659576499)
      ·
        refine ⟨212893436066746938989364749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141928957377831292659576499 212893436066746938989364749)
        ·
          refine ⟨79835038525030102121011781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212893436066746938989364749 79835038525030102121011781)
          ·
            refine ⟨14969069723443144147689709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79835038525030102121011781 14969069723443144147689709)
            ·
              refine ⟨5613401146291179055383641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14969069723443144147689709 5613401146291179055383641)
              ·
                refine ⟨4210050859718384291537731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5613401146291179055383641 4210050859718384291537731)
                ·
                  refine ⟨6315076289577576437306597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4210050859718384291537731 6315076289577576437306597)
                  ·
                    refine ⟨1184076804295795581994987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6315076289577576437306597 1184076804295795581994987)
                    ·
                      rfl

theorem cell23_6917944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_6917944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917944 prefixEnd_6917944 := by exact prefixLift 6917944
  have htrace : WordTrace (prefixWord ++ tailWord_6917944) baseStart_6917944 baseEnd_6917944 := by
    simpa [prefixWord, tailWord_6917944, baseEnd_6917944] using wordTrace_append hprefix tailTrace_6917944
  have hstable : (prefixWord ++ tailWord_6917944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917944).length < 2 ^ (prefixWord ++ tailWord_6917944).sum := by decide
  have hdescent : baseEnd_6917944 < baseStart_6917944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917970 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_6917970 : Nat := 118140960795 + 6917970 * 2 ^ 59
def prefixEnd_6917970 : Nat := 4983230072969 + 3 ^ 40 * 6917970 * 2
def baseEnd_6917970 : Nat := 1184081254461467881419947

theorem tailTrace_6917970 : CollatzResearch.WordTrace tailWord_6917970 prefixEnd_6917970 1184081254461467881419947 := by
  unfold tailWord_6917970
  simp only [CollatzResearch.WordTrace]
  refine ⟨63079773686845915014367841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168212729831589106704980909 63079773686845915014367841)
  ·
    refine ⟨47309830265134436260775881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63079773686845915014367841 47309830265134436260775881)
    ·
      refine ⟨35482372698850827195581911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47309830265134436260775881 35482372698850827195581911)
      ·
        refine ⟨53223559048276240793372867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35482372698850827195581911 53223559048276240793372867)
        ·
          refine ⟨79835338572414361190059301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53223559048276240793372867 79835338572414361190059301)
          ·
            refine ⟨14969125982327692723136119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79835338572414361190059301 14969125982327692723136119)
            ·
              refine ⟨22453688973491539084704179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14969125982327692723136119 22453688973491539084704179)
              ·
                refine ⟨33680533460237308627056269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22453688973491539084704179 33680533460237308627056269)
                ·
                  refine ⟨12630200047588990735146101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33680533460237308627056269 12630200047588990735146101)
                  ·
                    refine ⟨1184081254461467881419947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12630200047588990735146101 1184081254461467881419947)
                    ·
                      rfl

theorem cell23_6917970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_6917970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917970 prefixEnd_6917970 := by exact prefixLift 6917970
  have htrace : WordTrace (prefixWord ++ tailWord_6917970) baseStart_6917970 baseEnd_6917970 := by
    simpa [prefixWord, tailWord_6917970, baseEnd_6917970] using wordTrace_append hprefix tailTrace_6917970
  have hstable : (prefixWord ++ tailWord_6917970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917970).length < 2 ^ (prefixWord ++ tailWord_6917970).sum := by decide
  have hdescent : baseEnd_6917970 < baseStart_6917970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917977 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 2, 3, 2]
def baseStart_6917977 : Nat := 118140960795 + 6917977 * 2 ^ 59
def prefixEnd_6917977 : Nat := 4983230072969 + 3 ^ 40 * 6917977 * 2
def baseEnd_6917977 : Nat := 3552247357748985116872309

theorem tailTrace_6917977 : CollatzResearch.WordTrace tailWord_6917977 prefixEnd_6917977 3552247357748985116872309 := by
  unfold tailWord_6917977
  simp only [CollatzResearch.WordTrace]
  refine ⟨252319350058358300252976185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168212900038905533501984123 252319350058358300252976185)
  ·
    refine ⟨189239512543768725189732139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252319350058358300252976185 189239512543768725189732139)
    ·
      refine ⟨283859268815653087784598209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189239512543768725189732139 283859268815653087784598209)
      ·
        refine ⟨212894451611739815838448657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283859268815653087784598209 212894451611739815838448657)
        ·
          refine ⟨159670838708804861878836493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212894451611739815838448657 159670838708804861878836493)
          ·
            refine ⟨59876564515801823204563685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159670838708804861878836493 59876564515801823204563685)
            ·
              refine ⟨11226855846712841850855691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59876564515801823204563685 11226855846712841850855691)
              ·
                refine ⟨16840283770069262776283537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11226855846712841850855691 16840283770069262776283537)
                ·
                  refine ⟨12630212827551947082212653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16840283770069262776283537 12630212827551947082212653)
                  ·
                    refine ⟨4736329810331980155829745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12630212827551947082212653 4736329810331980155829745)
                    ·
                      refine ⟨3552247357748985116872309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4736329810331980155829745 3552247357748985116872309)
                      ·
                        rfl

theorem cell23_6917977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 3, 2].length) (baseStart_6917977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917977 prefixEnd_6917977 := by exact prefixLift 6917977
  have htrace : WordTrace (prefixWord ++ tailWord_6917977) baseStart_6917977 baseEnd_6917977 := by
    simpa [prefixWord, tailWord_6917977, baseEnd_6917977] using wordTrace_append hprefix tailTrace_6917977
  have hstable : (prefixWord ++ tailWord_6917977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917977).length < 2 ^ (prefixWord ++ tailWord_6917977).sum := by decide
  have hdescent : baseEnd_6917977 < baseStart_6917977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917983 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 3, 6]
def baseStart_6917983 : Nat := 118140960795 + 6917983 * 2 ^ 59
def prefixEnd_6917983 : Nat := 4983230072969 + 3 ^ 40 * 6917983 * 2
def baseEnd_6917983 : Nat := 1184083479544304031132427

theorem tailTrace_6917983 : CollatzResearch.WordTrace tailWord_6917983 prefixEnd_6917983 1184083479544304031132427 := by
  unfold tailWord_6917983
  simp only [CollatzResearch.WordTrace]
  refine ⟨252319568896336563277694603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168213045930891042185129735 252319568896336563277694603)
  ·
    refine ⟨378479353344504844916541905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252319568896336563277694603 378479353344504844916541905)
    ·
      refine ⟨283859515008378633687406429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378479353344504844916541905 283859515008378633687406429)
      ·
        refine ⟨106447318128141987632777411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283859515008378633687406429 106447318128141987632777411)
        ·
          refine ⟨159670977192212981449166117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106447318128141987632777411 159670977192212981449166117)
          ·
            refine ⟨29938308223539934021718647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159670977192212981449166117 29938308223539934021718647)
            ·
              refine ⟨44907462335309901032577971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29938308223539934021718647 44907462335309901032577971)
              ·
                refine ⟨67361193502964851548866957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44907462335309901032577971 67361193502964851548866957)
                ·
                  refine ⟨25260447563611819330825109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67361193502964851548866957 25260447563611819330825109)
                  ·
                    refine ⟨1184083479544304031132427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25260447563611819330825109 1184083479544304031132427)
                    ·
                      rfl

theorem cell23_6917983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_6917983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917983 prefixEnd_6917983 := by exact prefixLift 6917983
  have htrace : WordTrace (prefixWord ++ tailWord_6917983) baseStart_6917983 baseEnd_6917983 := by
    simpa [prefixWord, tailWord_6917983, baseEnd_6917983] using wordTrace_append hprefix tailTrace_6917983
  have hstable : (prefixWord ++ tailWord_6917983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917983).length < 2 ^ (prefixWord ++ tailWord_6917983).sum := by decide
  have hdescent : baseEnd_6917983 < baseStart_6917983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918003 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 4]
def baseStart_6918003 : Nat := 118140960795 + 6918003 * 2 ^ 59
def prefixEnd_6918003 : Nat := 4983230072969 + 3 ^ 40 * 6918003 * 2
def baseEnd_6918003 : Nat := 3552260708246002015147189

theorem tailTrace_6918003 : CollatzResearch.WordTrace tailWord_6918003 prefixEnd_6918003 3552260708246002015147189 := by
  unfold tailWord_6918003
  simp only [CollatzResearch.WordTrace]
  refine ⟨252320298356264106693422663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168213532237509404462281775 252320298356264106693422663)
  ·
    refine ⟨378480447534396160040133995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252320298356264106693422663 378480447534396160040133995)
    ·
      refine ⟨567720671301594240060200993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378480447534396160040133995 567720671301594240060200993)
      ·
        refine ⟨425790503476195680045150745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567720671301594240060200993 425790503476195680045150745)
        ·
          refine ⟨319342877607146760033863059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425790503476195680045150745 319342877607146760033863059)
          ·
            refine ⟨479014316410720140050794589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319342877607146760033863059 479014316410720140050794589)
            ·
              refine ⟨179630368654020052519047971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 479014316410720140050794589 179630368654020052519047971)
              ·
                refine ⟨269445552981030078778571957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179630368654020052519047971 269445552981030078778571957)
                ·
                  refine ⟨25260520591971569885491121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269445552981030078778571957 25260520591971569885491121)
                  ·
                    refine ⟨18945390443978677414118341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25260520591971569885491121 18945390443978677414118341)
                    ·
                      refine ⟨3552260708246002015147189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18945390443978677414118341 3552260708246002015147189)
                      ·
                        rfl

theorem cell23_6918003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_6918003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918003 prefixEnd_6918003 := by exact prefixLift 6918003
  have htrace : WordTrace (prefixWord ++ tailWord_6918003) baseStart_6918003 baseEnd_6918003 := by
    simpa [prefixWord, tailWord_6918003, baseEnd_6918003] using wordTrace_append hprefix tailTrace_6918003
  have hstable : (prefixWord ++ tailWord_6918003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918003).length < 2 ^ (prefixWord ++ tailWord_6918003).sum := by decide
  have hdescent : baseEnd_6918003 < baseStart_6918003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918010 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3]
def baseStart_6918010 : Nat := 118140960795 + 6918010 * 2 ^ 59
def prefixEnd_6918010 : Nat := 4983230072969 + 3 ^ 40 * 6918010 * 2
def baseEnd_6918010 : Nat := 3552264302610583487759657

theorem tailTrace_6918010 : CollatzResearch.WordTrace tailWord_6918010 prefixEnd_6918010 3552264302610583487759657 := by
  unfold tailWord_6918010
  simp only [CollatzResearch.WordTrace]
  refine ⟨63080138416809686722231871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168213702444825831259284989 63080138416809686722231871)
  ·
    refine ⟨94620207625214530083347807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63080138416809686722231871 94620207625214530083347807)
    ·
      refine ⟨141930311437821795125021711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94620207625214530083347807 141930311437821795125021711)
      ·
        refine ⟨212895467156732692687532567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141930311437821795125021711 212895467156732692687532567)
        ·
          refine ⟨319343200735099039031298851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212895467156732692687532567 319343200735099039031298851)
          ·
            refine ⟨479014801102648558546948277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319343200735099039031298851 479014801102648558546948277)
            ·
              refine ⟨44907637603373302363776401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 479014801102648558546948277 44907637603373302363776401)
              ·
                refine ⟨33680728202529976772832301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44907637603373302363776401 33680728202529976772832301)
                ·
                  refine ⟨12630273075948741289812113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33680728202529976772832301 12630273075948741289812113)
                  ·
                    refine ⟨9472704806961555967359085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12630273075948741289812113 9472704806961555967359085)
                    ·
                      refine ⟨3552264302610583487759657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9472704806961555967359085 3552264302610583487759657)
                      ·
                        rfl

theorem cell23_6918010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_6918010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918010 prefixEnd_6918010 := by exact prefixLift 6918010
  have htrace : WordTrace (prefixWord ++ tailWord_6918010) baseStart_6918010 baseEnd_6918010 := by
    simpa [prefixWord, tailWord_6918010, baseEnd_6918010] using wordTrace_append hprefix tailTrace_6918010
  have hstable : (prefixWord ++ tailWord_6918010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918010).length < 2 ^ (prefixWord ++ tailWord_6918010).sum := by decide
  have hdescent : baseEnd_6918010 < baseStart_6918010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918020 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_6918020 : Nat := 118140960795 + 6918020 * 2 ^ 59
def prefixEnd_6918020 : Nat := 4983230072969 + 3 ^ 40 * 6918020 * 2
def baseEnd_6918020 : Nat := 3552269437417128448634611

theorem tailTrace_6918020 : CollatzResearch.WordTrace tailWord_6918020 prefixEnd_6918020 3552269437417128448634611 := by
  unfold tailWord_6918020
  simp only [CollatzResearch.WordTrace]
  refine ⟨126160459198601259298395757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168213945598135012397861009 126160459198601259298395757)
  ·
    refine ⟨47310172199475472236898409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126160459198601259298395757 47310172199475472236898409)
    ·
      refine ⟨35482629149606604177673807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47310172199475472236898409 35482629149606604177673807)
      ·
        refine ⟨53223943724409906266510711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35482629149606604177673807 53223943724409906266510711)
        ·
          refine ⟨79835915586614859399766067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53223943724409906266510711 79835915586614859399766067)
          ·
            refine ⟨119753873379922289099649101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79835915586614859399766067 119753873379922289099649101)
            ·
              refine ⟨44907702517470858412368413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119753873379922289099649101 44907702517470858412368413)
              ·
                refine ⟨16840388444051571904638155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44907702517470858412368413 16840388444051571904638155)
                ·
                  refine ⟨25260582666077357856957233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16840388444051571904638155 25260582666077357856957233)
                  ·
                    refine ⟨18945436999558018392717925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25260582666077357856957233 18945436999558018392717925)
                    ·
                      refine ⟨3552269437417128448634611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18945436999558018392717925 3552269437417128448634611)
                      ·
                        rfl

theorem cell23_6918020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_6918020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918020 prefixEnd_6918020 := by exact prefixLift 6918020
  have htrace : WordTrace (prefixWord ++ tailWord_6918020) baseStart_6918020 baseEnd_6918020 := by
    simpa [prefixWord, tailWord_6918020, baseEnd_6918020] using wordTrace_append hprefix tailTrace_6918020
  have hstable : (prefixWord ++ tailWord_6918020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918020).length < 2 ^ (prefixWord ++ tailWord_6918020).sum := by decide
  have hdescent : baseEnd_6918020 < baseStart_6918020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918044 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6918044 : Nat := 118140960795 + 6918044 * 2 ^ 59
def prefixEnd_6918044 : Nat := 4983230072969 + 3 ^ 40 * 6918044 * 2
def baseEnd_6918044 : Nat := 3552281760952836354734501

theorem tailTrace_6918044 : CollatzResearch.WordTrace tailWord_6918044 prefixEnd_6918044 3552281760952836354734501 := by
  unfold tailWord_6918044
  simp only [CollatzResearch.WordTrace]
  refine ⟨126160896874557785347832593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168214529166077047130443457 126160896874557785347832593)
  ·
    refine ⟨94620672655918339010874445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126160896874557785347832593 94620672655918339010874445)
    ·
      refine ⟨35482752245969377129077917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94620672655918339010874445 35482752245969377129077917)
      ·
        refine ⟨13306032092238516423404219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35482752245969377129077917 13306032092238516423404219)
        ·
          refine ⟨19959048138357774635106329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13306032092238516423404219 19959048138357774635106329)
          ·
            refine ⟨14969286103768330976329747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19959048138357774635106329 14969286103768330976329747)
            ·
              refine ⟨22453929155652496464494621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14969286103768330976329747 22453929155652496464494621)
              ·
                refine ⟨8420223433369686174185483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22453929155652496464494621 8420223433369686174185483)
                ·
                  refine ⟨12630335150054529261278225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8420223433369686174185483 12630335150054529261278225)
                  ·
                    refine ⟨9472751362540896945958669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12630335150054529261278225 9472751362540896945958669)
                    ·
                      refine ⟨3552281760952836354734501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9472751362540896945958669 3552281760952836354734501)
                      ·
                        rfl

theorem cell23_6918044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6918044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918044 prefixEnd_6918044 := by exact prefixLift 6918044
  have htrace : WordTrace (prefixWord ++ tailWord_6918044) baseStart_6918044 baseEnd_6918044 := by
    simpa [prefixWord, tailWord_6918044, baseEnd_6918044] using wordTrace_append hprefix tailTrace_6918044
  have hstable : (prefixWord ++ tailWord_6918044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918044).length < 2 ^ (prefixWord ++ tailWord_6918044).sum := by decide
  have hdescent : baseEnd_6918044 < baseStart_6918044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918057 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 2, 1, 3]
def baseStart_6918057 : Nat := 118140960795 + 6918057 * 2 ^ 59
def prefixEnd_6918057 : Nat := 4983230072969 + 3 ^ 40 * 6918057 * 2
def baseEnd_6918057 : Nat := 3552288436201344803871941

theorem tailTrace_6918057 : CollatzResearch.WordTrace tailWord_6918057 prefixEnd_6918057 3552288436201344803871941 := by
  unfold tailWord_6918057
  simp only [CollatzResearch.WordTrace]
  refine ⟨252322267898068473915888425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168214845265378982610592283 252322267898068473915888425)
  ·
    refine ⟨189241700923551355436916319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252322267898068473915888425 189241700923551355436916319)
    ·
      refine ⟨283862551385327033155374479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189241700923551355436916319 283862551385327033155374479)
      ·
        refine ⟨425793827077990549733061719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283862551385327033155374479 425793827077990549733061719)
        ·
          refine ⟨638690740616985824599592579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425793827077990549733061719 638690740616985824599592579)
          ·
            refine ⟨958036110925478736899388869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638690740616985824599592579 958036110925478736899388869)
            ·
              refine ⟨179631770798527263168635413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 958036110925478736899388869 179631770798527263168635413)
              ·
                refine ⟨8420239256180965461029785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179631770798527263168635413 8420239256180965461029785)
                ·
                  refine ⟨6315179442135724095772339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8420239256180965461029785 6315179442135724095772339)
                  ·
                    refine ⟨9472769163203586143658509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6315179442135724095772339 9472769163203586143658509)
                    ·
                      refine ⟨3552288436201344803871941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9472769163203586143658509 3552288436201344803871941)
                      ·
                        rfl

theorem cell23_6918057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 1, 3].length) (baseStart_6918057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918057 prefixEnd_6918057 := by exact prefixLift 6918057
  have htrace : WordTrace (prefixWord ++ tailWord_6918057) baseStart_6918057 baseEnd_6918057 := by
    simpa [prefixWord, tailWord_6918057, baseEnd_6918057] using wordTrace_append hprefix tailTrace_6918057
  have hstable : (prefixWord ++ tailWord_6918057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918057).length < 2 ^ (prefixWord ++ tailWord_6918057).sum := by decide
  have hdescent : baseEnd_6918057 < baseStart_6918057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918068 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_6918068 : Nat := 118140960795 + 6918068 * 2 ^ 59
def prefixEnd_6918068 : Nat := 4983230072969 + 3 ^ 40 * 6918068 * 2
def baseEnd_6918068 : Nat := 1184098028162848086944797

theorem tailTrace_6918068 : CollatzResearch.WordTrace tailWord_6918068 prefixEnd_6918068 1184098028162848086944797 := by
  unfold tailWord_6918068
  simp only [CollatzResearch.WordTrace]
  refine ⟨126161334550514311397269429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168215112734019081863025905 126161334550514311397269429)
  ·
    refine ⟨11827625114110716693494009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126161334550514311397269429 11827625114110716693494009)
    ·
      refine ⟨8870718835583037520120507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11827625114110716693494009 8870718835583037520120507)
      ·
        refine ⟨13306078253374556280180761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8870718835583037520120507 13306078253374556280180761)
        ·
          refine ⟨9979558690030917210135571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13306078253374556280180761 9979558690030917210135571)
          ·
            refine ⟨14969338035046375815203357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9979558690030917210135571 14969338035046375815203357)
            ·
              refine ⟨5613501763142390930701259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14969338035046375815203357 5613501763142390930701259)
              ·
                refine ⟨8420252644713586396051889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5613501763142390930701259 8420252644713586396051889)
                ·
                  refine ⟨6315189483535189797038917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8420252644713586396051889 6315189483535189797038917)
                  ·
                    refine ⟨1184098028162848086944797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6315189483535189797038917 1184098028162848086944797)
                    ·
                      rfl

theorem cell23_6918068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_6918068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918068 prefixEnd_6918068 := by exact prefixLift 6918068
  have htrace : WordTrace (prefixWord ++ tailWord_6918068) baseStart_6918068 baseEnd_6918068 := by
    simpa [prefixWord, tailWord_6918068, baseEnd_6918068] using wordTrace_append hprefix tailTrace_6918068
  have hstable : (prefixWord ++ tailWord_6918068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918068).length < 2 ^ (prefixWord ++ tailWord_6918068).sum := by decide
  have hdescent : baseEnd_6918068 < baseStart_6918068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918125 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6918125 : Nat := 118140960795 + 6918125 * 2 ^ 59
def prefixEnd_6918125 : Nat := 4983230072969 + 3 ^ 40 * 6918125 * 2
def baseEnd_6918125 : Nat := 3552323352885850537821629

theorem tailTrace_6918125 : CollatzResearch.WordTrace tailWord_6918125 prefixEnd_6918125 3552323352885850537821629 := by
  unfold tailWord_6918125
  simp only [CollatzResearch.WordTrace]
  refine ⟨252324748061822121529363829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168216498707881414352909219 252324748061822121529363829)
  ·
    refine ⟨23655445130795823893377859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252324748061822121529363829 23655445130795823893377859)
    ·
      refine ⟨35483167696193735840066789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23655445130795823893377859 35483167696193735840066789)
      ·
        refine ⟨6653093943036325470012523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35483167696193735840066789 6653093943036325470012523)
        ·
          refine ⟨9979640914554488205018785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6653093943036325470012523 9979640914554488205018785)
          ·
            refine ⟨7484730685915866153764089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9979640914554488205018785 7484730685915866153764089)
            ·
              refine ⟨5613548014436899615323067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7484730685915866153764089 5613548014436899615323067)
              ·
                refine ⟨8420322021655349422984601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5613548014436899615323067 8420322021655349422984601)
                ·
                  refine ⟨6315241516241512067238451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8420322021655349422984601 6315241516241512067238451)
                  ·
                    refine ⟨9472862274362268100857677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6315241516241512067238451 9472862274362268100857677)
                    ·
                      refine ⟨3552323352885850537821629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9472862274362268100857677 3552323352885850537821629)
                      ·
                        rfl

theorem cell23_6918125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6918125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918125 prefixEnd_6918125 := by exact prefixLift 6918125
  have htrace : WordTrace (prefixWord ++ tailWord_6918125) baseStart_6918125 baseEnd_6918125 := by
    simpa [prefixWord, tailWord_6918125, baseEnd_6918125] using wordTrace_append hprefix tailTrace_6918125
  have hstable : (prefixWord ++ tailWord_6918125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918125).length < 2 ^ (prefixWord ++ tailWord_6918125).sum := by decide
  have hdescent : baseEnd_6918125 < baseStart_6918125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918197 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 5, 4]
def baseStart_6918197 : Nat := 118140960795 + 6918197 * 2 ^ 59
def prefixEnd_6918197 : Nat := 4983230072969 + 3 ^ 40 * 6918197 * 2
def baseEnd_6918197 : Nat := 1184120107830991418707099

theorem tailTrace_6918197 : CollatzResearch.WordTrace tailWord_6918197 prefixEnd_6918197 1184120107830991418707099 := by
  unfold tailWord_6918197
  simp only [CollatzResearch.WordTrace]
  refine ⟨252327374117561277825984845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168218249411707518550656563 252327374117561277825984845)
  ·
    refine ⟨94622765294085479184744317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252327374117561277825984845 94622765294085479184744317)
    ·
      refine ⟨35483536985282054694279119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94622765294085479184744317 35483536985282054694279119)
      ·
        refine ⟨53225305477923082041418679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35483536985282054694279119 53225305477923082041418679)
        ·
          refine ⟨79837958216884623062128019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53225305477923082041418679 79837958216884623062128019)
          ·
            refine ⟨119756937325326934593192029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79837958216884623062128019 119756937325326934593192029)
            ·
              refine ⟨44908851496997600472447011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119756937325326934593192029 44908851496997600472447011)
              ·
                refine ⟨67363277245496400708670517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44908851496997600472447011 67363277245496400708670517)
                ·
                  refine ⟨6315307241765287566437861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67363277245496400708670517 6315307241765287566437861)
                  ·
                    refine ⟨1184120107830991418707099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6315307241765287566437861 1184120107830991418707099)
                    ·
                      rfl

theorem cell23_6918197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_6918197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918197 prefixEnd_6918197 := by exact prefixLift 6918197
  have htrace : WordTrace (prefixWord ++ tailWord_6918197) baseStart_6918197 baseEnd_6918197 := by
    simpa [prefixWord, tailWord_6918197, baseEnd_6918197] using wordTrace_append hprefix tailTrace_6918197
  have hstable : (prefixWord ++ tailWord_6918197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918197).length < 2 ^ (prefixWord ++ tailWord_6918197).sum := by decide
  have hdescent : baseEnd_6918197 < baseStart_6918197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918201 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 2, 5]
def baseStart_6918201 : Nat := 118140960795 + 6918201 * 2 ^ 59
def prefixEnd_6918201 : Nat := 4983230072969 + 3 ^ 40 * 6918201 * 2
def baseEnd_6918201 : Nat := 1184120792471864080157093

theorem tailTrace_6918201 : CollatzResearch.WordTrace tailWord_6918201 prefixEnd_6918201 1184120792471864080157093 := by
  unfold tailWord_6918201
  simp only [CollatzResearch.WordTrace]
  refine ⟨252327520009546786509130457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168218346673031191006086971 252327520009546786509130457)
  ·
    refine ⟨189245640007160089881847843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252327520009546786509130457 189245640007160089881847843)
    ·
      refine ⟨283868460010740134822771765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189245640007160089881847843 283868460010740134822771765)
      ·
        refine ⟨26612668126006887639634853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283868460010740134822771765 26612668126006887639634853)
        ·
          refine ⟨4989875273626291432431535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26612668126006887639634853 4989875273626291432431535)
          ·
            refine ⟨7484812910439437148647303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989875273626291432431535 7484812910439437148647303)
            ·
              refine ⟨11227219365659155722970955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7484812910439437148647303 11227219365659155722970955)
              ·
                refine ⟨16840829048488733584456433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11227219365659155722970955 16840829048488733584456433)
                ·
                  refine ⟨12630621786366550188342325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16840829048488733584456433 12630621786366550188342325)
                  ·
                    refine ⟨1184120792471864080157093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12630621786366550188342325 1184120792471864080157093)
                    ·
                      rfl

theorem cell23_6918201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 5].length) (baseStart_6918201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918201 prefixEnd_6918201 := by exact prefixLift 6918201
  have htrace : WordTrace (prefixWord ++ tailWord_6918201) baseStart_6918201 baseEnd_6918201 := by
    simpa [prefixWord, tailWord_6918201, baseEnd_6918201] using wordTrace_append hprefix tailTrace_6918201
  have hstable : (prefixWord ++ tailWord_6918201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918201).length < 2 ^ (prefixWord ++ tailWord_6918201).sum := by decide
  have hdescent : baseEnd_6918201 < baseStart_6918201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918264 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 2, 3, 2]
def baseStart_6918264 : Nat := 118140960795 + 6918264 * 2 ^ 59
def prefixEnd_6918264 : Nat := 4983230072969 + 3 ^ 40 * 6918264 * 2
def baseEnd_6918264 : Nat := 3552394726696825493983489

theorem tailTrace_6918264 : CollatzResearch.WordTrace tailWord_6918264 prefixEnd_6918264 3552394726696825493983489 := by
  unfold tailWord_6918264
  simp only [CollatzResearch.WordTrace]
  refine ⟨126164908904159274134336923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168219878538879032179115897 126164908904159274134336923)
  ·
    refine ⟨189247363356238911201505385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126164908904159274134336923 189247363356238911201505385)
    ·
      refine ⟨141935522517179183401129039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189247363356238911201505385 141935522517179183401129039)
      ·
        refine ⟨212903283775768775101693559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141935522517179183401129039 212903283775768775101693559)
        ·
          refine ⟨319354925663653162652540339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212903283775768775101693559 319354925663653162652540339)
          ·
            refine ⟨479032388495479743978810509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319354925663653162652540339 479032388495479743978810509)
            ·
              refine ⟨179637145685804903992053941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 479032388495479743978810509 179637145685804903992053941)
              ·
                refine ⟨16840982408044209749255057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179637145685804903992053941 16840982408044209749255057)
                ·
                  refine ⟨12630736806033157311941293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16840982408044209749255057 12630736806033157311941293)
                  ·
                    refine ⟨4736526302262433991977985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12630736806033157311941293 4736526302262433991977985)
                    ·
                      refine ⟨3552394726696825493983489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4736526302262433991977985 3552394726696825493983489)
                      ·
                        rfl

theorem cell23_6918264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 3, 2].length) (baseStart_6918264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918264 prefixEnd_6918264 := by exact prefixLift 6918264
  have htrace : WordTrace (prefixWord ++ tailWord_6918264) baseStart_6918264 baseEnd_6918264 := by
    simpa [prefixWord, tailWord_6918264, baseEnd_6918264] using wordTrace_append hprefix tailTrace_6918264
  have hstable : (prefixWord ++ tailWord_6918264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918264).length < 2 ^ (prefixWord ++ tailWord_6918264).sum := by decide
  have hdescent : baseEnd_6918264 < baseStart_6918264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918288 : List Nat := [2, 1, 1, 1, 1, 1, 9, 2, 1, 1, 3]
def baseStart_6918288 : Nat := 118140960795 + 6918288 * 2 ^ 59
def prefixEnd_6918288 : Nat := 4983230072969 + 3 ^ 40 * 6918288 * 2
def baseEnd_6918288 : Nat := 3552407050232533400083379

theorem tailTrace_6918288 : CollatzResearch.WordTrace tailWord_6918288 prefixEnd_6918288 3552407050232533400083379 := by
  unfold tailWord_6918288
  simp only [CollatzResearch.WordTrace]
  refine ⟨126165346580115800183773759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168220462106821066911698345 126165346580115800183773759)
  ·
    refine ⟨189248019870173700275660639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126165346580115800183773759 189248019870173700275660639)
    ·
      refine ⟨283872029805260550413490959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189248019870173700275660639 283872029805260550413490959)
      ·
        refine ⟨425808044707890825620236439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283872029805260550413490959 425808044707890825620236439)
        ·
          refine ⟨638712067061836238430354659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425808044707890825620236439 638712067061836238430354659)
          ·
            refine ⟨958068100592754357645531989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638712067061836238430354659 958068100592754357645531989)
            ·
              refine ⟨5613680276910670064329289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 958068100592754357645531989 5613680276910670064329289)
              ·
                refine ⟨4210260207683002548246967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5613680276910670064329289 4210260207683002548246967)
                ·
                  refine ⟨6315390311524503822370451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4210260207683002548246967 6315390311524503822370451)
                  ·
                    refine ⟨9473085467286755733555677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6315390311524503822370451 9473085467286755733555677)
                    ·
                      refine ⟨3552407050232533400083379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9473085467286755733555677 3552407050232533400083379)
                      ·
                        rfl

theorem cell23_6918288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 1, 1, 3].length) (baseStart_6918288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918288 prefixEnd_6918288 := by exact prefixLift 6918288
  have htrace : WordTrace (prefixWord ++ tailWord_6918288) baseStart_6918288 baseEnd_6918288 := by
    simpa [prefixWord, tailWord_6918288, baseEnd_6918288] using wordTrace_append hprefix tailTrace_6918288
  have hstable : (prefixWord ++ tailWord_6918288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918288).length < 2 ^ (prefixWord ++ tailWord_6918288).sum := by decide
  have hdescent : baseEnd_6918288 < baseStart_6918288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918308 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_6918308 : Nat := 118140960795 + 6918308 * 2 ^ 59
def prefixEnd_6918308 : Nat := 4983230072969 + 3 ^ 40 * 6918308 * 2
def baseEnd_6918308 : Nat := 1184139106615207773944429

theorem tailTrace_6918308 : CollatzResearch.WordTrace tailWord_6918308 prefixEnd_6918308 1184139106615207773944429 := by
  unfold tailWord_6918308
  simp only [CollatzResearch.WordTrace]
  refine ⟨126165711310079571891637789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168220948413439429188850385 126165711310079571891637789)
  ·
    refine ⟨47312141741279839459364171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126165711310079571891637789 47312141741279839459364171)
    ·
      refine ⟨70968212611919759189046257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47312141741279839459364171 70968212611919759189046257)
      ·
        refine ⟨53226159458939819391784693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70968212611919759189046257 53226159458939819391784693)
        ·
          refine ⟨4989952449275608067979815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53226159458939819391784693 4989952449275608067979815)
          ·
            refine ⟨7484928673913412101969723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989952449275608067979815 7484928673913412101969723)
            ·
              refine ⟨11227393010870118152954585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7484928673913412101969723 11227393010870118152954585)
              ·
                refine ⟨8420544758152588614715939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11227393010870118152954585 8420544758152588614715939)
                ·
                  refine ⟨12630817137228882922073909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8420544758152588614715939 12630817137228882922073909)
                  ·
                    refine ⟨1184139106615207773944429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12630817137228882922073909 1184139106615207773944429)
                    ·
                      rfl

theorem cell23_6918308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_6918308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918308 prefixEnd_6918308 := by exact prefixLift 6918308
  have htrace : WordTrace (prefixWord ++ tailWord_6918308) baseStart_6918308 baseEnd_6918308 := by
    simpa [prefixWord, tailWord_6918308, baseEnd_6918308] using wordTrace_append hprefix tailTrace_6918308
  have hstable : (prefixWord ++ tailWord_6918308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918308).length < 2 ^ (prefixWord ++ tailWord_6918308).sum := by decide
  have hdescent : baseEnd_6918308 < baseStart_6918308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918311 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_6918311 : Nat := 118140960795 + 6918311 * 2 ^ 59
def prefixEnd_6918311 : Nat := 4983230072969 + 3 ^ 40 * 6918311 * 2
def baseEnd_6918311 : Nat := 3552418860287586810095773

theorem tailTrace_6918311 : CollatzResearch.WordTrace tailWord_6918311 prefixEnd_6918311 3552418860287586810095773 := by
  unfold tailWord_6918311
  simp only [CollatzResearch.WordTrace]
  refine ⟨252331532039148275295634787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168221021359432183530423191 252331532039148275295634787)
  ·
    refine ⟨378497298058722412943452181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252331532039148275295634787 378497298058722412943452181)
    ·
      refine ⟨17742060846502613106724321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 378497298058722412943452181 17742060846502613106724321)
      ·
        refine ⟨13306545634876959830043241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17742060846502613106724321 13306545634876959830043241)
        ·
          refine ⟨9979909226157719872532431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13306545634876959830043241 9979909226157719872532431)
          ·
            refine ⟨14969863839236579808798647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9979909226157719872532431 14969863839236579808798647)
            ·
              refine ⟨22454795758854869713197971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14969863839236579808798647 22454795758854869713197971)
              ·
                refine ⟨33682193638282304569796957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22454795758854869713197971 33682193638282304569796957)
                ·
                  refine ⟨12630822614355864213673859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33682193638282304569796957 12630822614355864213673859)
                  ·
                    refine ⟨18946233921533796320510789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12630822614355864213673859 18946233921533796320510789)
                    ·
                      refine ⟨3552418860287586810095773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18946233921533796320510789 3552418860287586810095773)
                      ·
                        rfl

theorem cell23_6918311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_6918311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918311 prefixEnd_6918311 := by exact prefixLift 6918311
  have htrace : WordTrace (prefixWord ++ tailWord_6918311) baseStart_6918311 baseEnd_6918311 := by
    simpa [prefixWord, tailWord_6918311, baseEnd_6918311] using wordTrace_append hprefix tailTrace_6918311
  have hstable : (prefixWord ++ tailWord_6918311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918311).length < 2 ^ (prefixWord ++ tailWord_6918311).sum := by decide
  have hdescent : baseEnd_6918311 < baseStart_6918311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918328 : List Nat := [2, 1, 2, 1, 2, 1, 4, 5, 1, 2, 2]
def baseStart_6918328 : Nat := 118140960795 + 6918328 * 2 ^ 59
def prefixEnd_6918328 : Nat := 4983230072969 + 3 ^ 40 * 6918328 * 2
def baseEnd_6918328 : Nat := 3552427589458713243583195

theorem tailTrace_6918328 : CollatzResearch.WordTrace tailWord_6918328 prefixEnd_6918328 3552427589458713243583195 := by
  unfold tailWord_6918328
  simp only [CollatzResearch.WordTrace]
  refine ⟨126166076040043343599501819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168221434720057791466002425 126166076040043343599501819)
  ·
    refine ⟨189249114060065015399252729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126166076040043343599501819 189249114060065015399252729)
    ·
      refine ⟨141936835545048761549439547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189249114060065015399252729 141936835545048761549439547)
      ·
        refine ⟨212905253317573142324159321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141936835545048761549439547 212905253317573142324159321)
        ·
          refine ⟨159678939988179856743119491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212905253317573142324159321 159678939988179856743119491)
          ·
            refine ⟨239518409982269785114679237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159678939988179856743119491 239518409982269785114679237)
            ·
              refine ⟨44909701871675584709002357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239518409982269785114679237 44909701871675584709002357)
              ·
                refine ⟨4210284550469586066468971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44909701871675584709002357 4210284550469586066468971)
                ·
                  refine ⟨6315426825704379099703457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4210284550469586066468971 6315426825704379099703457)
                  ·
                    refine ⟨4736570119278284324777593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6315426825704379099703457 4736570119278284324777593)
                    ·
                      refine ⟨3552427589458713243583195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4736570119278284324777593 3552427589458713243583195)
                      ·
                        rfl

theorem cell23_6918328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 1, 2, 2].length) (baseStart_6918328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918328 prefixEnd_6918328 := by exact prefixLift 6918328
  have htrace : WordTrace (prefixWord ++ tailWord_6918328) baseStart_6918328 baseEnd_6918328 := by
    simpa [prefixWord, tailWord_6918328, baseEnd_6918328] using wordTrace_append hprefix tailTrace_6918328
  have hstable : (prefixWord ++ tailWord_6918328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918328).length < 2 ^ (prefixWord ++ tailWord_6918328).sum := by decide
  have hdescent : baseEnd_6918328 < baseStart_6918328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918331 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 1, 2, 3]
def baseStart_6918331 : Nat := 118140960795 + 6918331 * 2 ^ 59
def prefixEnd_6918331 : Nat := 4983230072969 + 3 ^ 40 * 6918331 * 2
def baseEnd_6918331 : Nat := 3552429129900676731845681

theorem tailTrace_6918331 : CollatzResearch.WordTrace tailWord_6918331 prefixEnd_6918331 3552429129900676731845681 := by
  unfold tailWord_6918331
  simp only [CollatzResearch.WordTrace]
  refine ⟨252332261499075818711362847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168221507666050545807575231 252332261499075818711362847)
  ·
    refine ⟨378498392248613728067044271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252332261499075818711362847 378498392248613728067044271)
    ·
      refine ⟨567747588372920592100566407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378498392248613728067044271 567747588372920592100566407)
      ·
        refine ⟨851621382559380888150849611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567747588372920592100566407 851621382559380888150849611)
        ·
          refine ⟨1277432073839071332226274417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851621382559380888150849611 1277432073839071332226274417)
          ·
            refine ⟨958074055379303499169705813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1277432073839071332226274417 958074055379303499169705813)
            ·
              refine ⟨5613715168238106440447495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 958074055379303499169705813 5613715168238106440447495)
              ·
                refine ⟨8420572752357159660671243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5613715168238106440447495 8420572752357159660671243)
                ·
                  refine ⟨12630859128535739491006865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8420572752357159660671243 12630859128535739491006865)
                  ·
                    refine ⟨9473144346401804618255149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12630859128535739491006865 9473144346401804618255149)
                    ·
                      refine ⟨3552429129900676731845681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9473144346401804618255149 3552429129900676731845681)
                      ·
                        rfl

theorem cell23_6918331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 2, 3].length) (baseStart_6918331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918331 prefixEnd_6918331 := by exact prefixLift 6918331
  have htrace : WordTrace (prefixWord ++ tailWord_6918331) baseStart_6918331 baseEnd_6918331 := by
    simpa [prefixWord, tailWord_6918331, baseEnd_6918331] using wordTrace_append hprefix tailTrace_6918331
  have hstable : (prefixWord ++ tailWord_6918331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918331).length < 2 ^ (prefixWord ++ tailWord_6918331).sum := by decide
  have hdescent : baseEnd_6918331 < baseStart_6918331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918334 : List Nat := [4, 2, 1, 1, 5, 10]
def baseStart_6918334 : Nat := 118140960795 + 6918334 * 2 ^ 59
def prefixEnd_6918334 : Nat := 4983230072969 + 3 ^ 40 * 6918334 * 2
def baseEnd_6918334 : Nat := 14619056256554074979869

theorem tailTrace_6918334 : CollatzResearch.WordTrace tailWord_6918334 prefixEnd_6918334 14619056256554074979869 := by
  unfold tailWord_6918334
  simp only [CollatzResearch.WordTrace]
  refine ⟨31541546364758118777965257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168221580612043300149148037 31541546364758118777965257)
  ·
    refine ⟨23656159773568589083473943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31541546364758118777965257 23656159773568589083473943)
    ·
      refine ⟨35484239660352883625210915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23656159773568589083473943 35484239660352883625210915)
      ·
        refine ⟨53226359490529325437816373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35484239660352883625210915 53226359490529325437816373)
        ·
          refine ⟨4989971202237124259795285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53226359490529325437816373 4989971202237124259795285)
          ·
            refine ⟨14619056256554074979869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4989971202237124259795285 14619056256554074979869)
            ·
              rfl

theorem cell23_6918334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 10].length) (baseStart_6918334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918334 prefixEnd_6918334 := by exact prefixLift 6918334
  have htrace : WordTrace (prefixWord ++ tailWord_6918334) baseStart_6918334 baseEnd_6918334 := by
    simpa [prefixWord, tailWord_6918334, baseEnd_6918334] using wordTrace_append hprefix tailTrace_6918334
  have hstable : (prefixWord ++ tailWord_6918334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918334).length < 2 ^ (prefixWord ++ tailWord_6918334).sum := by decide
  have hdescent : baseEnd_6918334 < baseStart_6918334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918358 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_6918358 : Nat := 118140960795 + 6918358 * 2 ^ 59
def prefixEnd_6918358 : Nat := 4983230072969 + 3 ^ 40 * 6918358 * 2
def baseEnd_6918358 : Nat := 3552442993878348126208057

theorem tailTrace_6918358 : CollatzResearch.WordTrace tailWord_6918358 prefixEnd_6918358 3552442993878348126208057 := by
  unfold tailWord_6918358
  simp only [CollatzResearch.WordTrace]
  refine ⟨15770827891873625145162233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168222164179985334881730485 15770827891873625145162233)
  ·
    refine ⟨11828120918905218858871675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15770827891873625145162233 11828120918905218858871675)
    ·
      refine ⟨17742181378357828288307513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11828120918905218858871675 17742181378357828288307513)
      ·
        refine ⟨13306636033768371216230635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17742181378357828288307513 13306636033768371216230635)
        ·
          refine ⟨19959954050652556824345953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13306636033768371216230635 19959954050652556824345953)
          ·
            refine ⟨14969965537989417618259465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19959954050652556824345953 14969965537989417618259465)
            ·
              refine ⟨11227474153492063213694599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14969965537989417618259465 11227474153492063213694599)
              ·
                refine ⟨16841211230238094820541899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11227474153492063213694599 16841211230238094820541899)
                ·
                  refine ⟨25261816845357142230812849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16841211230238094820541899 25261816845357142230812849)
                  ·
                    refine ⟨18946362634017856673109637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25261816845357142230812849 18946362634017856673109637)
                    ·
                      refine ⟨3552442993878348126208057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18946362634017856673109637 3552442993878348126208057)
                      ·
                        rfl

theorem cell23_6918358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_6918358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918358 prefixEnd_6918358 := by exact prefixLift 6918358
  have htrace : WordTrace (prefixWord ++ tailWord_6918358) baseStart_6918358 baseEnd_6918358 := by
    simpa [prefixWord, tailWord_6918358, baseEnd_6918358] using wordTrace_append hprefix tailTrace_6918358
  have hstable : (prefixWord ++ tailWord_6918358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918358).length < 2 ^ (prefixWord ++ tailWord_6918358).sum := by decide
  have hdescent : baseEnd_6918358 < baseStart_6918358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918361 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 2, 1, 3]
def baseStart_6918361 : Nat := 118140960795 + 6918361 * 2 ^ 59
def prefixEnd_6918361 : Nat := 4983230072969 + 3 ^ 40 * 6918361 * 2
def baseEnd_6918361 : Nat := 3552444534320311614470543

theorem tailTrace_6918361 : CollatzResearch.WordTrace tailWord_6918361 prefixEnd_6918361 3552444534320311614470543 := by
  unfold tailWord_6918361
  simp only [CollatzResearch.WordTrace]
  refine ⟨252333355688967133834954937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168222237125978089223303291 252333355688967133834954937)
  ·
    refine ⟨189250016766725350376216203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252333355688967133834954937 189250016766725350376216203)
    ·
      refine ⟨283875025150088025564324305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189250016766725350376216203 283875025150088025564324305)
      ·
        refine ⟨212906268862566019173243229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283875025150088025564324305 212906268862566019173243229)
        ·
          refine ⟨79839850823462257189966211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212906268862566019173243229 79839850823462257189966211)
          ·
            refine ⟨119759776235193385784949317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79839850823462257189966211 119759776235193385784949317)
            ·
              refine ⟨22454958044098759834677997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119759776235193385784949317 22454958044098759834677997)
              ·
                refine ⟨8420609266537034938004249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22454958044098759834677997 8420609266537034938004249)
                ·
                  refine ⟨6315456949902776203503187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8420609266537034938004249 6315456949902776203503187)
                  ·
                    refine ⟨9473185424854164305254781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6315456949902776203503187 9473185424854164305254781)
                    ·
                      refine ⟨3552444534320311614470543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9473185424854164305254781 3552444534320311614470543)
                      ·
                        rfl

theorem cell23_6918361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_6918361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918361 prefixEnd_6918361 := by exact prefixLift 6918361
  have htrace : WordTrace (prefixWord ++ tailWord_6918361) baseStart_6918361 baseEnd_6918361 := by
    simpa [prefixWord, tailWord_6918361, baseEnd_6918361] using wordTrace_append hprefix tailTrace_6918361
  have hstable : (prefixWord ++ tailWord_6918361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918361).length < 2 ^ (prefixWord ++ tailWord_6918361).sum := by decide
  have hdescent : baseEnd_6918361 < baseStart_6918361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918367 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 4]
def baseStart_6918367 : Nat := 118140960795 + 6918367 * 2 ^ 59
def prefixEnd_6918367 : Nat := 4983230072969 + 3 ^ 40 * 6918367 * 2
def baseEnd_6918367 : Nat := 3552447615204238590995515

theorem tailTrace_6918367 : CollatzResearch.WordTrace tailWord_6918367 prefixEnd_6918367 3552447615204238590995515 := by
  unfold tailWord_6918367
  simp only [CollatzResearch.WordTrace]
  refine ⟨252333574526945396859673355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168222383017963597906448903 252333574526945396859673355)
  ·
    refine ⟨378500361790418095289510033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252333574526945396859673355 378500361790418095289510033)
    ·
      refine ⟨283875271342813571467132525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378500361790418095289510033 283875271342813571467132525)
      ·
        refine ⟨106453226753555089300174697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283875271342813571467132525 106453226753555089300174697)
        ·
          refine ⟨79839920065166316975131023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106453226753555089300174697 79839920065166316975131023)
          ·
            refine ⟨119759880097749475462696535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79839920065166316975131023 119759880097749475462696535)
            ·
              refine ⟨179639820146624213194044803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119759880097749475462696535 179639820146624213194044803)
              ·
                refine ⟨269459730219936319791067205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179639820146624213194044803 269459730219936319791067205)
                ·
                  refine ⟨50523699416238059960825101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269459730219936319791067205 50523699416238059960825101)
                  ·
                    refine ⟨18946387281089272485309413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50523699416238059960825101 18946387281089272485309413)
                    ·
                      refine ⟨3552447615204238590995515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18946387281089272485309413 3552447615204238590995515)
                      ·
                        rfl

theorem cell23_6918367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_6918367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918367 prefixEnd_6918367 := by exact prefixLift 6918367
  have htrace : WordTrace (prefixWord ++ tailWord_6918367) baseStart_6918367 baseEnd_6918367 := by
    simpa [prefixWord, tailWord_6918367, baseEnd_6918367] using wordTrace_append hprefix tailTrace_6918367
  have hstable : (prefixWord ++ tailWord_6918367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918367).length < 2 ^ (prefixWord ++ tailWord_6918367).sum := by decide
  have hdescent : baseEnd_6918367 < baseStart_6918367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918387 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 5]
def baseStart_6918387 : Nat := 118140960795 + 6918387 * 2 ^ 59
def prefixEnd_6918387 : Nat := 4983230072969 + 3 ^ 40 * 6918387 * 2
def baseEnd_6918387 : Nat := 3552457884817328512745423

theorem tailTrace_6918387 : CollatzResearch.WordTrace tailWord_6918387 prefixEnd_6918387 3552457884817328512745423 := by
  unfold tailWord_6918387
  simp only [CollatzResearch.WordTrace]
  refine ⟨252334303986872940275401415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168222869324581960183600943 252334303986872940275401415)
  ·
    refine ⟨378501455980309410413102123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252334303986872940275401415 378501455980309410413102123)
    ·
      refine ⟨567752183970464115619653185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378501455980309410413102123 567752183970464115619653185)
      ·
        refine ⟨425814137977848086714739889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567752183970464115619653185 425814137977848086714739889)
        ·
          refine ⟨319360603483386065036054917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425814137977848086714739889 319360603483386065036054917)
          ·
            refine ⟨59880113153134887194260297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319360603483386065036054917 59880113153134887194260297)
            ·
              refine ⟨44910084864851165395695223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59880113153134887194260297 44910084864851165395695223)
              ·
                refine ⟨67365127297276748093542835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44910084864851165395695223 67365127297276748093542835)
                ·
                  refine ⟨101047690945915122140314253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67365127297276748093542835 101047690945915122140314253)
                  ·
                    refine ⟨37892884104718170802617845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101047690945915122140314253 37892884104718170802617845)
                    ·
                      refine ⟨3552457884817328512745423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37892884104718170802617845 3552457884817328512745423)
                      ·
                        rfl

theorem cell23_6918387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_6918387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918387 prefixEnd_6918387 := by exact prefixLift 6918387
  have htrace : WordTrace (prefixWord ++ tailWord_6918387) baseStart_6918387 baseEnd_6918387 := by
    simpa [prefixWord, tailWord_6918387, baseEnd_6918387] using wordTrace_append hprefix tailTrace_6918387
  have hstable : (prefixWord ++ tailWord_6918387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918387).length < 2 ^ (prefixWord ++ tailWord_6918387).sum := by decide
  have hdescent : baseEnd_6918387 < baseStart_6918387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918414 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_6918414 : Nat := 118140960795 + 6918414 * 2 ^ 59
def prefixEnd_6918414 : Nat := 4983230072969 + 3 ^ 40 * 6918414 * 2
def baseEnd_6918414 : Nat := 3552471748794999907107799

theorem tailTrace_6918414 : CollatzResearch.WordTrace tailWord_6918414 prefixEnd_6918414 3552471748794999907107799 := by
  unfold tailWord_6918414
  simp only [CollatzResearch.WordTrace]
  refine ⟨31541911094721890485829287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168223525838516749257756197 31541911094721890485829287)
  ·
    refine ⟨47312866642082835728743931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31541911094721890485829287 47312866642082835728743931)
    ·
      refine ⟨70969299963124253593115897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47312866642082835728743931 70969299963124253593115897)
      ·
        refine ⟨53226974972343190194836923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70969299963124253593115897 53226974972343190194836923)
        ·
          refine ⟨79840462458514785292255385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53226974972343190194836923 79840462458514785292255385)
          ·
            refine ⟨59880346843886088969191539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79840462458514785292255385 59880346843886088969191539)
            ·
              refine ⟨89820520265829133453787309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59880346843886088969191539 89820520265829133453787309)
              ·
                refine ⟨33682695099685925045170241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89820520265829133453787309 33682695099685925045170241)
                ·
                  refine ⟨25262021324764443783877681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33682695099685925045170241 25262021324764443783877681)
                  ·
                    refine ⟨18946515993573332837908261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25262021324764443783877681 18946515993573332837908261)
                    ·
                      refine ⟨3552471748794999907107799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18946515993573332837908261 3552471748794999907107799)
                      ·
                        rfl

theorem cell23_6918414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_6918414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918414 prefixEnd_6918414 := by exact prefixLift 6918414
  have htrace : WordTrace (prefixWord ++ tailWord_6918414) baseStart_6918414 baseEnd_6918414 := by
    simpa [prefixWord, tailWord_6918414, baseEnd_6918414] using wordTrace_append hprefix tailTrace_6918414
  have hstable : (prefixWord ++ tailWord_6918414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918414).length < 2 ^ (prefixWord ++ tailWord_6918414).sum := by decide
  have hdescent : baseEnd_6918414 < baseStart_6918414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918458 : List Nat := [3, 1, 1, 1, 4, 3, 3, 2, 5]
def baseStart_6918458 : Nat := 118140960795 + 6918458 * 2 ^ 59
def prefixEnd_6918458 : Nat := 4983230072969 + 3 ^ 40 * 6918458 * 2
def baseEnd_6918458 : Nat := 394721593549310859439733

theorem tailTrace_6918458 : CollatzResearch.WordTrace tailWord_6918458 prefixEnd_6918458 394721593549310859439733 := by
  unfold tailWord_6918458
  simp only [CollatzResearch.WordTrace]
  refine ⟨63084223392403929850309007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168224595713077146267490685 63084223392403929850309007)
  ·
    refine ⟨94626335088605894775463511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63084223392403929850309007 94626335088605894775463511)
    ·
      refine ⟨141939502632908842163195267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94626335088605894775463511 141939502632908842163195267)
      ·
        refine ⟨212909253949363263244792901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141939502632908842163195267 212909253949363263244792901)
        ·
          refine ⟨39920485115505611858398669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212909253949363263244792901 39920485115505611858398669)
          ·
            refine ⟨14970181918314604446899501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39920485115505611858398669 14970181918314604446899501)
            ·
              refine ⟨5613818219367976667587313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14970181918314604446899501 5613818219367976667587313)
              ·
                refine ⟨4210363664525982500690485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5613818219367976667587313 4210363664525982500690485)
                ·
                  refine ⟨394721593549310859439733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4210363664525982500690485 394721593549310859439733)
                  ·
                    rfl

theorem cell23_6918458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_6918458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918458 prefixEnd_6918458 := by exact prefixLift 6918458
  have htrace : WordTrace (prefixWord ++ tailWord_6918458) baseStart_6918458 baseEnd_6918458 := by
    simpa [prefixWord, tailWord_6918458, baseEnd_6918458] using wordTrace_append hprefix tailTrace_6918458
  have hstable : (prefixWord ++ tailWord_6918458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918458).length < 2 ^ (prefixWord ++ tailWord_6918458).sum := by decide
  have hdescent : baseEnd_6918458 < baseStart_6918458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918601 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 3, 2, 3]
def baseStart_6918601 : Nat := 118140960795 + 6918601 * 2 ^ 59
def prefixEnd_6918601 : Nat := 4983230072969 + 3 ^ 40 * 6918601 * 2
def baseEnd_6918601 : Nat := 3552567769677390675469439

theorem tailTrace_6918601 : CollatzResearch.WordTrace tailWord_6918601 prefixEnd_6918601 3552567769677390675469439 := by
  unfold tailWord_6918601
  simp only [CollatzResearch.WordTrace]
  refine ⟨252342109208097654823691657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168228072805398436549127771 252342109208097654823691657)
  ·
    refine ⟨189256581906073241117768743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252342109208097654823691657 189256581906073241117768743)
    ·
      refine ⟨283884872859109861676653115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189256581906073241117768743 283884872859109861676653115)
      ·
        refine ⟨425827309288664792514979673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283884872859109861676653115 425827309288664792514979673)
        ·
          refine ⟨319370481966498594386234755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425827309288664792514979673 319370481966498594386234755)
          ·
            refine ⟨479055722949747891579352133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319370481966498594386234755 479055722949747891579352133)
            ·
              refine ⟨89822948053077729671128525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 479055722949747891579352133 89822948053077729671128525)
              ·
                refine ⟨33683605519904148626673197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89822948053077729671128525 33683605519904148626673197)
                ·
                  refine ⟨12631352069964055735002449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33683605519904148626673197 12631352069964055735002449)
                  ·
                    refine ⟨9473514052473041801251837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12631352069964055735002449 9473514052473041801251837)
                    ·
                      refine ⟨3552567769677390675469439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9473514052473041801251837 3552567769677390675469439)
                      ·
                        rfl

theorem cell23_6918601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2, 3].length) (baseStart_6918601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918601 prefixEnd_6918601 := by exact prefixLift 6918601
  have htrace : WordTrace (prefixWord ++ tailWord_6918601) baseStart_6918601 baseEnd_6918601 := by
    simpa [prefixWord, tailWord_6918601, baseEnd_6918601] using wordTrace_append hprefix tailTrace_6918601
  have hstable : (prefixWord ++ tailWord_6918601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918601).length < 2 ^ (prefixWord ++ tailWord_6918601).sum := by decide
  have hdescent : baseEnd_6918601 < baseStart_6918601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918618 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3]
def baseStart_6918618 : Nat := 118140960795 + 6918618 * 2 ^ 59
def prefixEnd_6918618 : Nat := 4983230072969 + 3 ^ 40 * 6918618 * 2
def baseEnd_6918618 : Nat := 3552576498848517108956861

theorem tailTrace_6918618 : CollatzResearch.WordTrace tailWord_6918618 prefixEnd_6918618 3552576498848517108956861 := by
  unfold tailWord_6918618
  simp only [CollatzResearch.WordTrace]
  refine ⟨63085682312259016681765127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168228486166024044484707005 63085682312259016681765127)
  ·
    refine ⟨94628523468388525022647691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63085682312259016681765127 94628523468388525022647691)
    ·
      refine ⟨141942785202582787533971537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94628523468388525022647691 141942785202582787533971537)
      ·
        refine ⟨106457088901937090650478653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141942785202582787533971537 106457088901937090650478653)
        ·
          refine ⟨39921408338226408993929495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106457088901937090650478653 39921408338226408993929495)
          ·
            refine ⟨59882112507339613490894243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39921408338226408993929495 59882112507339613490894243)
            ·
              refine ⟨89823168761009420236341365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59882112507339613490894243 89823168761009420236341365)
              ·
                refine ⟨8420922071344633147157003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89823168761009420236341365 8420922071344633147157003)
                ·
                  refine ⟨12631383107016949720735505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8420922071344633147157003 12631383107016949720735505)
                  ·
                    refine ⟨9473537330262712290551629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12631383107016949720735505 9473537330262712290551629)
                    ·
                      refine ⟨3552576498848517108956861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9473537330262712290551629 3552576498848517108956861)
                      ·
                        rfl

theorem cell23_6918618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_6918618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918618 prefixEnd_6918618 := by exact prefixLift 6918618
  have htrace : WordTrace (prefixWord ++ tailWord_6918618) baseStart_6918618 baseEnd_6918618 := by
    simpa [prefixWord, tailWord_6918618, baseEnd_6918618] using wordTrace_append hprefix tailTrace_6918618
  have hstable : (prefixWord ++ tailWord_6918618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918618).length < 2 ^ (prefixWord ++ tailWord_6918618).sum := by decide
  have hdescent : baseEnd_6918618 < baseStart_6918618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918626 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6918626 : Nat := 118140960795 + 6918626 * 2 ^ 59
def prefixEnd_6918626 : Nat := 4983230072969 + 3 ^ 40 * 6918626 * 2
def baseEnd_6918626 : Nat := 3552580606693753077656825

theorem tailTrace_6918626 : CollatzResearch.WordTrace tailWord_6918626 prefixEnd_6918626 3552580606693753077656825 := by
  unfold tailWord_6918626
  simp only [CollatzResearch.WordTrace]
  refine ⟨63085755258251771023337933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168228680688671389395567821 63085755258251771023337933)
  ·
    refine ⟨23657158221844414133751725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63085755258251771023337933 23657158221844414133751725)
    ·
      refine ⟨8871434333191655300156897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23657158221844414133751725 8871434333191655300156897)
      ·
        refine ⟨6653575749893741475117673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8871434333191655300156897 6653575749893741475117673)
        ·
          refine ⟨4990181812420306106338255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6653575749893741475117673 4990181812420306106338255)
          ·
            refine ⟨7485272718630459159507383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990181812420306106338255 7485272718630459159507383)
            ·
              refine ⟨11227909077945688739261075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7485272718630459159507383 11227909077945688739261075)
              ·
                refine ⟨16841863616918533108891613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11227909077945688739261075 16841863616918533108891613)
                ·
                  refine ⟨6315698856344449915834355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16841863616918533108891613 6315698856344449915834355)
                  ·
                    refine ⟨9473548284516674873751533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6315698856344449915834355 9473548284516674873751533)
                    ·
                      refine ⟨3552580606693753077656825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9473548284516674873751533 3552580606693753077656825)
                      ·
                        rfl

theorem cell23_6918626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6918626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918626 prefixEnd_6918626 := by exact prefixLift 6918626
  have htrace : WordTrace (prefixWord ++ tailWord_6918626) baseStart_6918626 baseEnd_6918626 := by
    simpa [prefixWord, tailWord_6918626, baseEnd_6918626] using wordTrace_append hprefix tailTrace_6918626
  have hstable : (prefixWord ++ tailWord_6918626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918626).length < 2 ^ (prefixWord ++ tailWord_6918626).sum := by decide
  have hdescent : baseEnd_6918626 < baseStart_6918626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918632 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_6918632 : Nat := 118140960795 + 6918632 * 2 ^ 59
def prefixEnd_6918632 : Nat := 4983230072969 + 3 ^ 40 * 6918632 * 2
def baseEnd_6918632 : Nat := 3552583687577680054181797

theorem tailTrace_6918632 : CollatzResearch.WordTrace tailWord_6918632 prefixEnd_6918632 3552583687577680054181797 := by
  unfold tailWord_6918632
  simp only [CollatzResearch.WordTrace]
  refine ⟨126171619935492673559035075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168228826580656898078713433 126171619935492673559035075)
  ·
    refine ⟨189257429903239010338552613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126171619935492673559035075 189257429903239010338552613)
    ·
      refine ⟨35485768106857314438478615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189257429903239010338552613 35485768106857314438478615)
      ·
        refine ⟨53228652160285971657717923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35485768106857314438478615 53228652160285971657717923)
        ·
          refine ⟨79842978240428957486576885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53228652160285971657717923 79842978240428957486576885)
          ·
            refine ⟨7485279210040214764366583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79842978240428957486576885 7485279210040214764366583)
            ·
              refine ⟨11227918815060322146549875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7485279210040214764366583 11227918815060322146549875)
              ·
                refine ⟨16841878222590483219824813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11227918815060322146549875 16841878222590483219824813)
                ·
                  refine ⟨6315704333471431207434305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16841878222590483219824813 6315704333471431207434305)
                  ·
                    refine ⟨4736778250103573405575729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6315704333471431207434305 4736778250103573405575729)
                    ·
                      refine ⟨3552583687577680054181797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4736778250103573405575729 3552583687577680054181797)
                      ·
                        rfl

theorem cell23_6918632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_6918632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918632 prefixEnd_6918632 := by exact prefixLift 6918632
  have htrace : WordTrace (prefixWord ++ tailWord_6918632) baseStart_6918632 baseEnd_6918632 := by
    simpa [prefixWord, tailWord_6918632, baseEnd_6918632] using wordTrace_append hprefix tailTrace_6918632
  have hstable : (prefixWord ++ tailWord_6918632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918632).length < 2 ^ (prefixWord ++ tailWord_6918632).sum := by decide
  have hdescent : baseEnd_6918632 < baseStart_6918632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918662 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6918662 : Nat := 118140960795 + 6918662 * 2 ^ 59
def prefixEnd_6918662 : Nat := 4983230072969 + 3 ^ 40 * 6918662 * 2
def baseEnd_6918662 : Nat := 3552599091997314936806659

theorem tailTrace_6918662 : CollatzResearch.WordTrace tailWord_6918662 prefixEnd_6918662 3552599091997314936806659 := by
  unfold tailWord_6918662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885760439402395695051945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168229556040584441494441493 7885760439402395695051945)
  ·
    refine ⟨5914320329551796771288959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7885760439402395695051945 5914320329551796771288959)
    ·
      refine ⟨8871480494327695156933439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5914320329551796771288959 8871480494327695156933439)
      ·
        refine ⟨13307220741491542735400159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8871480494327695156933439 13307220741491542735400159)
        ·
          refine ⟨19960831112237314103100239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13307220741491542735400159 19960831112237314103100239)
          ·
            refine ⟨29941246668355971154650359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19960831112237314103100239 29941246668355971154650359)
            ·
              refine ⟨44911870002533956731975539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29941246668355971154650359 44911870002533956731975539)
              ·
                refine ⟨67367805003800935097963309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44911870002533956731975539 67367805003800935097963309)
                ·
                  refine ⟨25262926876425350661736241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67367805003800935097963309 25262926876425350661736241)
                  ·
                    refine ⟨18947195157319012996302181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25262926876425350661736241 18947195157319012996302181)
                    ·
                      refine ⟨3552599091997314936806659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18947195157319012996302181 3552599091997314936806659)
                      ·
                        rfl

theorem cell23_6918662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6918662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918662 prefixEnd_6918662 := by exact prefixLift 6918662
  have htrace : WordTrace (prefixWord ++ tailWord_6918662) baseStart_6918662 baseEnd_6918662 := by
    simpa [prefixWord, tailWord_6918662, baseEnd_6918662] using wordTrace_append hprefix tailTrace_6918662
  have hstable : (prefixWord ++ tailWord_6918662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918662).length < 2 ^ (prefixWord ++ tailWord_6918662).sum := by decide
  have hdescent : baseEnd_6918662 < baseStart_6918662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918698 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_6918698 : Nat := 118140960795 + 6918698 * 2 ^ 59
def prefixEnd_6918698 : Nat := 4983230072969 + 3 ^ 40 * 6918698 * 2
def baseEnd_6918698 : Nat := 1184205859100292265318831

theorem tailTrace_6918698 : CollatzResearch.WordTrace tailWord_6918698 prefixEnd_6918698 1184205859100292265318831 := by
  unfold tailWord_6918698
  simp only [CollatzResearch.WordTrace]
  refine ⟨63086411772186560097493187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168230431392497493593315165 63086411772186560097493187)
  ·
    refine ⟨94629617658279840146239781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63086411772186560097493187 94629617658279840146239781)
    ·
      refine ⟨17743053310927470027419959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94629617658279840146239781 17743053310927470027419959)
      ·
        refine ⟨26614579966391205041129939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17743053310927470027419959 26614579966391205041129939)
        ·
          refine ⟨39921869949586807561694909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26614579966391205041129939 39921869949586807561694909)
          ·
            refine ⟨14970701231095052835635591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39921869949586807561694909 14970701231095052835635591)
            ·
              refine ⟨22456051846642579253453387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14970701231095052835635591 22456051846642579253453387)
              ·
                refine ⟨33684077769963868880180081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22456051846642579253453387 33684077769963868880180081)
                ·
                  refine ⟨25263058327472901660135061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33684077769963868880180081 25263058327472901660135061)
                  ·
                    refine ⟨1184205859100292265318831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25263058327472901660135061 1184205859100292265318831)
                    ·
                      rfl

theorem cell23_6918698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_6918698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918698 prefixEnd_6918698 := by exact prefixLift 6918698
  have htrace : WordTrace (prefixWord ++ tailWord_6918698) baseStart_6918698 baseEnd_6918698 := by
    simpa [prefixWord, tailWord_6918698, baseEnd_6918698] using wordTrace_append hprefix tailTrace_6918698
  have hstable : (prefixWord ++ tailWord_6918698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918698).length < 2 ^ (prefixWord ++ tailWord_6918698).sum := by decide
  have hdescent : baseEnd_6918698 < baseStart_6918698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918711 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 7]
def baseStart_6918711 : Nat := 118140960795 + 6918711 * 2 ^ 59
def prefixEnd_6918711 : Nat := 4983230072969 + 3 ^ 40 * 6918711 * 2
def baseEnd_6918711 : Nat := 394736028061042805010437

theorem tailTrace_6918711 : CollatzResearch.WordTrace tailWord_6918711 prefixEnd_6918711 394736028061042805010437 := by
  unfold tailWord_6918711
  simp only [CollatzResearch.WordTrace]
  refine ⟨252346121237699143610195987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168230747491799429073463991 252346121237699143610195987)
  ·
    refine ⟨378519181856548715415293981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252346121237699143610195987 378519181856548715415293981)
    ·
      refine ⟨141944693196205768280735243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378519181856548715415293981 141944693196205768280735243)
      ·
        refine ⟨212917039794308652421102865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141944693196205768280735243 212917039794308652421102865)
        ·
          refine ⟨159687779845731489315827149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212917039794308652421102865 159687779845731489315827149)
          ·
            refine ⟨59882917442149308493435181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159687779845731489315827149 59882917442149308493435181)
            ·
              refine ⟨22456094040805990685038193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59882917442149308493435181 22456094040805990685038193)
              ·
                refine ⟨16842070530604493013778645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22456094040805990685038193 16842070530604493013778645)
                ·
                  refine ⟨394736028061042805010437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16842070530604493013778645 394736028061042805010437)
                  ·
                    rfl

theorem cell23_6918711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 7].length) (baseStart_6918711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918711 prefixEnd_6918711 := by exact prefixLift 6918711
  have htrace : WordTrace (prefixWord ++ tailWord_6918711) baseStart_6918711 baseEnd_6918711 := by
    simpa [prefixWord, tailWord_6918711, baseEnd_6918711] using wordTrace_append hprefix tailTrace_6918711
  have hstable : (prefixWord ++ tailWord_6918711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918711).length < 2 ^ (prefixWord ++ tailWord_6918711).sum := by decide
  have hdescent : baseEnd_6918711 < baseStart_6918711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918726 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_6918726 : Nat := 118140960795 + 6918726 * 2 ^ 59
def prefixEnd_6918726 : Nat := 4983230072969 + 3 ^ 40 * 6918726 * 2
def baseEnd_6918726 : Nat := 3552631954759202686406365

theorem tailTrace_6918726 : CollatzResearch.WordTrace tailWord_6918726 prefixEnd_6918726 3552631954759202686406365 := by
  unfold tailWord_6918726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885833385395150036624751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168231112221763200781328021 7885833385395150036624751)
  ·
    refine ⟨11828750078092725054937127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7885833385395150036624751 11828750078092725054937127)
    ·
      refine ⟨17743125117139087582405691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11828750078092725054937127 17743125117139087582405691)
      ·
        refine ⟨26614687675708631373608537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17743125117139087582405691 26614687675708631373608537)
        ·
          refine ⟨19961015756781473530206403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26614687675708631373608537 19961015756781473530206403)
          ·
            refine ⟨29941523635172210295309605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19961015756781473530206403 29941523635172210295309605)
            ·
              refine ⟨5614035681594789430370551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29941523635172210295309605 5614035681594789430370551)
              ·
                refine ⟨8421053522392184145555827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614035681594789430370551 8421053522392184145555827)
                ·
                  refine ⟨12631580283588276218333741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8421053522392184145555827 12631580283588276218333741)
                  ·
                    refine ⟨4736842606345603581875153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12631580283588276218333741 4736842606345603581875153)
                    ·
                      refine ⟨3552631954759202686406365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4736842606345603581875153 3552631954759202686406365)
                      ·
                        rfl

theorem cell23_6918726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_6918726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918726 prefixEnd_6918726 := by exact prefixLift 6918726
  have htrace : WordTrace (prefixWord ++ tailWord_6918726) baseStart_6918726 baseEnd_6918726 := by
    simpa [prefixWord, tailWord_6918726, baseEnd_6918726] using wordTrace_append hprefix tailTrace_6918726
  have hstable : (prefixWord ++ tailWord_6918726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918726).length < 2 ^ (prefixWord ++ tailWord_6918726).sum := by decide
  have hdescent : baseEnd_6918726 < baseStart_6918726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918738 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_6918738 : Nat := 118140960795 + 6918738 * 2 ^ 59
def prefixEnd_6918738 : Nat := 4983230072969 + 3 ^ 40 * 6918738 * 2
def baseEnd_6918738 : Nat := 3552638116527056639456309

theorem tailTrace_6918738 : CollatzResearch.WordTrace tailWord_6918738 prefixEnd_6918738 3552638116527056639456309 := by
  unfold tailWord_6918738
  simp only [CollatzResearch.WordTrace]
  refine ⟨63086776502150331805357217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168231404005734218147619245 63086776502150331805357217)
  ·
    refine ⟨47315082376612748854017913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63086776502150331805357217 47315082376612748854017913)
    ·
      refine ⟨35486311782459561640513435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47315082376612748854017913 35486311782459561640513435)
      ·
        refine ⟨53229467673689342460770153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35486311782459561640513435 53229467673689342460770153)
        ·
          refine ⟨39922100755267006845577615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53229467673689342460770153 39922100755267006845577615)
          ·
            refine ⟨59883151132900510268366423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39922100755267006845577615 59883151132900510268366423)
            ·
              refine ⟨89824726699350765402549635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59883151132900510268366423 89824726699350765402549635)
              ·
                refine ⟨134737090049026148103824453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89824726699350765402549635 134737090049026148103824453)
                ·
                  refine ⟨25263204384192402769467085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134737090049026148103824453 25263204384192402769467085)
                  ·
                    refine ⟨9473701644072151038550157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25263204384192402769467085 9473701644072151038550157)
                    ·
                      refine ⟨3552638116527056639456309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9473701644072151038550157 3552638116527056639456309)
                      ·
                        rfl

theorem cell23_6918738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_6918738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918738 prefixEnd_6918738 := by exact prefixLift 6918738
  have htrace : WordTrace (prefixWord ++ tailWord_6918738) baseStart_6918738 baseEnd_6918738 := by
    simpa [prefixWord, tailWord_6918738, baseEnd_6918738] using wordTrace_append hprefix tailTrace_6918738
  have hstable : (prefixWord ++ tailWord_6918738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918738).length < 2 ^ (prefixWord ++ tailWord_6918738).sum := by decide
  have hdescent : baseEnd_6918738 < baseStart_6918738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918751 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 5]
def baseStart_6918751 : Nat := 118140960795 + 6918751 * 2 ^ 59
def prefixEnd_6918751 : Nat := 4983230072969 + 3 ^ 40 * 6918751 * 2
def baseEnd_6918751 : Nat := 3552644791775565088593749

theorem tailTrace_6918751 : CollatzResearch.WordTrace tailWord_6918751 prefixEnd_6918751 3552644791775565088593749 := by
  unfold tailWord_6918751
  simp only [CollatzResearch.WordTrace]
  refine ⟨252347580157554230441652107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168231720105036153627768071 252347580157554230441652107)
  ·
    refine ⟨378521370236331345662478161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252347580157554230441652107 378521370236331345662478161)
    ·
      refine ⟨283891027677248509246858621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378521370236331345662478161 283891027677248509246858621)
      ·
        refine ⟨106459135378968190967571983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283891027677248509246858621 106459135378968190967571983)
        ·
          refine ⟨159688703068452286451357975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106459135378968190967571983 159688703068452286451357975)
          ·
            refine ⟨239533054602678429677036963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159688703068452286451357975 239533054602678429677036963)
            ·
              refine ⟨359299581904017644515555445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239533054602678429677036963 359299581904017644515555445)
              ·
                refine ⟨33684335803501654173333323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 359299581904017644515555445 33684335803501654173333323)
                ·
                  refine ⟨50526503705252481259999985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33684335803501654173333323 50526503705252481259999985)
                  ·
                    refine ⟨37894877778939360944999989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50526503705252481259999985 37894877778939360944999989)
                    ·
                      refine ⟨3552644791775565088593749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37894877778939360944999989 3552644791775565088593749)
                      ·
                        rfl

theorem cell23_6918751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_6918751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918751 prefixEnd_6918751 := by exact prefixLift 6918751
  have htrace : WordTrace (prefixWord ++ tailWord_6918751) baseStart_6918751 baseEnd_6918751 := by
    simpa [prefixWord, tailWord_6918751, baseEnd_6918751] using wordTrace_append hprefix tailTrace_6918751
  have hstable : (prefixWord ++ tailWord_6918751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918751).length < 2 ^ (prefixWord ++ tailWord_6918751).sum := by decide
  have hdescent : baseEnd_6918751 < baseStart_6918751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918855 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 4, 3, 2]
def baseStart_6918855 : Nat := 118140960795 + 6918855 * 2 ^ 59
def prefixEnd_6918855 : Nat := 4983230072969 + 3 ^ 40 * 6918855 * 2
def baseEnd_6918855 : Nat := 3552698193763632681693271

theorem tailTrace_6918855 : CollatzResearch.WordTrace tailWord_6918855 prefixEnd_6918855 3552698193763632681693271 := by
  unfold tailWord_6918855
  simp only [CollatzResearch.WordTrace]
  refine ⟨252351373349177456203438019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168234248899451637468958679 252351373349177456203438019)
  ·
    refine ⟨378527060023766184305157029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252351373349177456203438019 378527060023766184305157029)
    ·
      refine ⟨70973823754456159557216943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 378527060023766184305157029 70973823754456159557216943)
      ·
        refine ⟨106460735631684239335825415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70973823754456159557216943 106460735631684239335825415)
        ·
          refine ⟨159691103447526359003738123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106460735631684239335825415 159691103447526359003738123)
          ·
            refine ⟨239536655171289538505607185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159691103447526359003738123 239536655171289538505607185)
            ·
              refine ⟨179652491378467153879205389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239536655171289538505607185 179652491378467153879205389)
              ·
                refine ⟨67369684266925182704702021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179652491378467153879205389 67369684266925182704702021)
                ·
                  refine ⟨12631815800048471757131629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67369684266925182704702021 12631815800048471757131629)
                  ·
                    refine ⟨4736930925018176908924361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12631815800048471757131629 4736930925018176908924361)
                    ·
                      refine ⟨3552698193763632681693271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4736930925018176908924361 3552698193763632681693271)
                      ·
                        rfl

theorem cell23_6918855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_6918855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918855 prefixEnd_6918855 := by exact prefixLift 6918855
  have htrace : WordTrace (prefixWord ++ tailWord_6918855) baseStart_6918855 baseEnd_6918855 := by
    simpa [prefixWord, tailWord_6918855, baseEnd_6918855] using wordTrace_append hprefix tailTrace_6918855
  have hstable : (prefixWord ++ tailWord_6918855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918855).length < 2 ^ (prefixWord ++ tailWord_6918855).sum := by decide
  have hdescent : baseEnd_6918855 < baseStart_6918855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918885 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_6918885 : Nat := 118140960795 + 6918885 * 2 ^ 59
def prefixEnd_6918885 : Nat := 4983230072969 + 3 ^ 40 * 6918885 * 2
def baseEnd_6918885 : Nat := 3552713598183267564318133

theorem tailTrace_6918885 : CollatzResearch.WordTrace tailWord_6918885 prefixEnd_6918885 3552713598183267564318133 := by
  unfold tailWord_6918885
  simp only [CollatzResearch.WordTrace]
  refine ⟨252352467539068771327030109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168234978359379180884686739 252352467539068771327030109)
  ·
    refine ⟨94632175327150789247636291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252352467539068771327030109 94632175327150789247636291)
    ·
      refine ⟨141948262990726183871454437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94632175327150789247636291 141948262990726183871454437)
      ·
        refine ⟨26615299310761159475897707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141948262990726183871454437 26615299310761159475897707)
        ·
          refine ⟨39922948966141739213846561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26615299310761159475897707 39922948966141739213846561)
          ·
            refine ⟨29942211724606304410384921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39922948966141739213846561 29942211724606304410384921)
            ·
              refine ⟨22456658793454728307788691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29942211724606304410384921 22456658793454728307788691)
              ·
                refine ⟨33684988190182092461683037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22456658793454728307788691 33684988190182092461683037)
                ·
                  refine ⟨12631870571318284673131139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33684988190182092461683037 12631870571318284673131139)
                  ·
                    refine ⟨18947805856977427009696709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12631870571318284673131139 18947805856977427009696709)
                    ·
                      refine ⟨3552713598183267564318133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18947805856977427009696709 3552713598183267564318133)
                      ·
                        rfl

theorem cell23_6918885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_6918885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918885 prefixEnd_6918885 := by exact prefixLift 6918885
  have htrace : WordTrace (prefixWord ++ tailWord_6918885) baseStart_6918885 baseEnd_6918885 := by
    simpa [prefixWord, tailWord_6918885, baseEnd_6918885] using wordTrace_append hprefix tailTrace_6918885
  have hstable : (prefixWord ++ tailWord_6918885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918885).length < 2 ^ (prefixWord ++ tailWord_6918885).sum := by decide
  have hdescent : baseEnd_6918885 < baseStart_6918885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918902 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_6918902 : Nat := 118140960795 + 6918902 * 2 ^ 59
def prefixEnd_6918902 : Nat := 4983230072969 + 3 ^ 40 * 6918902 * 2
def baseEnd_6918902 : Nat := 3552722327354393997805555

theorem tailTrace_6918902 : CollatzResearch.WordTrace tailWord_6918902 prefixEnd_6918902 3552722327354393997805555 := by
  unfold tailWord_6918902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15772067973750448951899935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168235391720004788820265973 15772067973750448951899935)
  ·
    refine ⟨23658101960625673427849903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15772067973750448951899935 23658101960625673427849903)
    ·
      refine ⟨35487152940938510141774855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23658101960625673427849903 35487152940938510141774855)
      ·
        refine ⟨53230729411407765212662283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35487152940938510141774855 53230729411407765212662283)
        ·
          refine ⟨79846094117111647818993425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53230729411407765212662283 79846094117111647818993425)
          ·
            refine ⟨59884570587833735864245069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79846094117111647818993425 59884570587833735864245069)
            ·
              refine ⟨22456713970437650949091901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59884570587833735864245069 22456713970437650949091901)
              ·
                refine ⟨8421267738914119105909463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22456713970437650949091901 8421267738914119105909463)
                ·
                  refine ⟨12631901608371178658864195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8421267738914119105909463 12631901608371178658864195)
                  ·
                    refine ⟨18947852412556767988296293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12631901608371178658864195 18947852412556767988296293)
                    ·
                      refine ⟨3552722327354393997805555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18947852412556767988296293 3552722327354393997805555)
                      ·
                        rfl

theorem cell23_6918902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_6918902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918902 prefixEnd_6918902 := by exact prefixLift 6918902
  have htrace : WordTrace (prefixWord ++ tailWord_6918902) baseStart_6918902 baseEnd_6918902 := by
    simpa [prefixWord, tailWord_6918902, baseEnd_6918902] using wordTrace_append hprefix tailTrace_6918902
  have hstable : (prefixWord ++ tailWord_6918902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918902).length < 2 ^ (prefixWord ++ tailWord_6918902).sum := by decide
  have hdescent : baseEnd_6918902 < baseStart_6918902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918908 : List Nat := [2, 2, 2, 1, 3, 3, 10]
def baseStart_6918908 : Nat := 118140960795 + 6918908 * 2 ^ 59
def prefixEnd_6918908 : Nat := 4983230072969 + 3 ^ 40 * 6918908 * 2
def baseEnd_6918908 : Nat := 43860807509115073757167

theorem tailTrace_6918908 : CollatzResearch.WordTrace tailWord_6918908 prefixEnd_6918908 43860807509115073757167 := by
  unfold tailWord_6918908
  simp only [CollatzResearch.WordTrace]
  refine ⟨126176653208992723127558689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168235537611990297503411585 126176653208992723127558689)
  ·
    refine ⟨94632489906744542345669017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126176653208992723127558689 94632489906744542345669017)
    ·
      refine ⟨70974367430058406759251763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94632489906744542345669017 70974367430058406759251763)
      ·
        refine ⟨106461551145087610138877645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70974367430058406759251763 106461551145087610138877645)
        ·
          refine ⟨39923081679407853802079117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106461551145087610138877645 39923081679407853802079117)
          ·
            refine ⟨14971155629777945175779669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39923081679407853802079117 14971155629777945175779669)
            ·
              refine ⟨43860807509115073757167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14971155629777945175779669 43860807509115073757167)
              ·
                rfl

theorem cell23_6918908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 10].length) (baseStart_6918908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918908 prefixEnd_6918908 := by exact prefixLift 6918908
  have htrace : WordTrace (prefixWord ++ tailWord_6918908) baseStart_6918908 baseEnd_6918908 := by
    simpa [prefixWord, tailWord_6918908, baseEnd_6918908] using wordTrace_append hprefix tailTrace_6918908
  have hstable : (prefixWord ++ tailWord_6918908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918908).length < 2 ^ (prefixWord ++ tailWord_6918908).sum := by decide
  have hdescent : baseEnd_6918908 < baseStart_6918908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918919 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 3, 2, 2]
def baseStart_6918919 : Nat := 118140960795 + 6918919 * 2 ^ 59
def prefixEnd_6918919 : Nat := 4983230072969 + 3 ^ 40 * 6918919 * 2
def baseEnd_6918919 : Nat := 3552731056525520431292977

theorem tailTrace_6918919 : CollatzResearch.WordTrace tailWord_6918919 prefixEnd_6918919 3552731056525520431292977 := by
  unfold tailWord_6918919
  simp only [CollatzResearch.WordTrace]
  refine ⟨252353707620945595133767811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168235805080630396755845207 252353707620945595133767811)
  ·
    refine ⟨378530561431418392700651717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252353707620945595133767811 378530561431418392700651717)
    ·
      refine ⟨70974480268390948631372197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 378530561431418392700651717 70974480268390948631372197)
      ·
        refine ⟨13307715050323302868382287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70974480268390948631372197 13307715050323302868382287)
        ·
          refine ⟨19961572575484954302573431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13307715050323302868382287 19961572575484954302573431)
          ·
            refine ⟨29942358863227431453860147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19961572575484954302573431 29942358863227431453860147)
            ·
              refine ⟨44913538294841147180790221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29942358863227431453860147 44913538294841147180790221)
              ·
                refine ⟨16842576860565430192796333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44913538294841147180790221 16842576860565430192796333)
                ·
                  refine ⟨6315966322712036322298625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16842576860565430192796333 6315966322712036322298625)
                  ·
                    refine ⟨4736974742034027241723969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6315966322712036322298625 4736974742034027241723969)
                    ·
                      refine ⟨3552731056525520431292977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4736974742034027241723969 3552731056525520431292977)
                      ·
                        rfl

theorem cell23_6918919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_6918919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918919 prefixEnd_6918919 := by exact prefixLift 6918919
  have htrace : WordTrace (prefixWord ++ tailWord_6918919) baseStart_6918919 baseEnd_6918919 := by
    simpa [prefixWord, tailWord_6918919, baseEnd_6918919] using wordTrace_append hprefix tailTrace_6918919
  have hstable : (prefixWord ++ tailWord_6918919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918919).length < 2 ^ (prefixWord ++ tailWord_6918919).sum := by decide
  have hdescent : baseEnd_6918919 < baseStart_6918919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918952 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_6918952 : Nat := 118140960795 + 6918952 * 2 ^ 59
def prefixEnd_6918952 : Nat := 4983230072969 + 3 ^ 40 * 6918952 * 2
def baseEnd_6918952 : Nat := 3552748001387118802180325

theorem tailTrace_6918952 : CollatzResearch.WordTrace tailWord_6918952 prefixEnd_6918952 3552748001387118802180325 := by
  unfold tailWord_6918952
  simp only [CollatzResearch.WordTrace]
  refine ⟨126177455614913020884859555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168236607486550694513146073 126177455614913020884859555)
  ·
    refine ⟨189266183422369531327289333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126177455614913020884859555 189266183422369531327289333)
    ·
      refine ⟨17743704695847143561933375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189266183422369531327289333 17743704695847143561933375)
      ·
        refine ⟨26615557043770715342900063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17743704695847143561933375 26615557043770715342900063)
        ·
          refine ⟨39923335565656073014350095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26615557043770715342900063 39923335565656073014350095)
          ·
            refine ⟨59885003348484109521525143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39923335565656073014350095 59885003348484109521525143)
            ·
              refine ⟨89827505022726164282287715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59885003348484109521525143 89827505022726164282287715)
              ·
                refine ⟨134741257534089246423431573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89827505022726164282287715 134741257534089246423431573)
                ·
                  refine ⟨6315996446910433426098355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134741257534089246423431573 6315996446910433426098355)
                  ·
                    refine ⟨9473994670365650139147533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6315996446910433426098355 9473994670365650139147533)
                    ·
                      refine ⟨3552748001387118802180325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9473994670365650139147533 3552748001387118802180325)
                      ·
                        rfl

theorem cell23_6918952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_6918952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918952 prefixEnd_6918952 := by exact prefixLift 6918952
  have htrace : WordTrace (prefixWord ++ tailWord_6918952) baseStart_6918952 baseEnd_6918952 := by
    simpa [prefixWord, tailWord_6918952, baseEnd_6918952] using wordTrace_append hprefix tailTrace_6918952
  have hstable : (prefixWord ++ tailWord_6918952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918952).length < 2 ^ (prefixWord ++ tailWord_6918952).sum := by decide
  have hdescent : baseEnd_6918952 < baseStart_6918952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6918980 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6918980 : Nat := 118140960795 + 6918980 * 2 ^ 59
def prefixEnd_6918980 : Nat := 4983230072969 + 3 ^ 40 * 6918980 * 2
def baseEnd_6918980 : Nat := 1184254126281814897543399

theorem tailTrace_6918980 : CollatzResearch.WordTrace tailWord_6918980 prefixEnd_6918980 1184254126281814897543399 := by
  unfold tailWord_6918980
  simp only [CollatzResearch.WordTrace]
  refine ⟨126177966236862301275869197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168237288315816401701158929 126177966236862301275869197)
  ·
    refine ⟨47316737338823362978450949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126177966236862301275869197 47316737338823362978450949)
    ·
      refine ⟨8871888251029380558459553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47316737338823362978450949 8871888251029380558459553)
      ·
        refine ⟨6653916188272035418844665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8871888251029380558459553 6653916188272035418844665)
        ·
          refine ⟨4990437141204026564133499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6653916188272035418844665 4990437141204026564133499)
          ·
            refine ⟨7485655711806039846200249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990437141204026564133499 7485655711806039846200249)
            ·
              refine ⟨5614241783854529884650187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7485655711806039846200249 5614241783854529884650187)
              ·
                refine ⟨8421362675781794826975281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614241783854529884650187 8421362675781794826975281)
                ·
                  refine ⟨6316022006836346120231461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8421362675781794826975281 6316022006836346120231461)
                  ·
                    refine ⟨1184254126281814897543399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6316022006836346120231461 1184254126281814897543399)
                    ·
                      rfl

theorem cell23_6918980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6918980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6918980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6918980 prefixEnd_6918980 := by exact prefixLift 6918980
  have htrace : WordTrace (prefixWord ++ tailWord_6918980) baseStart_6918980 baseEnd_6918980 := by
    simpa [prefixWord, tailWord_6918980, baseEnd_6918980] using wordTrace_append hprefix tailTrace_6918980
  have hstable : (prefixWord ++ tailWord_6918980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6918980).length < 2 ^ (prefixWord ++ tailWord_6918980).sum := by decide
  have hdescent : baseEnd_6918980 < baseStart_6918980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6918980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919094 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6919094 : Nat := 118140960795 + 6919094 * 2 ^ 59
def prefixEnd_6919094 : Nat := 4983230072969 + 3 ^ 40 * 6919094 * 2
def baseEnd_6919094 : Nat := 3552820915640057246604673

theorem tailTrace_6919094 : CollatzResearch.WordTrace tailWord_6919094 prefixEnd_6919094 3552820915640057246604673 := by
  unfold tailWord_6919094
  simp only [CollatzResearch.WordTrace]
  refine ⟨15772505649706975001336771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168240060263541066680925557 15772505649706975001336771)
  ·
    refine ⟨23658758474560462502005157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15772505649706975001336771 23658758474560462502005157)
    ·
      refine ⟨4436017213980086719125967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23658758474560462502005157 4436017213980086719125967)
      ·
        refine ⟨6654025820970130078688951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4436017213980086719125967 6654025820970130078688951)
        ·
          refine ⟨9981038731455195118033427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6654025820970130078688951 9981038731455195118033427)
          ·
            refine ⟨14971558097182792677050141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9981038731455195118033427 14971558097182792677050141)
            ·
              refine ⟨5614334286443547253893803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14971558097182792677050141 5614334286443547253893803)
              ·
                refine ⟨8421501429665320880840705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614334286443547253893803 8421501429665320880840705)
                ·
                  refine ⟨6316126072248990660630529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8421501429665320880840705 6316126072248990660630529)
                  ·
                    refine ⟨4737094554186742995472897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6316126072248990660630529 4737094554186742995472897)
                    ·
                      refine ⟨3552820915640057246604673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4737094554186742995472897 3552820915640057246604673)
                      ·
                        rfl

theorem cell23_6919094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6919094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919094 prefixEnd_6919094 := by exact prefixLift 6919094
  have htrace : WordTrace (prefixWord ++ tailWord_6919094) baseStart_6919094 baseEnd_6919094 := by
    simpa [prefixWord, tailWord_6919094, baseEnd_6919094] using wordTrace_append hprefix tailTrace_6919094
  have hstable : (prefixWord ++ tailWord_6919094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919094).length < 2 ^ (prefixWord ++ tailWord_6919094).sum := by decide
  have hdescent : baseEnd_6919094 < baseStart_6919094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919102 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_6919102 : Nat := 118140960795 + 6919102 * 2 ^ 59
def prefixEnd_6919102 : Nat := 4983230072969 + 3 ^ 40 * 6919102 * 2
def baseEnd_6919102 : Nat := 3552825023485293215304635

theorem tailTrace_6919102 : CollatzResearch.WordTrace tailWord_6919102 prefixEnd_6919102 3552825023485293215304635 := by
  unfold tailWord_6919102
  simp only [CollatzResearch.WordTrace]
  refine ⟨31545047772410327173459945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168240254786188411591786373 31545047772410327173459945)
  ·
    refine ⟨23658785829307745380094959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31545047772410327173459945 23658785829307745380094959)
    ·
      refine ⟨35488178743961618070142439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23658785829307745380094959 35488178743961618070142439)
      ·
        refine ⟨53232268115942427105213659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35488178743961618070142439 53232268115942427105213659)
        ·
          refine ⟨79848402173913640657820489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53232268115942427105213659 79848402173913640657820489)
          ·
            refine ⟨59886301630435230493365367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79848402173913640657820489 59886301630435230493365367)
            ·
              refine ⟨89829452445652845740048051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59886301630435230493365367 89829452445652845740048051)
              ·
                refine ⟨134744178668479268610072077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89829452445652845740048051 134744178668479268610072077)
                ·
                  refine ⟨50529067000679725728777029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134744178668479268610072077 50529067000679725728777029)
                  ·
                    refine ⟨9474200062627448574145693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50529067000679725728777029 9474200062627448574145693)
                    ·
                      refine ⟨3552825023485293215304635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9474200062627448574145693 3552825023485293215304635)
                      ·
                        rfl

theorem cell23_6919102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_6919102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919102 prefixEnd_6919102 := by exact prefixLift 6919102
  have htrace : WordTrace (prefixWord ++ tailWord_6919102) baseStart_6919102 baseEnd_6919102 := by
    simpa [prefixWord, tailWord_6919102, baseEnd_6919102] using wordTrace_append hprefix tailTrace_6919102
  have hstable : (prefixWord ++ tailWord_6919102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919102).length < 2 ^ (prefixWord ++ tailWord_6919102).sum := by decide
  have hdescent : baseEnd_6919102 < baseStart_6919102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919117 : List Nat := [1, 6, 3, 1, 2, 1, 1, 3, 5]
def baseStart_6919117 : Nat := 118140960795 + 6919117 * 2 ^ 59
def prefixEnd_6919117 : Nat := 4983230072969 + 3 ^ 40 * 6919117 * 2
def baseEnd_6919117 : Nat := 394759191743901184068563

theorem tailTrace_6919117 : CollatzResearch.WordTrace tailWord_6919117 prefixEnd_6919117 394759191743901184068563 := by
  unfold tailWord_6919117
  simp only [CollatzResearch.WordTrace]
  refine ⟨252360929274228274949475605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168240619516152183299650403 252360929274228274949475605)
  ·
    refine ⟨11829418559729450388256669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 252360929274228274949475605 11829418559729450388256669)
    ·
      refine ⟨4436031959898543895596251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11829418559729450388256669 4436031959898543895596251)
      ·
        refine ⟨6654047939847815843394377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4436031959898543895596251 6654047939847815843394377)
        ·
          refine ⟨4990535954885861882545783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6654047939847815843394377 4990535954885861882545783)
          ·
            refine ⟨7485803932328792823818675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990535954885861882545783 7485803932328792823818675)
            ·
              refine ⟨11228705898493189235728013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7485803932328792823818675 11228705898493189235728013)
              ·
                refine ⟨4210764711934945963398005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11228705898493189235728013 4210764711934945963398005)
                ·
                  refine ⟨394759191743901184068563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4210764711934945963398005 394759191743901184068563)
                  ·
                    rfl

theorem cell23_6919117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_6919117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919117 prefixEnd_6919117 := by exact prefixLift 6919117
  have htrace : WordTrace (prefixWord ++ tailWord_6919117) baseStart_6919117 baseEnd_6919117 := by
    simpa [prefixWord, tailWord_6919117, baseEnd_6919117] using wordTrace_append hprefix tailTrace_6919117
  have hstable : (prefixWord ++ tailWord_6919117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919117).length < 2 ^ (prefixWord ++ tailWord_6919117).sum := by decide
  have hdescent : baseEnd_6919117 < baseStart_6919117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919122 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 8]
def baseStart_6919122 : Nat := 118140960795 + 6919122 * 2 ^ 59
def prefixEnd_6919122 : Nat := 4983230072969 + 3 ^ 40 * 6919122 * 2
def baseEnd_6919122 : Nat := 394759477010931459672727

theorem tailTrace_6919122 : CollatzResearch.WordTrace tailWord_6919122 prefixEnd_6919122 394759477010931459672727 := by
  unfold tailWord_6919122
  simp only [CollatzResearch.WordTrace]
  refine ⟨63090277909802540200851905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168240741092806773868938413 63090277909802540200851905)
  ·
    refine ⟨47317708432351905150638929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63090277909802540200851905 47317708432351905150638929)
    ·
      refine ⟨35488281324263928862979197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47317708432351905150638929 35488281324263928862979197)
      ·
        refine ⟨13308105496598973323617199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35488281324263928862979197 13308105496598973323617199)
        ·
          refine ⟨19962158244898459985425799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13308105496598973323617199 19962158244898459985425799)
          ·
            refine ⟨29943237367347689978138699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19962158244898459985425799 29943237367347689978138699)
            ·
              refine ⟨44914856051021534967208049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29943237367347689978138699 44914856051021534967208049)
              ·
                refine ⟨33686142038266151225406037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44914856051021534967208049 33686142038266151225406037)
                ·
                  refine ⟨394759477010931459672727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33686142038266151225406037 394759477010931459672727)
                  ·
                    rfl

theorem cell23_6919122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_6919122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919122 prefixEnd_6919122 := by exact prefixLift 6919122
  have htrace : WordTrace (prefixWord ++ tailWord_6919122) baseStart_6919122 baseEnd_6919122 := by
    simpa [prefixWord, tailWord_6919122, baseEnd_6919122] using wordTrace_append hprefix tailTrace_6919122
  have hstable : (prefixWord ++ tailWord_6919122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919122).length < 2 ^ (prefixWord ++ tailWord_6919122).sum := by decide
  have hdescent : baseEnd_6919122 < baseStart_6919122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919143 : List Nat := [1, 1, 5, 2, 2, 2, 3, 2, 1, 4]
def baseStart_6919143 : Nat := 118140960795 + 6919143 * 2 ^ 59
def prefixEnd_6919143 : Nat := 4983230072969 + 3 ^ 40 * 6919143 * 2
def baseEnd_6919143 : Nat := 1184282025397375851630649

theorem tailTrace_6919143 : CollatzResearch.WordTrace tailWord_6919143 prefixEnd_6919143 1184282025397375851630649 := by
  unfold tailWord_6919143
  simp only [CollatzResearch.WordTrace]
  refine ⟨252361877572134081389922083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168241251714756054259948055 252361877572134081389922083)
  ·
    refine ⟨378542816358201122084883125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252361877572134081389922083 378542816358201122084883125)
    ·
      refine ⟨35488389033581355195457793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 378542816358201122084883125 35488389033581355195457793)
      ·
        refine ⟨26616291775186016396593345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35488389033581355195457793 26616291775186016396593345)
        ·
          refine ⟨19962218831389512297445009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26616291775186016396593345 19962218831389512297445009)
          ·
            refine ⟨14971664123542134223083757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19962218831389512297445009 14971664123542134223083757)
            ·
              refine ⟨5614374046328300333656409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14971664123542134223083757 5614374046328300333656409)
              ·
                refine ⟨4210780534746225250242307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5614374046328300333656409 4210780534746225250242307)
                ·
                  refine ⟨6316170802119337875363461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4210780534746225250242307 6316170802119337875363461)
                  ·
                    refine ⟨1184282025397375851630649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6316170802119337875363461 1184282025397375851630649)
                    ·
                      rfl

theorem cell23_6919143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_6919143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919143 prefixEnd_6919143 := by exact prefixLift 6919143
  have htrace : WordTrace (prefixWord ++ tailWord_6919143) baseStart_6919143 baseEnd_6919143 := by
    simpa [prefixWord, tailWord_6919143, baseEnd_6919143] using wordTrace_append hprefix tailTrace_6919143
  have hstable : (prefixWord ++ tailWord_6919143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919143).length < 2 ^ (prefixWord ++ tailWord_6919143).sum := by decide
  have hdescent : baseEnd_6919143 < baseStart_6919143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919155 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 4]
def baseStart_6919155 : Nat := 118140960795 + 6919155 * 2 ^ 59
def prefixEnd_6919155 : Nat := 4983230072969 + 3 ^ 40 * 6919155 * 2
def baseEnd_6919155 : Nat := 3552852237959981507941891

theorem tailTrace_6919155 : CollatzResearch.WordTrace tailWord_6919155 prefixEnd_6919155 3552852237959981507941891 := by
  unfold tailWord_6919155
  simp only [CollatzResearch.WordTrace]
  refine ⟨252362315248090607439358919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168241543498727071626239279 252362315248090607439358919)
  ·
    refine ⟨378543472872135911159038379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252362315248090607439358919 378543472872135911159038379)
    ·
      refine ⟨567815209308203866738557569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378543472872135911159038379 567815209308203866738557569)
      ·
        refine ⟨425861406981152900053918177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567815209308203866738557569 425861406981152900053918177)
        ·
          refine ⟨319396055235864675040438633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425861406981152900053918177 319396055235864675040438633)
          ·
            refine ⟨239547041426898506280328975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319396055235864675040438633 239547041426898506280328975)
            ·
              refine ⟨359320562140347759420493463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239547041426898506280328975 359320562140347759420493463)
              ·
                refine ⟨538980843210521639130740195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359320562140347759420493463 538980843210521639130740195)
                ·
                  refine ⟨808471264815782458696110293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538980843210521639130740195 808471264815782458696110293)
                  ·
                    refine ⟨18948545269119901375690085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 808471264815782458696110293 18948545269119901375690085)
                    ·
                      refine ⟨3552852237959981507941891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18948545269119901375690085 3552852237959981507941891)
                      ·
                        rfl

theorem cell23_6919155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_6919155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919155 prefixEnd_6919155 := by exact prefixLift 6919155
  have htrace : WordTrace (prefixWord ++ tailWord_6919155) baseStart_6919155 baseEnd_6919155 := by
    simpa [prefixWord, tailWord_6919155, baseEnd_6919155] using wordTrace_append hprefix tailTrace_6919155
  have hstable : (prefixWord ++ tailWord_6919155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919155).length < 2 ^ (prefixWord ++ tailWord_6919155).sum := by decide
  have hdescent : baseEnd_6919155 < baseStart_6919155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919169 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 1, 5]
def baseStart_6919169 : Nat := 118140960795 + 6919169 * 2 ^ 59
def prefixEnd_6919169 : Nat := 4983230072969 + 3 ^ 40 * 6919169 * 2
def baseEnd_6919169 : Nat := 1184286475563048151055609

theorem tailTrace_6919169 : CollatzResearch.WordTrace tailWord_6919169 prefixEnd_6919169 1184286475563048151055609 := by
  unfold tailWord_6919169
  simp only [CollatzResearch.WordTrace]
  refine ⟨252362825870039887830368561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168241883913359925220245707 252362825870039887830368561)
  ·
    refine ⟨189272119402529915872776421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252362825870039887830368561 189272119402529915872776421)
    ·
      refine ⟨35488522387974359226145579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189272119402529915872776421 35488522387974359226145579)
      ·
        refine ⟨53232783581961538839218369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35488522387974359226145579 53232783581961538839218369)
        ·
          refine ⟨39924587686471154129413777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53232783581961538839218369 39924587686471154129413777)
          ·
            refine ⟨29943440764853365597060333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39924587686471154129413777 29943440764853365597060333)
            ·
              refine ⟨11228790286820012098897625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29943440764853365597060333 11228790286820012098897625)
              ·
                refine ⟨8421592715115009074173219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11228790286820012098897625 8421592715115009074173219)
                ·
                  refine ⟨12632389072672513611259829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8421592715115009074173219 12632389072672513611259829)
                  ·
                    refine ⟨1184286475563048151055609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12632389072672513611259829 1184286475563048151055609)
                    ·
                      rfl

theorem cell23_6919169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_6919169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919169 prefixEnd_6919169 := by exact prefixLift 6919169
  have htrace : WordTrace (prefixWord ++ tailWord_6919169) baseStart_6919169 baseEnd_6919169 := by
    simpa [prefixWord, tailWord_6919169, baseEnd_6919169] using wordTrace_append hprefix tailTrace_6919169
  have hstable : (prefixWord ++ tailWord_6919169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919169).length < 2 ^ (prefixWord ++ tailWord_6919169).sum := by decide
  have hdescent : baseEnd_6919169 < baseStart_6919169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919176 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 2, 3, 2]
def baseStart_6919176 : Nat := 118140960795 + 6919176 * 2 ^ 59
def prefixEnd_6919176 : Nat := 4983230072969 + 3 ^ 40 * 6919176 * 2
def baseEnd_6919176 : Nat := 3552863021053725925779295

theorem tailTrace_6919176 : CollatzResearch.WordTrace tailWord_6919176 prefixEnd_6919176 3552863021053725925779295 := by
  unfold tailWord_6919176
  simp only [CollatzResearch.WordTrace]
  refine ⟨126181540590507264012936691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168242054120676352017248921 126181540590507264012936691)
  ·
    refine ⟨189272310885760896019405037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126181540590507264012936691 189272310885760896019405037)
    ·
      refine ⟨70977116582160336007276889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189272310885760896019405037 70977116582160336007276889)
      ·
        refine ⟨53232837436620252005457667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70977116582160336007276889 53232837436620252005457667)
        ·
          refine ⟨79849256154930378008186501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53232837436620252005457667 79849256154930378008186501)
          ·
            refine ⟨14971735529049445876534969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79849256154930378008186501 14971735529049445876534969)
            ·
              refine ⟨11228801646787084407401227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14971735529049445876534969 11228801646787084407401227)
              ·
                refine ⟨16843202470180626611101841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11228801646787084407401227 16843202470180626611101841)
                ·
                  refine ⟨12632401852635469958326381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16843202470180626611101841 12632401852635469958326381)
                  ·
                    refine ⟨4737150694738301234372393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12632401852635469958326381 4737150694738301234372393)
                    ·
                      refine ⟨3552863021053725925779295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4737150694738301234372393 3552863021053725925779295)
                      ·
                        rfl

theorem cell23_6919176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_6919176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919176 prefixEnd_6919176 := by exact prefixLift 6919176
  have htrace : WordTrace (prefixWord ++ tailWord_6919176) baseStart_6919176 baseEnd_6919176 := by
    simpa [prefixWord, tailWord_6919176, baseEnd_6919176] using wordTrace_append hprefix tailTrace_6919176
  have hstable : (prefixWord ++ tailWord_6919176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919176).length < 2 ^ (prefixWord ++ tailWord_6919176).sum := by decide
  have hdescent : baseEnd_6919176 < baseStart_6919176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919182 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_6919182 : Nat := 118140960795 + 6919182 * 2 ^ 59
def prefixEnd_6919182 : Nat := 4983230072969 + 3 ^ 40 * 6919182 * 2
def baseEnd_6919182 : Nat := 1184288700645884300768089

theorem tailTrace_6919182 : CollatzResearch.WordTrace tailWord_6919182 prefixEnd_6919182 1184288700645884300768089 := by
  unfold tailWord_6919182
  simp only [CollatzResearch.WordTrace]
  refine ⟨31545412502374098881323975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168242200012661860700394533 31545412502374098881323975)
  ·
    refine ⟨47318118753561148321985963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31545412502374098881323975 47318118753561148321985963)
    ·
      refine ⟨70977178130341722482978945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47318118753561148321985963 70977178130341722482978945)
      ·
        refine ⟨53232883597756291862234209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70977178130341722482978945 53232883597756291862234209)
        ·
          refine ⟨39924662698317218896675657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53232883597756291862234209 39924662698317218896675657)
          ·
            refine ⟨29943497023737914172506743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39924662698317218896675657 29943497023737914172506743)
            ·
              refine ⟨44915245535606871258760115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29943497023737914172506743 44915245535606871258760115)
              ·
                refine ⟨67372868303410306888140173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44915245535606871258760115 67372868303410306888140173)
                ·
                  refine ⟨25264825613778865083052565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67372868303410306888140173 25264825613778865083052565)
                  ·
                    refine ⟨1184288700645884300768089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25264825613778865083052565 1184288700645884300768089)
                    ·
                      rfl

theorem cell23_6919182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_6919182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919182 prefixEnd_6919182 := by exact prefixLift 6919182
  have htrace : WordTrace (prefixWord ++ tailWord_6919182) baseStart_6919182 baseEnd_6919182 := by
    simpa [prefixWord, tailWord_6919182, baseEnd_6919182] using wordTrace_append hprefix tailTrace_6919182
  have hstable : (prefixWord ++ tailWord_6919182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919182).length < 2 ^ (prefixWord ++ tailWord_6919182).sum := by decide
  have hdescent : baseEnd_6919182 < baseStart_6919182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919199 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 2, 4]
def baseStart_6919199 : Nat := 118140960795 + 6919199 * 2 ^ 59
def prefixEnd_6919199 : Nat := 4983230072969 + 3 ^ 40 * 6919199 * 2
def baseEnd_6919199 : Nat := 1184291610369593111930563

theorem tailTrace_6919199 : CollatzResearch.WordTrace tailWord_6919199 prefixEnd_6919199 1184291610369593111930563 := by
  unfold tailWord_6919199
  simp only [CollatzResearch.WordTrace]
  refine ⟨252363920059931202953960651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168242613373287468635973767 252363920059931202953960651)
  ·
    refine ⟨378545880089896804430940977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252363920059931202953960651 378545880089896804430940977)
    ·
      refine ⟨283909410067422603323205733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378545880089896804430940977 283909410067422603323205733)
      ·
        refine ⟨53233014387641738123101075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283909410067422603323205733 53233014387641738123101075)
        ·
          refine ⟨79849521581462607184651613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53233014387641738123101075 79849521581462607184651613)
          ·
            refine ⟨29943570593048477694244355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79849521581462607184651613 29943570593048477694244355)
            ·
              refine ⟨44915355889572716541366533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29943570593048477694244355 44915355889572716541366533)
              ·
                refine ⟨8421629229294884351506225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44915355889572716541366533 8421629229294884351506225)
                ·
                  refine ⟨6316221921971163263629669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8421629229294884351506225 6316221921971163263629669)
                  ·
                    refine ⟨1184291610369593111930563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6316221921971163263629669 1184291610369593111930563)
                    ·
                      rfl

theorem cell23_6919199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 4].length) (baseStart_6919199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919199 prefixEnd_6919199 := by exact prefixLift 6919199
  have htrace : WordTrace (prefixWord ++ tailWord_6919199) baseStart_6919199 baseEnd_6919199 := by
    simpa [prefixWord, tailWord_6919199, baseEnd_6919199] using wordTrace_append hprefix tailTrace_6919199
  have hstable : (prefixWord ++ tailWord_6919199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919199).length < 2 ^ (prefixWord ++ tailWord_6919199).sum := by decide
  have hdescent : baseEnd_6919199 < baseStart_6919199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919200 : List Nat := [2, 1, 1, 7, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6919200 : Nat := 118140960795 + 6919200 * 2 ^ 59
def prefixEnd_6919200 : Nat := 4983230072969 + 3 ^ 40 * 6919200 * 2
def baseEnd_6919200 : Nat := 3552875344589433831879185

theorem tailTrace_6919200 : CollatzResearch.WordTrace tailWord_6919200 prefixEnd_6919200 3552875344589433831879185 := by
  unfold tailWord_6919200
  simp only [CollatzResearch.WordTrace]
  refine ⟨126181978266463790062373527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168242637688618386749831369 126181978266463790062373527)
  ·
    refine ⟨189272967399695685093560291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126181978266463790062373527 189272967399695685093560291)
    ·
      refine ⟨283909451099543527640340437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189272967399695685093560291 283909451099543527640340437)
      ·
        refine ⟨6654127760145551429070479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 283909451099543527640340437 6654127760145551429070479)
        ·
          refine ⟨9981191640218327143605719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6654127760145551429070479 9981191640218327143605719)
          ·
            refine ⟨14971787460327490715408579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9981191640218327143605719 14971787460327490715408579)
            ·
              refine ⟨22457681190491236073112869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14971787460327490715408579 22457681190491236073112869)
              ·
                refine ⟨4210815223217106763708663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22457681190491236073112869 4210815223217106763708663)
                ·
                  refine ⟨6316222834825660145562995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4210815223217106763708663 6316222834825660145562995)
                  ·
                    refine ⟨9474334252238490218344493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6316222834825660145562995 9474334252238490218344493)
                    ·
                      refine ⟨3552875344589433831879185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9474334252238490218344493 3552875344589433831879185)
                      ·
                        rfl

theorem cell23_6919200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6919200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919200 prefixEnd_6919200 := by exact prefixLift 6919200
  have htrace : WordTrace (prefixWord ++ tailWord_6919200) baseStart_6919200 baseEnd_6919200 := by
    simpa [prefixWord, tailWord_6919200, baseEnd_6919200] using wordTrace_append hprefix tailTrace_6919200
  have hstable : (prefixWord ++ tailWord_6919200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919200).length < 2 ^ (prefixWord ++ tailWord_6919200).sum := by decide
  have hdescent : baseEnd_6919200 < baseStart_6919200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919229 : List Nat := [1, 4, 1, 3, 1, 3, 3, 7]
def baseStart_6919229 : Nat := 118140960795 + 6919229 * 2 ^ 59
def prefixEnd_6919229 : Nat := 4983230072969 + 3 ^ 40 * 6919229 * 2
def baseEnd_6919229 : Nat := 131588527241793119200613

theorem tailTrace_6919229 : CollatzResearch.WordTrace tailWord_6919229 prefixEnd_6919229 131588527241793119200613 := by
  unfold tailWord_6919229
  simp only [CollatzResearch.WordTrace]
  refine ⟨252365014249822518077552741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168243342833215012051701827 252365014249822518077552741)
  ·
    refine ⟨47318440171841722139541139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252365014249822518077552741 47318440171841722139541139)
    ·
      refine ⟨70977660257762583209311709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47318440171841722139541139 70977660257762583209311709)
      ·
        refine ⟨26616622596660968703491891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70977660257762583209311709 26616622596660968703491891)
        ·
          refine ⟨39924933894991453055237837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26616622596660968703491891 39924933894991453055237837)
          ·
            refine ⟨14971850210621794895714189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39924933894991453055237837 14971850210621794895714189)
            ·
              refine ⟨5614443828983173085892821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14971850210621794895714189 5614443828983173085892821)
              ·
                refine ⟨131588527241793119200613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5614443828983173085892821 131588527241793119200613)
                ·
                  rfl

theorem cell23_6919229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 7].length) (baseStart_6919229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919229 prefixEnd_6919229 := by exact prefixLift 6919229
  have htrace : WordTrace (prefixWord ++ tailWord_6919229) baseStart_6919229 baseEnd_6919229 := by
    simpa [prefixWord, tailWord_6919229, baseEnd_6919229] using wordTrace_append hprefix tailTrace_6919229
  have hstable : (prefixWord ++ tailWord_6919229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919229).length < 2 ^ (prefixWord ++ tailWord_6919229).sum := by decide
  have hdescent : baseEnd_6919229 < baseStart_6919229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919239 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_6919239 : Nat := 118140960795 + 6919239 * 2 ^ 59
def prefixEnd_6919239 : Nat := 4983230072969 + 3 ^ 40 * 6919239 * 2
def baseEnd_6919239 : Nat := 3552895370334959179291505

theorem tailTrace_6919239 : CollatzResearch.WordTrace tailWord_6919239 prefixEnd_6919239 3552895370334959179291505 := by
  unfold tailWord_6919239
  simp only [CollatzResearch.WordTrace]
  refine ⟨252365378979786289785416771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168243585986524193190277847 252365378979786289785416771)
  ·
    refine ⟨378548068469679434678125157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252365378979786289785416771 378548068469679434678125157)
    ·
      refine ⟨70977762838064894002148467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 378548068469679434678125157 70977762838064894002148467)
      ·
        refine ⟨106466644257097341003222701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70977762838064894002148467 106466644257097341003222701)
        ·
          refine ⟨39924991596411502876208513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106466644257097341003222701 39924991596411502876208513)
          ·
            refine ⟨29943743697308627157156385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39924991596411502876208513 29943743697308627157156385)
            ·
              refine ⟨22457807772981470367867289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29943743697308627157156385 22457807772981470367867289)
              ·
                refine ⟨16843355829736102775900467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22457807772981470367867289 16843355829736102775900467)
                ·
                  refine ⟨25265033744604154163850701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16843355829736102775900467 25265033744604154163850701)
                  ·
                    refine ⟨9474387654226557811444013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25265033744604154163850701 9474387654226557811444013)
                    ·
                      refine ⟨3552895370334959179291505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9474387654226557811444013 3552895370334959179291505)
                      ·
                        rfl

theorem cell23_6919239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_6919239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919239 prefixEnd_6919239 := by exact prefixLift 6919239
  have htrace : WordTrace (prefixWord ++ tailWord_6919239) baseStart_6919239 baseEnd_6919239 := by
    simpa [prefixWord, tailWord_6919239, baseEnd_6919239] using wordTrace_append hprefix tailTrace_6919239
  have hstable : (prefixWord ++ tailWord_6919239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919239).length < 2 ^ (prefixWord ++ tailWord_6919239).sum := by decide
  have hdescent : baseEnd_6919239 < baseStart_6919239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919273 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 2, 1, 3]
def baseStart_6919273 : Nat := 118140960795 + 6919273 * 2 ^ 59
def prefixEnd_6919273 : Nat := 4983230072969 + 3 ^ 40 * 6919273 * 2
def baseEnd_6919273 : Nat := 3552912828677212046266349

theorem tailTrace_6919273 : CollatzResearch.WordTrace tailWord_6919273 prefixEnd_6919273 3552912828677212046266349 := by
  unfold tailWord_6919273
  simp only [CollatzResearch.WordTrace]
  refine ⟨252366619061663113592154473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168244412707775409061436315 252366619061663113592154473)
  ·
    refine ⟨189274964296247335194115855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252366619061663113592154473 189274964296247335194115855)
    ·
      refine ⟨283912446444371002791173783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189274964296247335194115855 283912446444371002791173783)
      ·
        refine ⟨425868669666556504186760675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283912446444371002791173783 425868669666556504186760675)
        ·
          refine ⟨638803004499834756280141013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425868669666556504186760675 638803004499834756280141013)
          ·
            refine ⟨14971945417964877100315805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 638803004499834756280141013 14971945417964877100315805)
            ·
              refine ⟨5614479531736828912618427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14971945417964877100315805 5614479531736828912618427)
              ·
                refine ⟨8421719297605243368927641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614479531736828912618427 8421719297605243368927641)
                ·
                  refine ⟨6316289473203932526695731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8421719297605243368927641 6316289473203932526695731)
                  ·
                    refine ⟨9474434209805898790043597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6316289473203932526695731 9474434209805898790043597)
                    ·
                      refine ⟨3552912828677212046266349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9474434209805898790043597 3552912828677212046266349)
                      ·
                        rfl

theorem cell23_6919273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 2, 1, 3].length) (baseStart_6919273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919273 prefixEnd_6919273 := by exact prefixLift 6919273
  have htrace : WordTrace (prefixWord ++ tailWord_6919273) baseStart_6919273 baseEnd_6919273 := by
    simpa [prefixWord, tailWord_6919273, baseEnd_6919273] using wordTrace_append hprefix tailTrace_6919273
  have hstable : (prefixWord ++ tailWord_6919273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919273).length < 2 ^ (prefixWord ++ tailWord_6919273).sum := by decide
  have hdescent : baseEnd_6919273 < baseStart_6919273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919296 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 4, 2, 2]
def baseStart_6919296 : Nat := 118140960795 + 6919296 * 2 ^ 59
def prefixEnd_6919296 : Nat := 4983230072969 + 3 ^ 40 * 6919296 * 2
def baseEnd_6919296 : Nat := 3552924638732265456278743

theorem tailTrace_6919296 : CollatzResearch.WordTrace tailWord_6919296 prefixEnd_6919296 3552924638732265456278743 := by
  unfold tailWord_6919296
  simp only [CollatzResearch.WordTrace]
  refine ⟨126183728970289894260120871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168244971960386525680161161 126183728970289894260120871)
  ·
    refine ⟨189275593455434841390181307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126183728970289894260120871 189275593455434841390181307)
    ·
      refine ⟨283913390183152262085271961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189275593455434841390181307 283913390183152262085271961)
      ·
        refine ⟨212935042637364196563953971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283913390183152262085271961 212935042637364196563953971)
        ·
          refine ⟨319402563956046294845930957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212935042637364196563953971 319402563956046294845930957)
          ·
            refine ⟨119775961483517360567224109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319402563956046294845930957 119775961483517360567224109)
            ·
              refine ⟨44915985556319010212709041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119775961483517360567224109 44915985556319010212709041)
              ·
                refine ⟨33686989167239257659531781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44915985556319010212709041 33686989167239257659531781)
                ·
                  refine ⟨6316310468857360811162209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33686989167239257659531781 6316310468857360811162209)
                  ·
                    refine ⟨4737232851643020608371657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6316310468857360811162209 4737232851643020608371657)
                    ·
                      refine ⟨3552924638732265456278743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4737232851643020608371657 3552924638732265456278743)
                      ·
                        rfl

theorem cell23_6919296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4, 2, 2].length) (baseStart_6919296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919296 prefixEnd_6919296 := by exact prefixLift 6919296
  have htrace : WordTrace (prefixWord ++ tailWord_6919296) baseStart_6919296 baseEnd_6919296 := by
    simpa [prefixWord, tailWord_6919296, baseEnd_6919296] using wordTrace_append hprefix tailTrace_6919296
  have hstable : (prefixWord ++ tailWord_6919296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919296).length < 2 ^ (prefixWord ++ tailWord_6919296).sum := by decide
  have hdescent : baseEnd_6919296 < baseStart_6919296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919319 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 7]
def baseStart_6919319 : Nat := 118140960795 + 6919319 * 2 ^ 59
def prefixEnd_6919319 : Nat := 4983230072969 + 3 ^ 40 * 6919319 * 2
def baseEnd_6919319 : Nat := 394770716531924318476793

theorem tailTrace_6919319 : CollatzResearch.WordTrace tailWord_6919319 prefixEnd_6919319 394770716531924318476793 := by
  unfold tailWord_6919319
  simp only [CollatzResearch.WordTrace]
  refine ⟨252368296819496463448329011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168245531212997642298886007 252368296819496463448329011)
  ·
    refine ⟨378552445229244695172493517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252368296819496463448329011 378552445229244695172493517)
    ·
      refine ⟨141957166960966760689685069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378552445229244695172493517 141957166960966760689685069)
      ·
        refine ⟨53233937610362535258631901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141957166960966760689685069 53233937610362535258631901)
        ·
          refine ⟨19962726603885950721986963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53233937610362535258631901 19962726603885950721986963)
          ·
            refine ⟨29944089905828926082980445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19962726603885950721986963 29944089905828926082980445)
            ·
              refine ⟨11229033714685847281117667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29944089905828926082980445 11229033714685847281117667)
              ·
                refine ⟨16843550572028770921676501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11229033714685847281117667 16843550572028770921676501)
                ·
                  refine ⟨394770716531924318476793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16843550572028770921676501 394770716531924318476793)
                  ·
                    rfl

theorem cell23_6919319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 7].length) (baseStart_6919319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919319 prefixEnd_6919319 := by exact prefixLift 6919319
  have htrace : WordTrace (prefixWord ++ tailWord_6919319) baseStart_6919319 baseEnd_6919319 := by
    simpa [prefixWord, tailWord_6919319, baseEnd_6919319] using wordTrace_append hprefix tailTrace_6919319
  have hstable : (prefixWord ++ tailWord_6919319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919319).length < 2 ^ (prefixWord ++ tailWord_6919319).sum := by decide
  have hdescent : baseEnd_6919319 < baseStart_6919319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919329 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_6919329 : Nat := 118140960795 + 6919329 * 2 ^ 59
def prefixEnd_6919329 : Nat := 4983230072969 + 3 ^ 40 * 6919329 * 2
def baseEnd_6919329 : Nat := 3552941583593863827166091

theorem tailTrace_6919329 : CollatzResearch.WordTrace tailWord_6919329 prefixEnd_6919329 3552941583593863827166091 := by
  unfold tailWord_6919329
  simp only [CollatzResearch.WordTrace]
  refine ⟨252368661549460235156193041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168245774366306823437462027 252368661549460235156193041)
  ·
    refine ⟨189276496162095176367144781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252368661549460235156193041 189276496162095176367144781)
    ·
      refine ⟨70978686060785691137679293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189276496162095176367144781 70978686060785691137679293)
      ·
        refine ⟨26617007272794634176629735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70978686060785691137679293 26617007272794634176629735)
        ·
          refine ⟨39925510909191951264944603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26617007272794634176629735 39925510909191951264944603)
          ·
            refine ⟨59888266363787926897416905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39925510909191951264944603 59888266363787926897416905)
            ·
              refine ⟨44916199772840945173062679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59888266363787926897416905 44916199772840945173062679)
              ·
                refine ⟨67374299659261417759594019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44916199772840945173062679 67374299659261417759594019)
                ·
                  refine ⟨101061449488892126639391029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67374299659261417759594019 101061449488892126639391029)
                  ·
                    refine ⟨9474510889583636872442909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101061449488892126639391029 9474510889583636872442909)
                    ·
                      refine ⟨3552941583593863827166091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9474510889583636872442909 3552941583593863827166091)
                      ·
                        rfl

theorem cell23_6919329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_6919329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919329 prefixEnd_6919329 := by exact prefixLift 6919329
  have htrace : WordTrace (prefixWord ++ tailWord_6919329) baseStart_6919329 baseEnd_6919329 := by
    simpa [prefixWord, tailWord_6919329, baseEnd_6919329] using wordTrace_append hprefix tailTrace_6919329
  have hstable : (prefixWord ++ tailWord_6919329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919329).length < 2 ^ (prefixWord ++ tailWord_6919329).sum := by decide
  have hdescent : baseEnd_6919329 < baseStart_6919329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6919487 : List Nat := [1, 1, 2, 2, 4, 3, 3, 2, 1, 1, 3]
def baseStart_6919487 : Nat := 118140960795 + 6919487 * 2 ^ 59
def prefixEnd_6919487 : Nat := 4983230072969 + 3 ^ 40 * 6919487 * 2
def baseEnd_6919487 : Nat := 3553022713537274208990365

theorem tailTrace_6919487 : CollatzResearch.WordTrace tailWord_6919487 prefixEnd_6919487 3553022713537274208990365 := by
  unfold tailWord_6919487
  simp only [CollatzResearch.WordTrace]
  refine ⟨252374424282887828140444715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168249616188591885426963143 252374424282887828140444715)
  ·
    refine ⟨378561636424331742210667073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252374424282887828140444715 378561636424331742210667073)
    ·
      refine ⟨283921227318248806658000305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378561636424331742210667073 283921227318248806658000305)
      ·
        refine ⟨212940920488686604993500229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283921227318248806658000305 212940920488686604993500229)
        ·
          refine ⟨39926422591628738436281293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212940920488686604993500229 39926422591628738436281293)
          ·
            refine ⟨14972408471860776913605485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39926422591628738436281293 14972408471860776913605485)
            ·
              refine ⟨5614653176947791342602057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14972408471860776913605485 5614653176947791342602057)
              ·
                refine ⟨4210989882710843506951543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5614653176947791342602057 4210989882710843506951543)
                ·
                  refine ⟨6316484824066265260427315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4210989882710843506951543 6316484824066265260427315)
                  ·
                    refine ⟨9474727236099397890640973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6316484824066265260427315 9474727236099397890640973)
                    ·
                      refine ⟨3553022713537274208990365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9474727236099397890640973 3553022713537274208990365)
                      ·
                        rfl

theorem cell23_6919487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 1, 1, 3].length) (baseStart_6919487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6919487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6919487 prefixEnd_6919487 := by exact prefixLift 6919487
  have htrace : WordTrace (prefixWord ++ tailWord_6919487) baseStart_6919487 baseEnd_6919487 := by
    simpa [prefixWord, tailWord_6919487, baseEnd_6919487] using wordTrace_append hprefix tailTrace_6919487
  have hstable : (prefixWord ++ tailWord_6919487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6919487).length < 2 ^ (prefixWord ++ tailWord_6919487).sum := by decide
  have hdescent : baseEnd_6919487 < baseStart_6919487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6919487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
