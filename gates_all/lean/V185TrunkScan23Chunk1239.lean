import V185TrunkScan23Chunk1238

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7340483 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 3, 6, 2]
def baseStart_7340483 : Nat := 118140960795 + 7340483 * 2 ^ 59
def prefixEnd_7340483 : Nat := 4983230072969 + 3 ^ 40 * 7340483 * 2
def baseEnd_7340483 : Nat := 3769196015157509060204239

theorem tailTrace_7340483 : CollatzResearch.WordTrace tailWord_7340483 prefixEnd_7340483 3769196015157509060204239 := by
  unfold tailWord_7340483
  simp only [CollatzResearch.WordTrace]
  refine ⟨267729409865691220532962103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178486273243794147021974735 267729409865691220532962103)
  ·
    refine ⟨401594114798536830799443155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267729409865691220532962103 401594114798536830799443155)
    ·
      refine ⟨602391172197805246199164733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401594114798536830799443155 602391172197805246199164733)
      ·
        refine ⟨225896689574176967324686775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 602391172197805246199164733 225896689574176967324686775)
        ·
          refine ⟨338845034361265450987030163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225896689574176967324686775 338845034361265450987030163)
          ·
            refine ⟨508267551541898176480545245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338845034361265450987030163 508267551541898176480545245)
            ·
              refine ⟨190600331828211816180204467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508267551541898176480545245 190600331828211816180204467)
              ·
                refine ⟨285900497742317724270306701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190600331828211816180204467 285900497742317724270306701)
                ·
                  refine ⟨107212686653369146601365013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285900497742317724270306701 107212686653369146601365013)
                  ·
                    refine ⟨5025594686876678746938985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107212686653369146601365013 5025594686876678746938985)
                    ·
                      refine ⟨3769196015157509060204239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025594686876678746938985 3769196015157509060204239)
                      ·
                        rfl

theorem cell23_7340483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 6, 2].length) (baseStart_7340483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340483 prefixEnd_7340483 := by exact prefixLift 7340483
  have htrace : WordTrace (prefixWord ++ tailWord_7340483) baseStart_7340483 baseEnd_7340483 := by
    simpa [prefixWord, tailWord_7340483, baseEnd_7340483] using wordTrace_append hprefix tailTrace_7340483
  have hstable : (prefixWord ++ tailWord_7340483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340483).length < 2 ^ (prefixWord ++ tailWord_7340483).sum := by decide
  have hdescent : baseEnd_7340483 < baseStart_7340483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340557 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7340557 : Nat := 118140960795 + 7340557 * 2 ^ 59
def prefixEnd_7340557 : Nat := 4983230072969 + 3 ^ 40 * 7340557 * 2
def baseEnd_7340557 : Nat := 418803779191771307853211

theorem tailTrace_7340557 : CollatzResearch.WordTrace tailWord_7340557 prefixEnd_7340557 418803779191771307853211 := by
  unfold tailWord_7340557
  simp only [CollatzResearch.WordTrace]
  refine ⟨267732108867423131171155925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178488072578282087447437283 267732108867423131171155925)
  ·
    refine ⟨6274971301580229636823967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 267732108867423131171155925 6274971301580229636823967)
    ·
      refine ⟨9412456952370344455235951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6274971301580229636823967 9412456952370344455235951)
      ·
        refine ⟨14118685428555516682853927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9412456952370344455235951 14118685428555516682853927)
        ·
          refine ⟨21178028142833275024280891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14118685428555516682853927 21178028142833275024280891)
          ·
            refine ⟨31767042214249912536421337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21178028142833275024280891 31767042214249912536421337)
            ·
              refine ⟨23825281660687434402316003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31767042214249912536421337 23825281660687434402316003)
              ·
                refine ⟨35737922491031151603474005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23825281660687434402316003 35737922491031151603474005)
                ·
                  refine ⟨418803779191771307853211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35737922491031151603474005 418803779191771307853211)
                  ·
                    rfl

theorem cell23_7340557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7340557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340557 prefixEnd_7340557 := by exact prefixLift 7340557
  have htrace : WordTrace (prefixWord ++ tailWord_7340557) baseStart_7340557 baseEnd_7340557 := by
    simpa [prefixWord, tailWord_7340557, baseEnd_7340557] using wordTrace_append hprefix tailTrace_7340557
  have hstable : (prefixWord ++ tailWord_7340557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340557).length < 2 ^ (prefixWord ++ tailWord_7340557).sum := by decide
  have hdescent : baseEnd_7340557 < baseStart_7340557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340593 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_7340593 : Nat := 118140960795 + 7340593 * 2 ^ 59
def prefixEnd_7340593 : Nat := 4983230072969 + 3 ^ 40 * 7340593 * 2
def baseEnd_7340593 : Nat := 3769252498029503629828733

theorem tailTrace_7340593 : CollatzResearch.WordTrace tailWord_7340593 prefixEnd_7340593 3769252498029503629828733 := by
  unfold tailWord_7340593
  simp only [CollatzResearch.WordTrace]
  refine ⟨267733421895292709319466433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178488947930195139546310955 267733421895292709319466433)
  ·
    refine ⟨200800066421469531989599825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267733421895292709319466433 200800066421469531989599825)
    ·
      refine ⟨150600049816102148992199869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200800066421469531989599825 150600049816102148992199869)
      ·
        refine ⟨56475018681038305872074951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150600049816102148992199869 56475018681038305872074951)
        ·
          refine ⟨84712528021557458808112427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56475018681038305872074951 84712528021557458808112427)
          ·
            refine ⟨127068792032336188212168641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84712528021557458808112427 127068792032336188212168641)
            ·
              refine ⟨95301594024252141159126481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127068792032336188212168641 95301594024252141159126481)
              ·
                refine ⟨71476195518189105869344861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95301594024252141159126481 71476195518189105869344861)
                ·
                  refine ⟨26803573319320914701004323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71476195518189105869344861 26803573319320914701004323)
                  ·
                    refine ⟨40205359978981372051506485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26803573319320914701004323 40205359978981372051506485)
                    ·
                      refine ⟨3769252498029503629828733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40205359978981372051506485 3769252498029503629828733)
                      ·
                        rfl

theorem cell23_7340593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_7340593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340593 prefixEnd_7340593 := by exact prefixLift 7340593
  have htrace : WordTrace (prefixWord ++ tailWord_7340593) baseStart_7340593 baseEnd_7340593 := by
    simpa [prefixWord, tailWord_7340593, baseEnd_7340593] using wordTrace_append hprefix tailTrace_7340593
  have hstable : (prefixWord ++ tailWord_7340593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340593).length < 2 ^ (prefixWord ++ tailWord_7340593).sum := by decide
  have hdescent : baseEnd_7340593 < baseStart_7340593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340607 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 1, 1, 4]
def baseStart_7340607 : Nat := 118140960795 + 7340607 * 2 ^ 59
def prefixEnd_7340607 : Nat := 4983230072969 + 3 ^ 40 * 7340607 * 2
def baseEnd_7340607 : Nat := 3769259686758666575053669

theorem tailTrace_7340607 : CollatzResearch.WordTrace tailWord_7340607 prefixEnd_7340607 3769259686758666575053669 := by
  unfold tailWord_7340607
  simp only [CollatzResearch.WordTrace]
  refine ⟨267733932517241989710476075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178489288344827993140317383 267733932517241989710476075)
  ·
    refine ⟨401600898775862984565714113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267733932517241989710476075 401600898775862984565714113)
    ·
      refine ⟨301200674081897238424285585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401600898775862984565714113 301200674081897238424285585)
      ·
        refine ⟨225900505561422928818214189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301200674081897238424285585 225900505561422928818214189)
        ·
          refine ⟨84712689585533598306830321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225900505561422928818214189 84712689585533598306830321)
          ·
            refine ⟨63534517189150198730122741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84712689585533598306830321 63534517189150198730122741)
            ·
              refine ⟨5956360986482831130949007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63534517189150198730122741 5956360986482831130949007)
              ·
                refine ⟨8934541479724246696423511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956360986482831130949007 8934541479724246696423511)
                ·
                  refine ⟨13401812219586370044635267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8934541479724246696423511 13401812219586370044635267)
                  ·
                    refine ⟨20102718329379555066952901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13401812219586370044635267 20102718329379555066952901)
                    ·
                      refine ⟨3769259686758666575053669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20102718329379555066952901 3769259686758666575053669)
                      ·
                        rfl

theorem cell23_7340607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 1, 4].length) (baseStart_7340607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340607 prefixEnd_7340607 := by exact prefixLift 7340607
  have htrace : WordTrace (prefixWord ++ tailWord_7340607) baseStart_7340607 baseEnd_7340607 := by
    simpa [prefixWord, tailWord_7340607, baseEnd_7340607] using wordTrace_append hprefix tailTrace_7340607
  have hstable : (prefixWord ++ tailWord_7340607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340607).length < 2 ^ (prefixWord ++ tailWord_7340607).sum := by decide
  have hdescent : baseEnd_7340607 < baseStart_7340607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340612 : List Nat := [2, 3, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_7340612 : Nat := 118140960795 + 7340612 * 2 ^ 59
def prefixEnd_7340612 : Nat := 4983230072969 + 3 ^ 40 * 7340612 * 2
def baseEnd_7340612 : Nat := 1256420751387313018497049

theorem tailTrace_7340612 : CollatzResearch.WordTrace tailWord_7340612 prefixEnd_7340612 1256420751387313018497049 := by
  unfold tailWord_7340612
  simp only [CollatzResearch.WordTrace]
  refine ⟨133867057441111937782204045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178489409921482583709605393 133867057441111937782204045)
  ·
    refine ⟨50200146540416976668326517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133867057441111937782204045 50200146540416976668326517)
    ·
      refine ⟨4706263738164091562655611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50200146540416976668326517 4706263738164091562655611)
      ·
        refine ⟨7059395607246137343983417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4706263738164091562655611 7059395607246137343983417)
        ·
          refine ⟨5294546705434603007987563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7059395607246137343983417 5294546705434603007987563)
          ·
            refine ⟨7941820058151904511981345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294546705434603007987563 7941820058151904511981345)
            ·
              refine ⟨5956365043613928383986009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7941820058151904511981345 5956365043613928383986009)
              ·
                refine ⟨4467273782710446287989507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5956365043613928383986009 4467273782710446287989507)
                ·
                  refine ⟨6700910674065669431984261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467273782710446287989507 6700910674065669431984261)
                  ·
                    refine ⟨1256420751387313018497049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6700910674065669431984261 1256420751387313018497049)
                    ·
                      rfl

theorem cell23_7340612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_7340612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340612 prefixEnd_7340612 := by exact prefixLift 7340612
  have htrace : WordTrace (prefixWord ++ tailWord_7340612) baseStart_7340612 baseEnd_7340612 := by
    simpa [prefixWord, tailWord_7340612, baseEnd_7340612] using wordTrace_append hprefix tailTrace_7340612
  have hstable : (prefixWord ++ tailWord_7340612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340612).length < 2 ^ (prefixWord ++ tailWord_7340612).sum := by decide
  have hdescent : baseEnd_7340612 < baseStart_7340612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340640 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 3]
def baseStart_7340640 : Nat := 118140960795 + 7340640 * 2 ^ 59
def prefixEnd_7340640 : Nat := 4983230072969 + 3 ^ 40 * 7340640 * 2
def baseEnd_7340640 : Nat := 3769276631620264945941017

theorem tailTrace_7340640 : CollatzResearch.WordTrace tailWord_7340640 prefixEnd_7340640 3769276631620264945941017 := by
  unfold tailWord_7340640
  simp only [CollatzResearch.WordTrace]
  refine ⟨133867568063061218173213687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178490090750748290897618249 133867568063061218173213687)
  ·
    refine ⟨200801352094591827259820531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133867568063061218173213687 200801352094591827259820531)
    ·
      refine ⟨301202028141887740889730797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200801352094591827259820531 301202028141887740889730797)
      ·
        refine ⟨112950760553207902833649049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301202028141887740889730797 112950760553207902833649049)
        ·
          refine ⟨84713070414905927125236787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112950760553207902833649049 84713070414905927125236787)
          ·
            refine ⟨127069605622358890687855181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84713070414905927125236787 127069605622358890687855181)
            ·
              refine ⟨47651102108384584007945693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127069605622358890687855181 47651102108384584007945693)
              ·
                refine ⟨17869163290644219002979635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47651102108384584007945693 17869163290644219002979635)
                ·
                  refine ⟨26803744935966328504469453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17869163290644219002979635 26803744935966328504469453)
                  ·
                    refine ⟨10051404350987373189176045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26803744935966328504469453 10051404350987373189176045)
                    ·
                      refine ⟨3769276631620264945941017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10051404350987373189176045 3769276631620264945941017)
                      ·
                        rfl

theorem cell23_7340640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_7340640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340640 prefixEnd_7340640 := by exact prefixLift 7340640
  have htrace : WordTrace (prefixWord ++ tailWord_7340640) baseStart_7340640 baseEnd_7340640 := by
    simpa [prefixWord, tailWord_7340640, baseEnd_7340640] using wordTrace_append hprefix tailTrace_7340640
  have hstable : (prefixWord ++ tailWord_7340640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340640).length < 2 ^ (prefixWord ++ tailWord_7340640).sum := by decide
  have hdescent : baseEnd_7340640 < baseStart_7340640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340643 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 2, 7]
def baseStart_7340643 : Nat := 118140960795 + 7340643 * 2 ^ 59
def prefixEnd_7340643 : Nat := 4983230072969 + 3 ^ 40 * 7340643 * 2
def baseEnd_7340643 : Nat := 1256426057354076144734501

theorem tailTrace_7340643 : CollatzResearch.WordTrace tailWord_7340643 prefixEnd_7340643 1256426057354076144734501 := by
  unfold tailWord_7340643
  simp only [CollatzResearch.WordTrace]
  refine ⟨267735245545111567858786583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178490163696741045239191055 267735245545111567858786583)
  ·
    refine ⟨401602868317667351788179875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267735245545111567858786583 401602868317667351788179875)
    ·
      refine ⟨602404302476501027682269813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401602868317667351788179875 602404302476501027682269813)
      ·
        refine ⟨56475403357171971345212795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 602404302476501027682269813 56475403357171971345212795)
        ·
          refine ⟨84713105035757957017819193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56475403357171971345212795 84713105035757957017819193)
          ·
            refine ⟨63534828776818467763364395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84713105035757957017819193 63534828776818467763364395)
            ·
              refine ⟨95302243165227701645046593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63534828776818467763364395 95302243165227701645046593)
              ·
                refine ⟨71476682373920776233784945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95302243165227701645046593 71476682373920776233784945)
                ·
                  refine ⟨53607511780440582175338709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71476682373920776233784945 53607511780440582175338709)
                  ·
                    refine ⟨1256426057354076144734501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53607511780440582175338709 1256426057354076144734501)
                    ·
                      rfl

theorem cell23_7340643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 7].length) (baseStart_7340643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340643 prefixEnd_7340643 := by exact prefixLift 7340643
  have htrace : WordTrace (prefixWord ++ tailWord_7340643) baseStart_7340643 baseEnd_7340643 := by
    simpa [prefixWord, tailWord_7340643, baseEnd_7340643] using wordTrace_append hprefix tailTrace_7340643
  have hstable : (prefixWord ++ tailWord_7340643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340643).length < 2 ^ (prefixWord ++ tailWord_7340643).sum := by decide
  have hdescent : baseEnd_7340643 < baseStart_7340643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340658 : List Nat := [3, 2, 1, 2, 4, 1, 2, 3, 1, 2, 2]
def baseStart_7340658 : Nat := 118140960795 + 7340658 * 2 ^ 59
def prefixEnd_7340658 : Nat := 4983230072969 + 3 ^ 40 * 7340658 * 2
def baseEnd_7340658 : Nat := 3769285874272045875515935

theorem tailTrace_7340658 : CollatzResearch.WordTrace tailWord_7340658 prefixEnd_7340658 3769285874272045875515935 := by
  unfold tailWord_7340658
  simp only [CollatzResearch.WordTrace]
  refine ⟨66933948160014306355145657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178490528426704816947055085 66933948160014306355145657)
  ·
    refine ⟨50200461120010729766359243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66933948160014306355145657 50200461120010729766359243)
    ·
      refine ⟨75300691680016094649538865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50200461120010729766359243 75300691680016094649538865)
      ·
        refine ⟨56475518760012070987154149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75300691680016094649538865 56475518760012070987154149)
        ·
          refine ⟨10589159767502263310091403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56475518760012070987154149 10589159767502263310091403)
          ·
            refine ⟨15883739651253394965137105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10589159767502263310091403 15883739651253394965137105)
            ·
              refine ⟨11912804738440046223852829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15883739651253394965137105 11912804738440046223852829)
              ·
                refine ⟨4467301776915017333944811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11912804738440046223852829 4467301776915017333944811)
                ·
                  refine ⟨6700952665372526000917217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467301776915017333944811 6700952665372526000917217)
                  ·
                    refine ⟨5025714499029394500687913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6700952665372526000917217 5025714499029394500687913)
                    ·
                      refine ⟨3769285874272045875515935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025714499029394500687913 3769285874272045875515935)
                      ·
                        rfl

theorem cell23_7340658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_7340658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340658 prefixEnd_7340658 := by exact prefixLift 7340658
  have htrace : WordTrace (prefixWord ++ tailWord_7340658) baseStart_7340658 baseEnd_7340658 := by
    simpa [prefixWord, tailWord_7340658, baseEnd_7340658] using wordTrace_append hprefix tailTrace_7340658
  have hstable : (prefixWord ++ tailWord_7340658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340658).length < 2 ^ (prefixWord ++ tailWord_7340658).sum := by decide
  have hdescent : baseEnd_7340658 < baseStart_7340658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340683 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 5]
def baseStart_7340683 : Nat := 118140960795 + 7340683 * 2 ^ 59
def prefixEnd_7340683 : Nat := 4983230072969 + 3 ^ 40 * 7340683 * 2
def baseEnd_7340683 : Nat := 3769298711288408277703319

theorem tailTrace_7340683 : CollatzResearch.WordTrace tailWord_7340683 prefixEnd_7340683 3769298711288408277703319 := by
  unfold tailWord_7340683
  simp only [CollatzResearch.WordTrace]
  refine ⟨267736704464966654690242703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178491136309977769793495135 267736704464966654690242703)
  ·
    refine ⟨401605056697449982035364055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267736704464966654690242703 401605056697449982035364055)
    ·
      refine ⟨602407585046174973053046083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401605056697449982035364055 602407585046174973053046083)
      ·
        refine ⟨903611377569262459579569125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602407585046174973053046083 903611377569262459579569125)
        ·
          refine ⟨169427133294236711171169211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 903611377569262459579569125 169427133294236711171169211)
          ·
            refine ⟨254140699941355066756753817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169427133294236711171169211 254140699941355066756753817)
            ·
              refine ⟨190605524956016300067565363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254140699941355066756753817 190605524956016300067565363)
              ·
                refine ⟨285908287434024450101348045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190605524956016300067565363 285908287434024450101348045)
                ·
                  refine ⟨107215607787759168788005517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285908287434024450101348045 107215607787759168788005517)
                  ·
                    refine ⟨40205852920409688295502069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107215607787759168788005517 40205852920409688295502069)
                    ·
                      refine ⟨3769298711288408277703319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40205852920409688295502069 3769298711288408277703319)
                      ·
                        rfl

theorem cell23_7340683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_7340683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340683 prefixEnd_7340683 := by exact prefixLift 7340683
  have htrace : WordTrace (prefixWord ++ tailWord_7340683) baseStart_7340683 baseEnd_7340683 := by
    simpa [prefixWord, tailWord_7340683, baseEnd_7340683] using wordTrace_append hprefix tailTrace_7340683
  have hstable : (prefixWord ++ tailWord_7340683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340683).length < 2 ^ (prefixWord ++ tailWord_7340683).sum := by decide
  have hdescent : baseEnd_7340683 < baseStart_7340683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340713 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_7340713 : Nat := 118140960795 + 7340713 * 2 ^ 59
def prefixEnd_7340713 : Nat := 4983230072969 + 3 ^ 40 * 7340713 * 2
def baseEnd_7340713 : Nat := 3769314115708043160328181

theorem tailTrace_7340713 : CollatzResearch.WordTrace tailWord_7340713 prefixEnd_7340713 3769314115708043160328181 := by
  unfold tailWord_7340713
  simp only [CollatzResearch.WordTrace]
  refine ⟨267737798654857969813834793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178491865769905313209223195 267737798654857969813834793)
  ·
    refine ⟨200803348991143477360376095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267737798654857969813834793 200803348991143477360376095)
    ·
      refine ⟨301205023486715216040564143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200803348991143477360376095 301205023486715216040564143)
      ·
        refine ⟨451807535230072824060846215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301205023486715216040564143 451807535230072824060846215)
        ·
          refine ⟨677711302845109236091269323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451807535230072824060846215 677711302845109236091269323)
          ·
            refine ⟨1016566954267663854136903985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677711302845109236091269323 1016566954267663854136903985)
            ·
              refine ⟨762425215700747890602677989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016566954267663854136903985 762425215700747890602677989)
              ·
                refine ⟨142954727943890229488002123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 762425215700747890602677989 142954727943890229488002123)
                ·
                  refine ⟨214432091915835344232003185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142954727943890229488002123 214432091915835344232003185)
                  ·
                    refine ⟨160824068936876508174002389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 214432091915835344232003185 160824068936876508174002389)
                    ·
                      refine ⟨3769314115708043160328181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160824068936876508174002389 3769314115708043160328181)
                      ·
                        rfl

theorem cell23_7340713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_7340713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340713 prefixEnd_7340713 := by exact prefixLift 7340713
  have htrace : WordTrace (prefixWord ++ tailWord_7340713) baseStart_7340713 baseEnd_7340713 := by
    simpa [prefixWord, tailWord_7340713, baseEnd_7340713] using wordTrace_append hprefix tailTrace_7340713
  have hstable : (prefixWord ++ tailWord_7340713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340713).length < 2 ^ (prefixWord ++ tailWord_7340713).sum := by decide
  have hdescent : baseEnd_7340713 < baseStart_7340713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340717 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_7340717 : Nat := 118140960795 + 7340717 * 2 ^ 59
def prefixEnd_7340717 : Nat := 4983230072969 + 3 ^ 40 * 7340717 * 2
def baseEnd_7340717 : Nat := 3769316169630661144678163

theorem tailTrace_7340717 : CollatzResearch.WordTrace tailWord_7340717 prefixEnd_7340717 3769316169630661144678163 := by
  unfold tailWord_7340717
  simp only [CollatzResearch.WordTrace]
  refine ⟨267737944546843478496980405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178491963031228985664653603 267737944546843478496980405)
  ·
    refine ⟨25100432301266576109091913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267737944546843478496980405 25100432301266576109091913)
    ·
      refine ⟨18825324225949932081818935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25100432301266576109091913 18825324225949932081818935)
      ·
        refine ⟨28237986338924898122728403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18825324225949932081818935 28237986338924898122728403)
        ·
          refine ⟨42356979508387347184092605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28237986338924898122728403 42356979508387347184092605)
          ·
            refine ⟨15883867315645255194034727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42356979508387347184092605 15883867315645255194034727)
            ·
              refine ⟨23825800973467882791052091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15883867315645255194034727 23825800973467882791052091)
              ·
                refine ⟨35738701460201824186578137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23825800973467882791052091 35738701460201824186578137)
                ·
                  refine ⟨26804026095151368139933603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35738701460201824186578137 26804026095151368139933603)
                  ·
                    refine ⟨40206039142727052209900405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26804026095151368139933603 40206039142727052209900405)
                    ·
                      refine ⟨3769316169630661144678163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40206039142727052209900405 3769316169630661144678163)
                      ·
                        rfl

theorem cell23_7340717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_7340717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340717 prefixEnd_7340717 := by exact prefixLift 7340717
  have htrace : WordTrace (prefixWord ++ tailWord_7340717) baseStart_7340717 baseEnd_7340717 := by
    simpa [prefixWord, tailWord_7340717, baseEnd_7340717] using wordTrace_append hprefix tailTrace_7340717
  have hstable : (prefixWord ++ tailWord_7340717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340717).length < 2 ^ (prefixWord ++ tailWord_7340717).sum := by decide
  have hdescent : baseEnd_7340717 < baseStart_7340717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340742 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_7340742 : Nat := 118140960795 + 7340742 * 2 ^ 59
def prefixEnd_7340742 : Nat := 4983230072969 + 3 ^ 40 * 7340742 * 2
def baseEnd_7340742 : Nat := 3769329006647023546865549

theorem tailTrace_7340742 : CollatzResearch.WordTrace tailWord_7340742 prefixEnd_7340742 3769329006647023546865549 := by
  unfold tailWord_7340742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8366839261617278367707515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178492570914501938511093653 8366839261617278367707515)
  ·
    refine ⟨12550258892425917551561273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8366839261617278367707515 12550258892425917551561273)
    ·
      refine ⟨9412694169319438163670955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12550258892425917551561273 9412694169319438163670955)
      ·
        refine ⟨14119041253979157245506433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9412694169319438163670955 14119041253979157245506433)
        ·
          refine ⟨10589280940484367934129825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14119041253979157245506433 10589280940484367934129825)
          ·
            refine ⟨7941960705363275950597369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10589280940484367934129825 7941960705363275950597369)
            ·
              refine ⟨5956470529022456962948027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7941960705363275950597369 5956470529022456962948027)
              ·
                refine ⟨8934705793533685444422041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956470529022456962948027 8934705793533685444422041)
                ·
                  refine ⟨6701029345150264083316531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8934705793533685444422041 6701029345150264083316531)
                  ·
                    refine ⟨10051544017725396124974797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6701029345150264083316531 10051544017725396124974797)
                    ·
                      refine ⟨3769329006647023546865549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10051544017725396124974797 3769329006647023546865549)
                      ·
                        rfl

theorem cell23_7340742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_7340742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340742 prefixEnd_7340742 := by exact prefixLift 7340742
  have htrace : WordTrace (prefixWord ++ tailWord_7340742) baseStart_7340742 baseEnd_7340742 := by
    simpa [prefixWord, tailWord_7340742, baseEnd_7340742] using wordTrace_append hprefix tailTrace_7340742
  have hstable : (prefixWord ++ tailWord_7340742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340742).length < 2 ^ (prefixWord ++ tailWord_7340742).sum := by decide
  have hdescent : baseEnd_7340742 < baseStart_7340742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340748 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7340748 : Nat := 118140960795 + 7340748 * 2 ^ 59
def prefixEnd_7340748 : Nat := 4983230072969 + 3 ^ 40 * 7340748 * 2
def baseEnd_7340748 : Nat := 3769332087530950523390521

theorem tailTrace_7340748 : CollatzResearch.WordTrace tailWord_7340748 prefixEnd_7340748 3769332087530950523390521 := by
  unfold tailWord_7340748
  simp only [CollatzResearch.WordTrace]
  refine ⟨133869537604865585395679449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178492716806487447194239265 133869537604865585395679449)
  ·
    refine ⟨100402153203649189046759587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133869537604865585395679449 100402153203649189046759587)
    ·
      refine ⟨150603229805473783570139381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100402153203649189046759587 150603229805473783570139381)
      ·
        refine ⟨14119052794263167209700567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150603229805473783570139381 14119052794263167209700567)
        ·
          refine ⟨21178579191394750814550851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14119052794263167209700567 21178579191394750814550851)
          ·
            refine ⟨31767868787092126221826277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21178579191394750814550851 31767868787092126221826277)
            ·
              refine ⟨5956475397579773666592427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31767868787092126221826277 5956475397579773666592427)
              ·
                refine ⟨8934713096369660499888641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956475397579773666592427 8934713096369660499888641)
                ·
                  refine ⟨6701034822277245374916481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8934713096369660499888641 6701034822277245374916481)
                  ·
                    refine ⟨5025776116707934031187361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6701034822277245374916481 5025776116707934031187361)
                    ·
                      refine ⟨3769332087530950523390521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025776116707934031187361 3769332087530950523390521)
                      ·
                        rfl

theorem cell23_7340748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7340748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340748 prefixEnd_7340748 := by exact prefixLift 7340748
  have htrace : WordTrace (prefixWord ++ tailWord_7340748) baseStart_7340748 baseEnd_7340748 := by
    simpa [prefixWord, tailWord_7340748, baseEnd_7340748] using wordTrace_append hprefix tailTrace_7340748
  have hstable : (prefixWord ++ tailWord_7340748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340748).length < 2 ^ (prefixWord ++ tailWord_7340748).sum := by decide
  have hdescent : baseEnd_7340748 < baseStart_7340748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340767 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 2, 5]
def baseStart_7340767 : Nat := 118140960795 + 7340767 * 2 ^ 59
def prefixEnd_7340767 : Nat := 4983230072969 + 3 ^ 40 * 7340767 * 2
def baseEnd_7340767 : Nat := 1256447281221128649684311

theorem tailTrace_7340767 : CollatzResearch.WordTrace tailWord_7340767 prefixEnd_7340767 1256447281221128649684311 := by
  unfold tailWord_7340767
  simp only [CollatzResearch.WordTrace]
  refine ⟨267739768196662337036300555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178493178797774891357533703 267739768196662337036300555)
  ·
    refine ⟨401609652294993505554450833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267739768196662337036300555 401609652294993505554450833)
    ·
      refine ⟨301207239221245129165838125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401609652294993505554450833 301207239221245129165838125)
      ·
        refine ⟨112952714707966923437189297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301207239221245129165838125 112952714707966923437189297)
        ·
          refine ⟨84714536030975192577891973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112952714707966923437189297 84714536030975192577891973)
          ·
            refine ⟨15883975505807848608354745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84714536030975192577891973 15883975505807848608354745)
            ·
              refine ⟨11912981629355886456266059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15883975505807848608354745 11912981629355886456266059)
              ·
                refine ⟨17869472444033829684399089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11912981629355886456266059 17869472444033829684399089)
                ·
                  refine ⟨13402104333025372263299317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17869472444033829684399089 13402104333025372263299317)
                  ·
                    refine ⟨1256447281221128649684311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13402104333025372263299317 1256447281221128649684311)
                    ·
                      rfl

theorem cell23_7340767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 5].length) (baseStart_7340767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340767 prefixEnd_7340767 := by exact prefixLift 7340767
  have htrace : WordTrace (prefixWord ++ tailWord_7340767) baseStart_7340767 baseEnd_7340767 := by
    simpa [prefixWord, tailWord_7340767, baseEnd_7340767] using wordTrace_append hprefix tailTrace_7340767
  have hstable : (prefixWord ++ tailWord_7340767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340767).length < 2 ^ (prefixWord ++ tailWord_7340767).sum := by decide
  have hdescent : baseEnd_7340767 < baseStart_7340767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340787 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 2, 4, 2]
def baseStart_7340787 : Nat := 118140960795 + 7340787 * 2 ^ 59
def prefixEnd_7340787 : Nat := 4983230072969 + 3 ^ 40 * 7340787 * 2
def baseEnd_7340787 : Nat := 3769352113276475870802841

theorem tailTrace_7340787 : CollatzResearch.WordTrace tailWord_7340787 prefixEnd_7340787 3769352113276475870802841 := by
  unfold tailWord_7340787
  simp only [CollatzResearch.WordTrace]
  refine ⟨267740497656589880452028615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178493665104393253634685743 267740497656589880452028615)
  ·
    refine ⟨401610746484884820678042923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267740497656589880452028615 401610746484884820678042923)
    ·
      refine ⟨602416119727327231017064385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401610746484884820678042923 602416119727327231017064385)
      ·
        refine ⟨451812089795495423262798289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602416119727327231017064385 451812089795495423262798289)
        ·
          refine ⟨338859067346621567447098717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451812089795495423262798289 338859067346621567447098717)
          ·
            refine ⟨127072150254983087792662019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338859067346621567447098717 127072150254983087792662019)
            ·
              refine ⟨190608225382474631688993029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127072150254983087792662019 190608225382474631688993029)
              ·
                refine ⟨35739042259213993441686193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190608225382474631688993029 35739042259213993441686193)
                ·
                  refine ⟨26804281694410495081264645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35739042259213993441686193 26804281694410495081264645)
                  ·
                    refine ⟨5025802817701967827737121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26804281694410495081264645 5025802817701967827737121)
                    ·
                      refine ⟨3769352113276475870802841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025802817701967827737121 3769352113276475870802841)
                      ·
                        rfl

theorem cell23_7340787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 4, 2].length) (baseStart_7340787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340787 prefixEnd_7340787 := by exact prefixLift 7340787
  have htrace : WordTrace (prefixWord ++ tailWord_7340787) baseStart_7340787 baseEnd_7340787 := by
    simpa [prefixWord, tailWord_7340787, baseEnd_7340787] using wordTrace_append hprefix tailTrace_7340787
  have hstable : (prefixWord ++ tailWord_7340787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340787).length < 2 ^ (prefixWord ++ tailWord_7340787).sum := by decide
  have hdescent : baseEnd_7340787 < baseStart_7340787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340788 : List Nat := [2, 6, 1, 1, 2, 1, 1, 4, 5]
def baseStart_7340788 : Nat := 118140960795 + 7340788 * 2 ^ 59
def prefixEnd_7340788 : Nat := 4983230072969 + 3 ^ 40 * 7340788 * 2
def baseEnd_7340788 : Nat := 418816958528570040765593

theorem tailTrace_7340788 : CollatzResearch.WordTrace tailWord_7340788 prefixEnd_7340788 418816958528570040765593 := by
  unfold tailWord_7340788
  simp only [CollatzResearch.WordTrace]
  refine ⟨133870267064793128811407509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178493689419724171748543345 133870267064793128811407509)
  ·
    refine ⟨6275168768662177913034727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133870267064793128811407509 6275168768662177913034727)
    ·
      refine ⟨9412753152993266869552091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6275168768662177913034727 9412753152993266869552091)
      ·
        refine ⟨14119129729489900304328137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9412753152993266869552091 14119129729489900304328137)
        ·
          refine ⟨10589347297117425228246103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14119129729489900304328137 10589347297117425228246103)
          ·
            refine ⟨15884020945676137842369155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10589347297117425228246103 15884020945676137842369155)
            ·
              refine ⟨23826031418514206763553733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15884020945676137842369155 23826031418514206763553733)
              ·
                refine ⟨4467380890971413768166325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23826031418514206763553733 4467380890971413768166325)
                ·
                  refine ⟨418816958528570040765593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4467380890971413768166325 418816958528570040765593)
                  ·
                    rfl

theorem cell23_7340788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_7340788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340788 prefixEnd_7340788 := by exact prefixLift 7340788
  have htrace : WordTrace (prefixWord ++ tailWord_7340788) baseStart_7340788 baseEnd_7340788 := by
    simpa [prefixWord, tailWord_7340788, baseEnd_7340788] using wordTrace_append hprefix tailTrace_7340788
  have hstable : (prefixWord ++ tailWord_7340788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340788).length < 2 ^ (prefixWord ++ tailWord_7340788).sum := by decide
  have hdescent : baseEnd_7340788 < baseStart_7340788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340797 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_7340797 : Nat := 118140960795 + 7340797 * 2 ^ 59
def prefixEnd_7340797 : Nat := 4983230072969 + 3 ^ 40 * 7340797 * 2
def baseEnd_7340797 : Nat := 1256452416027673610559265

theorem tailTrace_7340797 : CollatzResearch.WordTrace tailWord_7340797 prefixEnd_7340797 1256452416027673610559265 := by
  unfold tailWord_7340797
  simp only [CollatzResearch.WordTrace]
  refine ⟨267740862386553652159892645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178493908257702434773261763 267740862386553652159892645)
  ·
    refine ⟨50201411697478809779979871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267740862386553652159892645 50201411697478809779979871)
    ·
      refine ⟨75302117546218214669969807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50201411697478809779979871 75302117546218214669969807)
      ·
        refine ⟨112953176319327322004954711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75302117546218214669969807 112953176319327322004954711)
        ·
          refine ⟨169429764478990983007432067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112953176319327322004954711 169429764478990983007432067)
          ·
            refine ⟨254144646718486474511148101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169429764478990983007432067 254144646718486474511148101)
            ·
              refine ⟨47652121259716213970840269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254144646718486474511148101 47652121259716213970840269)
              ·
                refine ⟨17869545472393580239065101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47652121259716213970840269 17869545472393580239065101)
                ·
                  refine ⟨6701079552147592589649413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17869545472393580239065101 6701079552147592589649413)
                  ·
                    refine ⟨1256452416027673610559265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6701079552147592589649413 1256452416027673610559265)
                    ·
                      rfl

theorem cell23_7340797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_7340797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340797 prefixEnd_7340797 := by exact prefixLift 7340797
  have htrace : WordTrace (prefixWord ++ tailWord_7340797) baseStart_7340797 baseEnd_7340797 := by
    simpa [prefixWord, tailWord_7340797, baseEnd_7340797] using wordTrace_append hprefix tailTrace_7340797
  have hstable : (prefixWord ++ tailWord_7340797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340797).length < 2 ^ (prefixWord ++ tailWord_7340797).sum := by decide
  have hdescent : baseEnd_7340797 < baseStart_7340797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340804 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_7340804 : Nat := 118140960795 + 7340804 * 2 ^ 59
def prefixEnd_7340804 : Nat := 4983230072969 + 3 ^ 40 * 7340804 * 2
def baseEnd_7340804 : Nat := 3769360842447602304290263

theorem tailTrace_7340804 : CollatzResearch.WordTrace tailWord_7340804 prefixEnd_7340804 3769360842447602304290263 := by
  unfold tailWord_7340804
  simp only [CollatzResearch.WordTrace]
  refine ⟨133870558848764146177698733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178494078465018861570264977 133870558848764146177698733)
  ·
    refine ⟨50201459568286554816637025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133870558848764146177698733 50201459568286554816637025)
    ·
      refine ⟨37651094676214916112477769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50201459568286554816637025 37651094676214916112477769)
      ·
        refine ⟨28238321007161187084358327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37651094676214916112477769 28238321007161187084358327)
        ·
          refine ⟨42357481510741780626537491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28238321007161187084358327 42357481510741780626537491)
          ·
            refine ⟨63536222266112670939806237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42357481510741780626537491 63536222266112670939806237)
            ·
              refine ⟨23826083349792251602427339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63536222266112670939806237 23826083349792251602427339)
              ·
                refine ⟨35739125024688377403641009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23826083349792251602427339 35739125024688377403641009)
                ·
                  refine ⟨26804343768516283052730757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35739125024688377403641009 26804343768516283052730757)
                  ·
                    refine ⟨5025814456596803072387017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26804343768516283052730757 5025814456596803072387017)
                    ·
                      refine ⟨3769360842447602304290263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025814456596803072387017 3769360842447602304290263)
                      ·
                        rfl

theorem cell23_7340804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_7340804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340804 prefixEnd_7340804 := by exact prefixLift 7340804
  have htrace : WordTrace (prefixWord ++ tailWord_7340804) baseStart_7340804 baseEnd_7340804 := by
    simpa [prefixWord, tailWord_7340804, baseEnd_7340804] using wordTrace_append hprefix tailTrace_7340804
  have hstable : (prefixWord ++ tailWord_7340804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340804).length < 2 ^ (prefixWord ++ tailWord_7340804).sum := by decide
  have hdescent : baseEnd_7340804 < baseStart_7340804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340818 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_7340818 : Nat := 118140960795 + 7340818 * 2 ^ 59
def prefixEnd_7340818 : Nat := 4983230072969 + 3 ^ 40 * 7340818 * 2
def baseEnd_7340818 : Nat := 1256456010392255083171733

theorem tailTrace_7340818 : CollatzResearch.WordTrace tailWord_7340818 prefixEnd_7340818 1256456010392255083171733 := by
  unfold tailWord_7340818
  simp only [CollatzResearch.WordTrace]
  refine ⟨66935407079869393186601777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178494418879651715164271405 66935407079869393186601777)
  ·
    refine ⟨50201555309902044889951333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66935407079869393186601777 50201555309902044889951333)
    ·
      refine ⟨9412791620606633416865875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50201555309902044889951333 9412791620606633416865875)
      ·
        refine ⟨14119187430909950125298813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9412791620606633416865875 14119187430909950125298813)
        ·
          refine ⟨5294695286591231296987055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14119187430909950125298813 5294695286591231296987055)
          ·
            refine ⟨7942042929886846945480583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294695286591231296987055 7942042929886846945480583)
            ·
              refine ⟨11913064394830270418220875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942042929886846945480583 11913064394830270418220875)
              ·
                refine ⟨17869596592245405627331313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11913064394830270418220875 17869596592245405627331313)
                ·
                  refine ⟨13402197444184054220498485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17869596592245405627331313 13402197444184054220498485)
                  ·
                    refine ⟨1256456010392255083171733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13402197444184054220498485 1256456010392255083171733)
                    ·
                      rfl

theorem cell23_7340818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_7340818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340818 prefixEnd_7340818 := by exact prefixLift 7340818
  have htrace : WordTrace (prefixWord ++ tailWord_7340818) baseStart_7340818 baseEnd_7340818 := by
    simpa [prefixWord, tailWord_7340818, baseEnd_7340818] using wordTrace_append hprefix tailTrace_7340818
  have hstable : (prefixWord ++ tailWord_7340818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340818).length < 2 ^ (prefixWord ++ tailWord_7340818).sum := by decide
  have hdescent : baseEnd_7340818 < baseStart_7340818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340831 : List Nat := [1, 1, 2, 4, 2, 3, 2, 3, 1, 4]
def baseStart_7340831 : Nat := 118140960795 + 7340831 * 2 ^ 59
def prefixEnd_7340831 : Nat := 4983230072969 + 3 ^ 40 * 7340831 * 2
def baseEnd_7340831 : Nat := 1256458235475091232884213

theorem tailTrace_7340831 : CollatzResearch.WordTrace tailWord_7340831 prefixEnd_7340831 1256458235475091232884213 := by
  unfold tailWord_7340831
  simp only [CollatzResearch.WordTrace]
  refine ⟨267742102468430475966630347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178494734978953650644420231 267742102468430475966630347)
  ·
    refine ⟨401613153702645713949945521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267742102468430475966630347 401613153702645713949945521)
    ·
      refine ⟨301209865276984285462459141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401613153702645713949945521 301209865276984285462459141)
      ·
        refine ⟨56476849739434553524211089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301209865276984285462459141 56476849739434553524211089)
        ·
          refine ⟨42357637304575915143158317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56476849739434553524211089 42357637304575915143158317)
          ·
            refine ⟨15884113989215968178684369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42357637304575915143158317 15884113989215968178684369)
            ·
              refine ⟨11913085491911976134013277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15884113989215968178684369 11913085491911976134013277)
              ·
                refine ⟨4467407059466991050254979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11913085491911976134013277 4467407059466991050254979)
                ·
                  refine ⟨6701110589200486575382469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467407059466991050254979 6701110589200486575382469)
                  ·
                    refine ⟨1256458235475091232884213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6701110589200486575382469 1256458235475091232884213)
                    ·
                      rfl

theorem cell23_7340831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 1, 4].length) (baseStart_7340831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340831 prefixEnd_7340831 := by exact prefixLift 7340831
  have htrace : WordTrace (prefixWord ++ tailWord_7340831) baseStart_7340831 baseEnd_7340831 := by
    simpa [prefixWord, tailWord_7340831, baseEnd_7340831] using wordTrace_append hprefix tailTrace_7340831
  have hstable : (prefixWord ++ tailWord_7340831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340831).length < 2 ^ (prefixWord ++ tailWord_7340831).sum := by decide
  have hdescent : baseEnd_7340831 < baseStart_7340831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340847 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 5, 5, 2]
def baseStart_7340847 : Nat := 118140960795 + 7340847 * 2 ^ 59
def prefixEnd_7340847 : Nat := 4983230072969 + 3 ^ 40 * 7340847 * 2
def baseEnd_7340847 : Nat := 3769382922115745636052565

theorem tailTrace_7340847 : CollatzResearch.WordTrace tailWord_7340847 prefixEnd_7340847 3769382922115745636052565 := by
  unfold tailWord_7340847
  simp only [CollatzResearch.WordTrace]
  refine ⟨267742686036372510699212795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178495124024248340466141863 267742686036372510699212795)
  ·
    refine ⟨401614029054558766048819193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267742686036372510699212795 401614029054558766048819193)
    ·
      refine ⟨301210521790919074536614395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401614029054558766048819193 301210521790919074536614395)
      ·
        refine ⟨451815782686378611804921593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301210521790919074536614395 451815782686378611804921593)
        ·
          refine ⟨338861837014783958853691195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451815782686378611804921593 338861837014783958853691195)
          ·
            refine ⟨508292755522175938280536793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338861837014783958853691195 508292755522175938280536793)
            ·
              refine ⟨381219566641631953710402595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508292755522175938280536793 381219566641631953710402595)
              ·
                refine ⟨571829349962447930565603893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381219566641631953710402595 571829349962447930565603893)
                ·
                  refine ⟨53609001558979493490525365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 571829349962447930565603893 53609001558979493490525365)
                  ·
                    refine ⟨5025843896154327514736753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53609001558979493490525365 5025843896154327514736753)
                    ·
                      refine ⟨3769382922115745636052565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025843896154327514736753 3769382922115745636052565)
                      ·
                        rfl

theorem cell23_7340847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 5, 2].length) (baseStart_7340847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340847 prefixEnd_7340847 := by exact prefixLift 7340847
  have htrace : WordTrace (prefixWord ++ tailWord_7340847) baseStart_7340847 baseEnd_7340847 := by
    simpa [prefixWord, tailWord_7340847, baseEnd_7340847] using wordTrace_append hprefix tailTrace_7340847
  have hstable : (prefixWord ++ tailWord_7340847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340847).length < 2 ^ (prefixWord ++ tailWord_7340847).sum := by decide
  have hdescent : baseEnd_7340847 < baseStart_7340847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340861 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 6]
def baseStart_7340861 : Nat := 118140960795 + 7340861 * 2 ^ 59
def prefixEnd_7340861 : Nat := 4983230072969 + 3 ^ 40 * 7340861 * 2
def baseEnd_7340861 : Nat := 418821123427212064586389

theorem tailTrace_7340861 : CollatzResearch.WordTrace tailWord_7340861 prefixEnd_7340861 418821123427212064586389 := by
  unfold tailWord_7340861
  simp only [CollatzResearch.WordTrace]
  refine ⟨267743196658321791090222437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178495464438881194060148291 267743196658321791090222437)
  ·
    refine ⟨50201849373435335829416707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267743196658321791090222437 50201849373435335829416707)
    ·
      refine ⟨75302774060153003744125061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50201849373435335829416707 75302774060153003744125061)
      ·
        refine ⟨14119270136278688202023449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75302774060153003744125061 14119270136278688202023449)
        ·
          refine ⟨10589452602209016151517587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14119270136278688202023449 10589452602209016151517587)
          ·
            refine ⟨15884178903313524227276381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10589452602209016151517587 15884178903313524227276381)
            ·
              refine ⟨5956567088742571585228643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15884178903313524227276381 5956567088742571585228643)
              ·
                refine ⟨8934850633113857377842965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956567088742571585228643 8934850633113857377842965)
                ·
                  refine ⟨418821123427212064586389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8934850633113857377842965 418821123427212064586389)
                  ·
                    rfl

theorem cell23_7340861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_7340861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340861 prefixEnd_7340861 := by exact prefixLift 7340861
  have htrace : WordTrace (prefixWord ++ tailWord_7340861) baseStart_7340861 baseEnd_7340861 := by
    simpa [prefixWord, tailWord_7340861, baseEnd_7340861] using wordTrace_append hprefix tailTrace_7340861
  have hstable : (prefixWord ++ tailWord_7340861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340861).length < 2 ^ (prefixWord ++ tailWord_7340861).sum := by decide
  have hdescent : baseEnd_7340861 < baseStart_7340861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340898 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_7340898 : Nat := 118140960795 + 7340898 * 2 ^ 59
def prefixEnd_7340898 : Nat := 4983230072969 + 3 ^ 40 * 7340898 * 2
def baseEnd_7340898 : Nat := 3769409109629124936514831

theorem tailTrace_7340898 : CollatzResearch.WordTrace tailWord_7340898 prefixEnd_7340898 3769409109629124936514831 := by
  unfold tailWord_7340898
  simp only [CollatzResearch.WordTrace]
  refine ⟨66936136539796936602329837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178496364106125164272879565 66936136539796936602329837)
  ·
    refine ⟨25101051202423851225873689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66936136539796936602329837 25101051202423851225873689)
    ·
      refine ⟨18825788401817888419405267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25101051202423851225873689 18825788401817888419405267)
      ·
        refine ⟨28238682602726832629107901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18825788401817888419405267 28238682602726832629107901)
        ·
          refine ⟨10589505976022562235915463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28238682602726832629107901 10589505976022562235915463)
          ·
            refine ⟨15884258964033843353873195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10589505976022562235915463 15884258964033843353873195)
            ·
              refine ⟨23826388446050765030809793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15884258964033843353873195 23826388446050765030809793)
              ·
                refine ⟨17869791334538073773107345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23826388446050765030809793 17869791334538073773107345)
                ·
                  refine ⟨13402343500903555329830509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17869791334538073773107345 13402343500903555329830509)
                  ·
                    refine ⟨5025878812838833248686441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13402343500903555329830509 5025878812838833248686441)
                    ·
                      refine ⟨3769409109629124936514831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025878812838833248686441 3769409109629124936514831)
                      ·
                        rfl

theorem cell23_7340898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_7340898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340898 prefixEnd_7340898 := by exact prefixLift 7340898
  have htrace : WordTrace (prefixWord ++ tailWord_7340898) baseStart_7340898 baseEnd_7340898 := by
    simpa [prefixWord, tailWord_7340898, baseEnd_7340898] using wordTrace_append hprefix tailTrace_7340898
  have hstable : (prefixWord ++ tailWord_7340898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340898).length < 2 ^ (prefixWord ++ tailWord_7340898).sum := by decide
  have hdescent : baseEnd_7340898 < baseStart_7340898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340904 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 4, 4]
def baseStart_7340904 : Nat := 118140960795 + 7340904 * 2 ^ 59
def prefixEnd_7340904 : Nat := 4983230072969 + 3 ^ 40 * 7340904 * 2
def baseEnd_7340904 : Nat := 1256470730171017304346601

theorem tailTrace_7340904 : CollatzResearch.WordTrace tailWord_7340904 prefixEnd_7340904 1256470730171017304346601 := by
  unfold tailWord_7340904
  simp only [CollatzResearch.WordTrace]
  refine ⟨133872382498583004717018883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178496509998110672956025177 133872382498583004717018883)
  ·
    refine ⟨200808573747874507075528325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133872382498583004717018883 200808573747874507075528325)
    ·
      refine ⟨37651607577726470076661561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200808573747874507075528325 37651607577726470076661561)
      ·
        refine ⟨28238705683294852557496171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37651607577726470076661561 28238705683294852557496171)
        ·
          refine ⟨42358058524942278836244257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28238705683294852557496171 42358058524942278836244257)
          ·
            refine ⟨31768543893706709127183193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42358058524942278836244257 31768543893706709127183193)
            ·
              refine ⟨23826407920280031845387395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31768543893706709127183193 23826407920280031845387395)
              ·
                refine ⟨35739611880420047768081093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23826407920280031845387395 35739611880420047768081093)
                ·
                  refine ⟨6701177227578758956515205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35739611880420047768081093 6701177227578758956515205)
                  ·
                    refine ⟨1256470730171017304346601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6701177227578758956515205 1256470730171017304346601)
                    ·
                      rfl

theorem cell23_7340904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_7340904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340904 prefixEnd_7340904 := by exact prefixLift 7340904
  have htrace : WordTrace (prefixWord ++ tailWord_7340904) baseStart_7340904 baseEnd_7340904 := by
    simpa [prefixWord, tailWord_7340904, baseEnd_7340904] using wordTrace_append hprefix tailTrace_7340904
  have hstable : (prefixWord ++ tailWord_7340904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340904).length < 2 ^ (prefixWord ++ tailWord_7340904).sum := by decide
  have hdescent : baseEnd_7340904 < baseStart_7340904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340917 : List Nat := [1, 3, 4, 1, 1, 2, 1, 10]
def baseStart_7340917 : Nat := 118140960795 + 7340917 * 2 ^ 59
def prefixEnd_7340917 : Nat := 4983230072969 + 3 ^ 40 * 7340917 * 2
def baseEnd_7340917 : Nat := 139608106139317050451009

theorem tailTrace_7340917 : CollatzResearch.WordTrace tailWord_7340917 prefixEnd_7340917 139608106139317050451009 := by
  unfold tailWord_7340917
  simp only [CollatzResearch.WordTrace]
  refine ⟨267745239146118912654261005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178496826097412608436174003 267745239146118912654261005)
  ·
    refine ⟨100404464679794592245347877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267745239146118912654261005 100404464679794592245347877)
    ·
      refine ⟨18825837127461486046002727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100404464679794592245347877 18825837127461486046002727)
      ·
        refine ⟨28238755691192229069004091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18825837127461486046002727 28238755691192229069004091)
        ·
          refine ⟨42358133536788343603506137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28238755691192229069004091 42358133536788343603506137)
          ·
            refine ⟨31768600152591257702629603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42358133536788343603506137 31768600152591257702629603)
            ·
              refine ⟨47652900228886886553944405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31768600152591257702629603 47652900228886886553944405)
              ·
                refine ⟨139608106139317050451009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47652900228886886553944405 139608106139317050451009)
                ·
                  rfl

theorem cell23_7340917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 10].length) (baseStart_7340917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340917 prefixEnd_7340917 := by exact prefixLift 7340917
  have htrace : WordTrace (prefixWord ++ tailWord_7340917) baseStart_7340917 baseEnd_7340917 := by
    simpa [prefixWord, tailWord_7340917, baseEnd_7340917] using wordTrace_append hprefix tailTrace_7340917
  have hstable : (prefixWord ++ tailWord_7340917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340917).length < 2 ^ (prefixWord ++ tailWord_7340917).sum := by decide
  have hdescent : baseEnd_7340917 < baseStart_7340917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340921 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 2, 4]
def baseStart_7340921 : Nat := 118140960795 + 7340921 * 2 ^ 59
def prefixEnd_7340921 : Nat := 4983230072969 + 3 ^ 40 * 7340921 * 2
def baseEnd_7340921 : Nat := 1256473639894726115509075

theorem tailTrace_7340921 : CollatzResearch.WordTrace tailWord_7340921 prefixEnd_7340921 1256473639894726115509075 := by
  unfold tailWord_7340921
  simp only [CollatzResearch.WordTrace]
  refine ⟨267745385038104421337406617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178496923358736280891604411 267745385038104421337406617)
  ·
    refine ⟨200809038778578316003054963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267745385038104421337406617 200809038778578316003054963)
    ·
      refine ⟨301213558167867474004582445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200809038778578316003054963 301213558167867474004582445)
      ·
        refine ⟨112955084312950302751718417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301213558167867474004582445 112955084312950302751718417)
        ·
          refine ⟨84716313234712727063788813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112955084312950302751718417 84716313234712727063788813)
          ·
            refine ⟨31768617463017272648920805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84716313234712727063788813 31768617463017272648920805)
            ·
              refine ⟨5956615774315738621672651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31768617463017272648920805 5956615774315738621672651)
              ·
                refine ⟨8934923661473607932508977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956615774315738621672651 8934923661473607932508977)
                ·
                  refine ⟨6701192746105205949381733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8934923661473607932508977 6701192746105205949381733)
                  ·
                    refine ⟨1256473639894726115509075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6701192746105205949381733 1256473639894726115509075)
                    ·
                      rfl

theorem cell23_7340921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 2, 4].length) (baseStart_7340921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340921 prefixEnd_7340921 := by exact prefixLift 7340921
  have htrace : WordTrace (prefixWord ++ tailWord_7340921) baseStart_7340921 baseEnd_7340921 := by
    simpa [prefixWord, tailWord_7340921, baseEnd_7340921] using wordTrace_append hprefix tailTrace_7340921
  have hstable : (prefixWord ++ tailWord_7340921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340921).length < 2 ^ (prefixWord ++ tailWord_7340921).sum := by decide
  have hdescent : baseEnd_7340921 < baseStart_7340921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340948 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_7340948 : Nat := 118140960795 + 7340948 * 2 ^ 59
def prefixEnd_7340948 : Nat := 4983230072969 + 3 ^ 40 * 7340948 * 2
def baseEnd_7340948 : Nat := 3769434783661849740889601

theorem tailTrace_7340948 : CollatzResearch.WordTrace tailWord_7340948 prefixEnd_7340948 3769434783661849740889601 := by
  unfold tailWord_7340948
  simp only [CollatzResearch.WordTrace]
  refine ⟨133873184904503302474319749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178497579872671069965759665 133873184904503302474319749)
  ·
    refine ⟨25101222169594369213934953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133873184904503302474319749 25101222169594369213934953)
    ·
      refine ⟨18825916627195776910451215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25101222169594369213934953 18825916627195776910451215)
      ·
        refine ⟨28238874940793665365676823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18825916627195776910451215 28238874940793665365676823)
        ·
          refine ⟨42358312411190498048515235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28238874940793665365676823 42358312411190498048515235)
          ·
            refine ⟨63537468616785747072772853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42358312411190498048515235 63537468616785747072772853)
            ·
              refine ⟨5956637682823663788072455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63537468616785747072772853 5956637682823663788072455)
              ·
                refine ⟨8934956524235495682108683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956637682823663788072455 8934956524235495682108683)
                ·
                  refine ⟨13402434786353243523163025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8934956524235495682108683 13402434786353243523163025)
                  ·
                    refine ⟨10051826089764932642372269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13402434786353243523163025 10051826089764932642372269)
                    ·
                      refine ⟨3769434783661849740889601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10051826089764932642372269 3769434783661849740889601)
                      ·
                        rfl

theorem cell23_7340948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_7340948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340948 prefixEnd_7340948 := by exact prefixLift 7340948
  have htrace : WordTrace (prefixWord ++ tailWord_7340948) baseStart_7340948 baseEnd_7340948 := by
    simpa [prefixWord, tailWord_7340948, baseEnd_7340948] using wordTrace_append hprefix tailTrace_7340948
  have hstable : (prefixWord ++ tailWord_7340948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340948).length < 2 ^ (prefixWord ++ tailWord_7340948).sum := by decide
  have hdescent : baseEnd_7340948 < baseStart_7340948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340962 : List Nat := [3, 3, 1, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_7340962 : Nat := 118140960795 + 7340962 * 2 ^ 59
def prefixEnd_7340962 : Nat := 4983230072969 + 3 ^ 40 * 7340962 * 2
def baseEnd_7340962 : Nat := 3769441972391012686114537

theorem tailTrace_7340962 : CollatzResearch.WordTrace tailWord_7340962 prefixEnd_7340962 3769441972391012686114537 := by
  unfold tailWord_7340962
  simp only [CollatzResearch.WordTrace]
  refine ⟨66936720107738971334912285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178497920287303923559766093 66936720107738971334912285)
  ·
    refine ⟨25101270040402114250592107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66936720107738971334912285 25101270040402114250592107)
    ·
      refine ⟨37651905060603171375888161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25101270040402114250592107 37651905060603171375888161)
      ·
        refine ⟨28238928795452378531916121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37651905060603171375888161 28238928795452378531916121)
        ·
          refine ⟨21179196596589283898937091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28238928795452378531916121 21179196596589283898937091)
          ·
            refine ⟨31768794894883925848405637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21179196596589283898937091 31768794894883925848405637)
            ·
              refine ⟨5956649042790736096576057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31768794894883925848405637 5956649042790736096576057)
              ·
                refine ⟨4467486782093052072432043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5956649042790736096576057 4467486782093052072432043)
                ·
                  refine ⟨6701230173139578108648065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467486782093052072432043 6701230173139578108648065)
                  ·
                    refine ⟨5025922629854683581486049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6701230173139578108648065 5025922629854683581486049)
                    ·
                      refine ⟨3769441972391012686114537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025922629854683581486049 3769441972391012686114537)
                      ·
                        rfl

theorem cell23_7340962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_7340962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340962 prefixEnd_7340962 := by exact prefixLift 7340962
  have htrace : WordTrace (prefixWord ++ tailWord_7340962) baseStart_7340962 baseEnd_7340962 := by
    simpa [prefixWord, tailWord_7340962, baseEnd_7340962] using wordTrace_append hprefix tailTrace_7340962
  have hstable : (prefixWord ++ tailWord_7340962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340962).length < 2 ^ (prefixWord ++ tailWord_7340962).sum := by decide
  have hdescent : baseEnd_7340962 < baseStart_7340962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340987 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 3]
def baseStart_7340987 : Nat := 118140960795 + 7340987 * 2 ^ 59
def prefixEnd_7340987 : Nat := 4983230072969 + 3 ^ 40 * 7340987 * 2
def baseEnd_7340987 : Nat := 3769454809407375088301921

theorem tailTrace_7340987 : CollatzResearch.WordTrace tailWord_7340987 prefixEnd_7340987 3769454809407375088301921 := by
  unfold tailWord_7340987
  simp only [CollatzResearch.WordTrace]
  refine ⟨267747792255865314609309215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178498528170576876406206143 267747792255865314609309215)
  ·
    refine ⟨401621688383797971913963823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267747792255865314609309215 401621688383797971913963823)
    ·
      refine ⟨602432532575696957870945735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401621688383797971913963823 602432532575696957870945735)
      ·
        refine ⟨903648798863545436806418603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602432532575696957870945735 903648798863545436806418603)
        ·
          refine ⟨1355473198295318155209627905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903648798863545436806418603 1355473198295318155209627905)
          ·
            refine ⟨1016604898721488616407220929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355473198295318155209627905 1016604898721488616407220929)
            ·
              refine ⟨762453674041116462305415697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016604898721488616407220929 762453674041116462305415697)
              ·
                refine ⟨571840255530837346729061773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762453674041116462305415697 571840255530837346729061773)
                ·
                  refine ⟨214440095824064005023398165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571840255530837346729061773 214440095824064005023398165)
                  ·
                    refine ⟨10051879491753000235471789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214440095824064005023398165 10051879491753000235471789)
                    ·
                      refine ⟨3769454809407375088301921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10051879491753000235471789 3769454809407375088301921)
                      ·
                        rfl

theorem cell23_7340987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 3].length) (baseStart_7340987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340987 prefixEnd_7340987 := by exact prefixLift 7340987
  have htrace : WordTrace (prefixWord ++ tailWord_7340987) baseStart_7340987 baseEnd_7340987 := by
    simpa [prefixWord, tailWord_7340987, baseEnd_7340987] using wordTrace_append hprefix tailTrace_7340987
  have hstable : (prefixWord ++ tailWord_7340987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340987).length < 2 ^ (prefixWord ++ tailWord_7340987).sum := by decide
  have hdescent : baseEnd_7340987 < baseStart_7340987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341018 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2]
def baseStart_7341018 : Nat := 118140960795 + 7341018 * 2 ^ 59
def prefixEnd_7341018 : Nat := 4983230072969 + 3 ^ 40 * 7341018 * 2
def baseEnd_7341018 : Nat := 3769470727307664467014279

theorem tailTrace_7341018 : CollatzResearch.WordTrace tailWord_7341018 prefixEnd_7341018 3769470727307664467014279 := by
  unfold tailWord_7341018
  simp only [CollatzResearch.WordTrace]
  refine ⟨66937230729688251725921927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178499281945835337935791805 66937230729688251725921927)
  ·
    refine ⟨100405846094532377588882891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66937230729688251725921927 100405846094532377588882891)
    ·
      refine ⟨150608769141798566383324337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100405846094532377588882891 150608769141798566383324337)
      ·
        refine ⟨112956576856348924787493253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150608769141798566383324337 112956576856348924787493253)
        ·
          refine ⟨21179358160565423397654985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112956576856348924787493253 21179358160565423397654985)
          ·
            refine ⟨15884518620424067548241239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21179358160565423397654985 15884518620424067548241239)
            ·
              refine ⟨23826777930636101322361859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15884518620424067548241239 23826777930636101322361859)
              ·
                refine ⟨35740166895954151983542789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23826777930636101322361859 35740166895954151983542789)
                ·
                  refine ⟨6701281292991403496914273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35740166895954151983542789 6701281292991403496914273)
                  ·
                    refine ⟨5025960969743552622685705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6701281292991403496914273 5025960969743552622685705)
                    ·
                      refine ⟨3769470727307664467014279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025960969743552622685705 3769470727307664467014279)
                      ·
                        rfl

theorem cell23_7341018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_7341018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341018 prefixEnd_7341018 := by exact prefixLift 7341018
  have htrace : WordTrace (prefixWord ++ tailWord_7341018) baseStart_7341018 baseEnd_7341018 := by
    simpa [prefixWord, tailWord_7341018, baseEnd_7341018] using wordTrace_append hprefix tailTrace_7341018
  have hstable : (prefixWord ++ tailWord_7341018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341018).length < 2 ^ (prefixWord ++ tailWord_7341018).sum := by decide
  have hdescent : baseEnd_7341018 < baseStart_7341018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341108 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_7341108 : Nat := 118140960795 + 7341108 * 2 ^ 59
def prefixEnd_7341108 : Nat := 4983230072969 + 3 ^ 40 * 7341108 * 2
def baseEnd_7341108 : Nat := 3769516940566569114888865

theorem tailTrace_7341108 : CollatzResearch.WordTrace tailWord_7341108 prefixEnd_7341108 3769516940566569114888865 := by
  unfold tailWord_7341108
  simp only [CollatzResearch.WordTrace]
  refine ⟨133876102744213476137231989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178501470325617968182975985 133876102744213476137231989)
  ·
    refine ⟨12550884632270013387865499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133876102744213476137231989 12550884632270013387865499)
    ·
      refine ⟨18826326948405020081798249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12550884632270013387865499 18826326948405020081798249)
      ·
        refine ⟨14119745211303765061348687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18826326948405020081798249 14119745211303765061348687)
        ·
          refine ⟨21179617816955647592023031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14119745211303765061348687 21179617816955647592023031)
          ·
            refine ⟨31769426725433471388034547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21179617816955647592023031 31769426725433471388034547)
            ·
              refine ⟨47654140088150207082051821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31769426725433471388034547 47654140088150207082051821)
              ·
                refine ⟨17870302533056327655769433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47654140088150207082051821 17870302533056327655769433)
                ·
                  refine ⟨13402726899792245741827075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17870302533056327655769433 13402726899792245741827075)
                  ·
                    refine ⟨20104090349688368612740613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13402726899792245741827075 20104090349688368612740613)
                    ·
                      refine ⟨3769516940566569114888865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20104090349688368612740613 3769516940566569114888865)
                      ·
                        rfl

theorem cell23_7341108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_7341108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341108 prefixEnd_7341108 := by exact prefixLift 7341108
  have htrace : WordTrace (prefixWord ++ tailWord_7341108) baseStart_7341108 baseEnd_7341108 := by
    simpa [prefixWord, tailWord_7341108, baseEnd_7341108] using wordTrace_append hprefix tailTrace_7341108
  have hstable : (prefixWord ++ tailWord_7341108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341108).length < 2 ^ (prefixWord ++ tailWord_7341108).sum := by decide
  have hdescent : baseEnd_7341108 < baseStart_7341108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341134 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_7341134 : Nat := 118140960795 + 7341134 * 2 ^ 59
def prefixEnd_7341134 : Nat := 4983230072969 + 3 ^ 40 * 7341134 * 2
def baseEnd_7341134 : Nat := 3769530291063586013163745

theorem tailTrace_7341134 : CollatzResearch.WordTrace tailWord_7341134 prefixEnd_7341134 3769530291063586013163745 := by
  unfold tailWord_7341134
  simp only [CollatzResearch.WordTrace]
  refine ⟨33469144223291594839363807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178502102524221839143273637 33469144223291594839363807)
  ·
    refine ⟨50203716334937392259045711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33469144223291594839363807 50203716334937392259045711)
    ·
      refine ⟨75305574502406088388568567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50203716334937392259045711 75305574502406088388568567)
      ·
        refine ⟨112958361753609132582852851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75305574502406088388568567 112958361753609132582852851)
        ·
          refine ⟨169437542630413698874279277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112958361753609132582852851 169437542630413698874279277)
          ·
            refine ⟨63539078486405137077854729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169437542630413698874279277 63539078486405137077854729)
            ·
              refine ⟨47654308864803852808391047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63539078486405137077854729 47654308864803852808391047)
              ·
                refine ⟨71481463297205779212586571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47654308864803852808391047 71481463297205779212586571)
                ·
                  refine ⟨107222194945808668818879857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71481463297205779212586571 107222194945808668818879857)
                  ·
                    refine ⟨80416646209356501614159893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107222194945808668818879857 80416646209356501614159893)
                    ·
                      refine ⟨3769530291063586013163745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80416646209356501614159893 3769530291063586013163745)
                      ·
                        rfl

theorem cell23_7341134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_7341134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341134 prefixEnd_7341134 := by exact prefixLift 7341134
  have htrace : WordTrace (prefixWord ++ tailWord_7341134) baseStart_7341134 baseEnd_7341134 := by
    simpa [prefixWord, tailWord_7341134, baseEnd_7341134] using wordTrace_append hprefix tailTrace_7341134
  have hstable : (prefixWord ++ tailWord_7341134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341134).length < 2 ^ (prefixWord ++ tailWord_7341134).sum := by decide
  have hdescent : baseEnd_7341134 < baseStart_7341134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341142 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_7341142 : Nat := 118140960795 + 7341142 * 2 ^ 59
def prefixEnd_7341142 : Nat := 4983230072969 + 3 ^ 40 * 7341142 * 2
def baseEnd_7341142 : Nat := 3769534398908821981863709

theorem tailTrace_7341142 : CollatzResearch.WordTrace tailWord_7341142 prefixEnd_7341142 3769534398908821981863709 := by
  unfold tailWord_7341142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16734590348143986005075105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178502297046869184054134453 16734590348143986005075105)
  ·
    refine ⟨12550942761107989503806329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16734590348143986005075105 12550942761107989503806329)
    ·
      refine ⟨9413207070830992127854747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12550942761107989503806329 9413207070830992127854747)
      ·
        refine ⟨14119810606246488191782121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9413207070830992127854747 14119810606246488191782121)
        ·
          refine ⟨10589857954684866143836591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14119810606246488191782121 10589857954684866143836591)
          ·
            refine ⟨15884786932027299215754887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10589857954684866143836591 15884786932027299215754887)
            ·
              refine ⟨23827180398040948823632331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15884786932027299215754887 23827180398040948823632331)
              ·
                refine ⟨35740770597061423235448497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23827180398040948823632331 35740770597061423235448497)
                ·
                  refine ⟨26805577947796067426586373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35740770597061423235448497 26805577947796067426586373)
                  ·
                    refine ⟨5026045865211762642484945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26805577947796067426586373 5026045865211762642484945)
                    ·
                      refine ⟨3769534398908821981863709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026045865211762642484945 3769534398908821981863709)
                      ·
                        rfl

theorem cell23_7341142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_7341142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341142 prefixEnd_7341142 := by exact prefixLift 7341142
  have htrace : WordTrace (prefixWord ++ tailWord_7341142) baseStart_7341142 baseEnd_7341142 := by
    simpa [prefixWord, tailWord_7341142, baseEnd_7341142] using wordTrace_append hprefix tailTrace_7341142
  have hstable : (prefixWord ++ tailWord_7341142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341142).length < 2 ^ (prefixWord ++ tailWord_7341142).sum := by decide
  have hdescent : baseEnd_7341142 < baseStart_7341142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341144 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 5, 5]
def baseStart_7341144 : Nat := 118140960795 + 7341144 * 2 ^ 59
def prefixEnd_7341144 : Nat := 4983230072969 + 3 ^ 40 * 7341144 * 2
def baseEnd_7341144 : Nat := 1256511808623376991346233

theorem tailTrace_7341144 : CollatzResearch.WordTrace tailWord_7341144 prefixEnd_7341144 1256511808623376991346233 := by
  unfold tailWord_7341144
  simp only [CollatzResearch.WordTrace]
  refine ⟨133876759258148265211387243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178502345677531020281849657 133876759258148265211387243)
  ·
    refine ⟨200815138887222397817080865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133876759258148265211387243 200815138887222397817080865)
    ·
      refine ⟨150611354165416798362810649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200815138887222397817080865 150611354165416798362810649)
      ·
        refine ⟨112958515624062598772107987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150611354165416798362810649 112958515624062598772107987)
        ·
          refine ⟨169437773436093898158161981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112958515624062598772107987 169437773436093898158161981)
          ·
            refine ⟨63539165038535211809310743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169437773436093898158161981 63539165038535211809310743)
            ·
              refine ⟨95308747557802817713966115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63539165038535211809310743 95308747557802817713966115)
              ·
                refine ⟨142963121336704226570949173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95308747557802817713966115 142963121336704226570949173)
                ·
                  refine ⟨13402792625316021241026485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142963121336704226570949173 13402792625316021241026485)
                  ·
                    refine ⟨1256511808623376991346233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13402792625316021241026485 1256511808623376991346233)
                    ·
                      rfl

theorem cell23_7341144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_7341144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341144 prefixEnd_7341144 := by exact prefixLift 7341144
  have htrace : WordTrace (prefixWord ++ tailWord_7341144) baseStart_7341144 baseEnd_7341144 := by
    simpa [prefixWord, tailWord_7341144, baseEnd_7341144] using wordTrace_append hprefix tailTrace_7341144
  have hstable : (prefixWord ++ tailWord_7341144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341144).length < 2 ^ (prefixWord ++ tailWord_7341144).sum := by decide
  have hdescent : baseEnd_7341144 < baseStart_7341144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341151 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 1, 5, 2]
def baseStart_7341151 : Nat := 118140960795 + 7341151 * 2 ^ 59
def prefixEnd_7341151 : Nat := 4983230072969 + 3 ^ 40 * 7341151 * 2
def baseEnd_7341151 : Nat := 3769539020234712446651167

theorem tailTrace_7341151 : CollatzResearch.WordTrace tailWord_7341151 prefixEnd_7341151 3769539020234712446651167 := by
  unfold tailWord_7341151
  simp only [CollatzResearch.WordTrace]
  refine ⟨267753773827271170618279307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178502515884847447078852871 267753773827271170618279307)
  ·
    refine ⟨401630660740906755927418961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267753773827271170618279307 401630660740906755927418961)
    ·
      refine ⟨301222995555680066945564221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401630660740906755927418961 301222995555680066945564221)
      ·
        refine ⟨112958623333380025104586583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301222995555680066945564221 112958623333380025104586583)
        ·
          refine ⟨169437935000070037656879875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112958623333380025104586583 169437935000070037656879875)
          ·
            refine ⟨254156902500105056485319813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169437935000070037656879875 254156902500105056485319813)
            ·
              refine ⟨47654419218769698090997465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254156902500105056485319813 47654419218769698090997465)
              ·
                refine ⟨35740814414077273568248099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47654419218769698090997465 35740814414077273568248099)
                ·
                  refine ⟨53611221621115910352372149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35740814414077273568248099 53611221621115910352372149)
                  ·
                    refine ⟨5026052026979616595534889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53611221621115910352372149 5026052026979616595534889)
                    ·
                      refine ⟨3769539020234712446651167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026052026979616595534889 3769539020234712446651167)
                      ·
                        rfl

theorem cell23_7341151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_7341151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341151 prefixEnd_7341151 := by exact prefixLift 7341151
  have htrace : WordTrace (prefixWord ++ tailWord_7341151) baseStart_7341151 baseEnd_7341151 := by
    simpa [prefixWord, tailWord_7341151, baseEnd_7341151] using wordTrace_append hprefix tailTrace_7341151
  have hstable : (prefixWord ++ tailWord_7341151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341151).length < 2 ^ (prefixWord ++ tailWord_7341151).sum := by decide
  have hdescent : baseEnd_7341151 < baseStart_7341151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341175 : List Nat := [1, 1, 3, 1, 1, 4, 4, 3, 1, 1, 3]
def baseStart_7341175 : Nat := 118140960795 + 7341175 * 2 ^ 59
def prefixEnd_7341175 : Nat := 4983230072969 + 3 ^ 40 * 7341175 * 2
def baseEnd_7341175 : Nat := 3769551343770420352751057

theorem tailTrace_7341175 : CollatzResearch.WordTrace tailWord_7341175 prefixEnd_7341175 3769551343770420352751057 := by
  unfold tailWord_7341175
  simp only [CollatzResearch.WordTrace]
  refine ⟨267754649179184222717152979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178503099452789481811435319 267754649179184222717152979)
  ·
    refine ⟨401631973768776334075729469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267754649179184222717152979 401631973768776334075729469)
    ·
      refine ⟨150611990163291125278398551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401631973768776334075729469 150611990163291125278398551)
      ·
        refine ⟨225917985244936687917597827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150611990163291125278398551 225917985244936687917597827)
        ·
          refine ⟨338876977867405031876396741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225917985244936687917597827 338876977867405031876396741)
          ·
            refine ⟨63539433350138443476824389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338876977867405031876396741 63539433350138443476824389)
            ·
              refine ⟨11913643753150958151904573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63539433350138443476824389 11913643753150958151904573)
              ·
                refine ⟨4467616407431609306964215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11913643753150958151904573 4467616407431609306964215)
                ·
                  refine ⟨6701424611147413960446323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467616407431609306964215 6701424611147413960446323)
                  ·
                    refine ⟨10052136916721120940669485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6701424611147413960446323 10052136916721120940669485)
                    ·
                      refine ⟨3769551343770420352751057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10052136916721120940669485 3769551343770420352751057)
                      ·
                        rfl

theorem cell23_7341175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 1, 1, 3].length) (baseStart_7341175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341175 prefixEnd_7341175 := by exact prefixLift 7341175
  have htrace : WordTrace (prefixWord ++ tailWord_7341175) baseStart_7341175 baseEnd_7341175 := by
    simpa [prefixWord, tailWord_7341175, baseEnd_7341175] using wordTrace_append hprefix tailTrace_7341175
  have hstable : (prefixWord ++ tailWord_7341175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341175).length < 2 ^ (prefixWord ++ tailWord_7341175).sum := by decide
  have hdescent : baseEnd_7341175 < baseStart_7341175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341208 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 1, 6]
def baseStart_7341208 : Nat := 118140960795 + 7341208 * 2 ^ 59
def prefixEnd_7341208 : Nat := 4983230072969 + 3 ^ 40 * 7341208 * 2
def baseEnd_7341208 : Nat := 1256522762877339574546135

theorem tailTrace_7341208 : CollatzResearch.WordTrace tailWord_7341208 prefixEnd_7341208 1256522762877339574546135 := by
  unfold tailWord_7341208
  simp only [CollatzResearch.WordTrace]
  refine ⟨133877926394032334676552139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178503901858709779568736185 133877926394032334676552139)
  ·
    refine ⟨200816889591048502014828209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133877926394032334676552139 200816889591048502014828209)
    ·
      refine ⟨150612667193286376511121157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200816889591048502014828209 150612667193286376511121157)
      ·
        refine ⟨28239875098741195595835217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150612667193286376511121157 28239875098741195595835217)
        ·
          refine ⟨21179906324055896696876413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28239875098741195595835217 21179906324055896696876413)
          ·
            refine ⟨7942464871520961261328655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21179906324055896696876413 7942464871520961261328655)
            ·
              refine ⟨11913697307281441891992983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942464871520961261328655 11913697307281441891992983)
              ·
                refine ⟨17870545960922162837989475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11913697307281441891992983 17870545960922162837989475)
                ·
                  refine ⟨26805818941383244256984213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17870545960922162837989475 26805818941383244256984213)
                  ·
                    refine ⟨1256522762877339574546135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26805818941383244256984213 1256522762877339574546135)
                    ·
                      rfl

theorem cell23_7341208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_7341208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341208 prefixEnd_7341208 := by exact prefixLift 7341208
  have htrace : WordTrace (prefixWord ++ tailWord_7341208) baseStart_7341208 baseEnd_7341208 := by
    simpa [prefixWord, tailWord_7341208, baseEnd_7341208] using wordTrace_append hprefix tailTrace_7341208
  have hstable : (prefixWord ++ tailWord_7341208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341208).length < 2 ^ (prefixWord ++ tailWord_7341208).sum := by decide
  have hdescent : baseEnd_7341208 < baseStart_7341208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341215 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 4]
def baseStart_7341215 : Nat := 118140960795 + 7341215 * 2 ^ 59
def prefixEnd_7341215 : Nat := 4983230072969 + 3 ^ 40 * 7341215 * 2
def baseEnd_7341215 : Nat := 3769571882996600196250873

theorem tailTrace_7341215 : CollatzResearch.WordTrace tailWord_7341215 prefixEnd_7341215 3769571882996600196250873 := by
  unfold tailWord_7341215
  simp only [CollatzResearch.WordTrace]
  refine ⟨267756108099039309548609099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178504072066026206365739399 267756108099039309548609099)
  ·
    refine ⟨401634162148558964322913649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267756108099039309548609099 401634162148558964322913649)
    ·
      refine ⟨301225621611419223242185237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401634162148558964322913649 301225621611419223242185237)
      ·
        refine ⟨14119951013035276089477433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 301225621611419223242185237 14119951013035276089477433)
        ·
          refine ⟨10589963259776457067108075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14119951013035276089477433 10589963259776457067108075)
          ·
            refine ⟨15884944889664685600662113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10589963259776457067108075 15884944889664685600662113)
            ·
              refine ⟨11913708667248514200496585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15884944889664685600662113 11913708667248514200496585)
              ·
                refine ⟨8935281500436385650372439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11913708667248514200496585 8935281500436385650372439)
                ·
                  refine ⟨13402922250654578475558659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8935281500436385650372439 13402922250654578475558659)
                  ·
                    refine ⟨20104383375981867713337989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13402922250654578475558659 20104383375981867713337989)
                    ·
                      refine ⟨3769571882996600196250873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20104383375981867713337989 3769571882996600196250873)
                      ·
                        rfl

theorem cell23_7341215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_7341215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341215 prefixEnd_7341215 := by exact prefixLift 7341215
  have htrace : WordTrace (prefixWord ++ tailWord_7341215) baseStart_7341215 baseEnd_7341215 := by
    simpa [prefixWord, tailWord_7341215, baseEnd_7341215] using wordTrace_append hprefix tailTrace_7341215
  have hstable : (prefixWord ++ tailWord_7341215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341215).length < 2 ^ (prefixWord ++ tailWord_7341215).sum := by decide
  have hdescent : baseEnd_7341215 < baseStart_7341215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341221 : List Nat := [1, 3, 1, 2, 1, 4, 4, 7]
def baseStart_7341221 : Nat := 118140960795 + 7341221 * 2 ^ 59
def prefixEnd_7341221 : Nat := 4983230072969 + 3 ^ 40 * 7341221 * 2
def baseEnd_7341221 : Nat := 139613887551130636028735

theorem tailTrace_7341221 : CollatzResearch.WordTrace tailWord_7341221 prefixEnd_7341221 139613887551130636028735 := by
  unfold tailWord_7341221
  simp only [CollatzResearch.WordTrace]
  refine ⟨267756326937017572573327517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178504217958011715048885011 267756326937017572573327517)
  ·
    refine ⟨100408622601381589714997819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267756326937017572573327517 100408622601381589714997819)
    ·
      refine ⟨150612933902072384572496729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100408622601381589714997819 150612933902072384572496729)
      ·
        refine ⟨112959700426554288429372547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150612933902072384572496729 112959700426554288429372547)
        ·
          refine ⟨169439550639831432644058821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112959700426554288429372547 169439550639831432644058821)
          ·
            refine ⟨31769915744968393620761029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169439550639831432644058821 31769915744968393620761029)
            ·
              refine ⟨5956859202181573803892693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31769915744968393620761029 5956859202181573803892693)
              ·
                refine ⟨139613887551130636028735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5956859202181573803892693 139613887551130636028735)
                ·
                  rfl

theorem cell23_7341221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 7].length) (baseStart_7341221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341221 prefixEnd_7341221 := by exact prefixLift 7341221
  have htrace : WordTrace (prefixWord ++ tailWord_7341221) baseStart_7341221 baseEnd_7341221 := by
    simpa [prefixWord, tailWord_7341221, baseEnd_7341221] using wordTrace_append hprefix tailTrace_7341221
  have hstable : (prefixWord ++ tailWord_7341221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341221).length < 2 ^ (prefixWord ++ tailWord_7341221).sum := by decide
  have hdescent : baseEnd_7341221 < baseStart_7341221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341231 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 3]
def baseStart_7341231 : Nat := 118140960795 + 7341231 * 2 ^ 59
def prefixEnd_7341231 : Nat := 4983230072969 + 3 ^ 40 * 7341231 * 2
def baseEnd_7341231 : Nat := 3769580098687072133650799

theorem tailTrace_7341231 : CollatzResearch.WordTrace tailWord_7341231 prefixEnd_7341231 3769580098687072133650799 := by
  unfold tailWord_7341231
  simp only [CollatzResearch.WordTrace]
  refine ⟨267756691666981344281191547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178504461111320896187461031 267756691666981344281191547)
  ·
    refine ⟨401635037500472016421787321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267756691666981344281191547 401635037500472016421787321)
    ·
      refine ⟨301226278125354012316340491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401635037500472016421787321 301226278125354012316340491)
      ·
        refine ⟨451839417188031018474510737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301226278125354012316340491 451839417188031018474510737)
        ·
          refine ⟨338879562891023263855883053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451839417188031018474510737 338879562891023263855883053)
          ·
            refine ⟨127079836084133723945956145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338879562891023263855883053 127079836084133723945956145)
            ·
              refine ⟨95309877063100292959467109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127079836084133723945956145 95309877063100292959467109)
              ·
                refine ⟨17870601949331304929900083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95309877063100292959467109 17870601949331304929900083)
                ·
                  refine ⟨26805902923996957394850125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17870601949331304929900083 26805902923996957394850125)
                  ·
                    refine ⟨10052213596498859023068797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26805902923996957394850125 10052213596498859023068797)
                    ·
                      refine ⟨3769580098687072133650799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10052213596498859023068797 3769580098687072133650799)
                      ·
                        rfl

theorem cell23_7341231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 3].length) (baseStart_7341231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341231 prefixEnd_7341231 := by exact prefixLift 7341231
  have htrace : WordTrace (prefixWord ++ tailWord_7341231) baseStart_7341231 baseEnd_7341231 := by
    simpa [prefixWord, tailWord_7341231, baseEnd_7341231] using wordTrace_append hprefix tailTrace_7341231
  have hstable : (prefixWord ++ tailWord_7341231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341231).length < 2 ^ (prefixWord ++ tailWord_7341231).sum := by decide
  have hdescent : baseEnd_7341231 < baseStart_7341231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341249 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7341249 : Nat := 118140960795 + 7341249 * 2 ^ 59
def prefixEnd_7341249 : Nat := 4983230072969 + 3 ^ 40 * 7341249 * 2
def baseEnd_7341249 : Nat := 3769589341338853063225717

theorem tailTrace_7341249 : CollatzResearch.WordTrace tailWord_7341249 prefixEnd_7341249 3769589341338853063225717 := by
  unfold tailWord_7341249
  simp only [CollatzResearch.WordTrace]
  refine ⟨267757348180916133355346801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178504898787277422236897867 267757348180916133355346801)
  ·
    refine ⟨200818011135687100016510101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267757348180916133355346801 200818011135687100016510101)
    ·
      refine ⟨9413344271985332813273911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 200818011135687100016510101 9413344271985332813273911)
      ·
        refine ⟨14120016407977999219910867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9413344271985332813273911 14120016407977999219910867)
        ·
          refine ⟨21180024611966998829866301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14120016407977999219910867 21180024611966998829866301)
          ·
            refine ⟨7942509229487624561199863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21180024611966998829866301 7942509229487624561199863)
            ·
              refine ⟨11913763844231436841799795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942509229487624561199863 11913763844231436841799795)
              ·
                refine ⟨17870645766347155262699693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11913763844231436841799795 17870645766347155262699693)
                ·
                  refine ⟨6701492162380183223512385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17870645766347155262699693 6701492162380183223512385)
                  ·
                    refine ⟨5026119121785137417634289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6701492162380183223512385 5026119121785137417634289)
                    ·
                      refine ⟨3769589341338853063225717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026119121785137417634289 3769589341338853063225717)
                      ·
                        rfl

theorem cell23_7341249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7341249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341249 prefixEnd_7341249 := by exact prefixLift 7341249
  have htrace : WordTrace (prefixWord ++ tailWord_7341249) baseStart_7341249 baseEnd_7341249 := by
    simpa [prefixWord, tailWord_7341249, baseEnd_7341249] using wordTrace_append hprefix tailTrace_7341249
  have hstable : (prefixWord ++ tailWord_7341249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341249).length < 2 ^ (prefixWord ++ tailWord_7341249).sum := by decide
  have hdescent : baseEnd_7341249 < baseStart_7341249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341291 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 5]
def baseStart_7341291 : Nat := 118140960795 + 7341291 * 2 ^ 59
def prefixEnd_7341291 : Nat := 4983230072969 + 3 ^ 40 * 7341291 * 2
def baseEnd_7341291 : Nat := 3769610907526341898900523

theorem tailTrace_7341291 : CollatzResearch.WordTrace tailWord_7341291 prefixEnd_7341291 3769610907526341898900523 := by
  unfold tailWord_7341291
  simp only [CollatzResearch.WordTrace]
  refine ⟨267758880046763974528375727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178505920031175983018917151 267758880046763974528375727)
  ·
    refine ⟨401638320070145961792563591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267758880046763974528375727 401638320070145961792563591)
    ·
      refine ⟨602457480105218942688845387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401638320070145961792563591 602457480105218942688845387)
      ·
        refine ⟨903686220157828414033268081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602457480105218942688845387 903686220157828414033268081)
        ·
          refine ⟨677764665118371310524951061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903686220157828414033268081 677764665118371310524951061)
          ·
            refine ⟨31770218677423655180857081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 677764665118371310524951061 31770218677423655180857081)
            ·
              refine ⟨23827664008067741385642811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31770218677423655180857081 23827664008067741385642811)
              ·
                refine ⟨35741496012101612078464217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23827664008067741385642811 35741496012101612078464217)
                ·
                  refine ⟨26806122009076209058848163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35741496012101612078464217 26806122009076209058848163)
                  ·
                    refine ⟨40209183013614313588272245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26806122009076209058848163 40209183013614313588272245)
                    ·
                      refine ⟨3769610907526341898900523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40209183013614313588272245 3769610907526341898900523)
                      ·
                        rfl

theorem cell23_7341291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 5].length) (baseStart_7341291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341291 prefixEnd_7341291 := by exact prefixLift 7341291
  have htrace : WordTrace (prefixWord ++ tailWord_7341291) baseStart_7341291 baseEnd_7341291 := by
    simpa [prefixWord, tailWord_7341291, baseEnd_7341291] using wordTrace_append hprefix tailTrace_7341291
  have hstable : (prefixWord ++ tailWord_7341291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341291).length < 2 ^ (prefixWord ++ tailWord_7341291).sum := by decide
  have hdescent : baseEnd_7341291 < baseStart_7341291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341292 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 1, 3, 2]
def baseStart_7341292 : Nat := 118140960795 + 7341292 * 2 ^ 59
def prefixEnd_7341292 : Nat := 4983230072969 + 3 ^ 40 * 7341292 * 2
def baseEnd_7341292 : Nat := 3769611421006996394988019

theorem tailTrace_7341292 : CollatzResearch.WordTrace tailWord_7341292 prefixEnd_7341292 3769611421006996394988019 := by
  unfold tailWord_7341292
  simp only [CollatzResearch.WordTrace]
  refine ⟨133879458259880175849581065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178505944346506901132774753 133879458259880175849581065)
  ·
    refine ⟨100409593694910131887185799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133879458259880175849581065 100409593694910131887185799)
    ·
      refine ⟨150614390542365197830778699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100409593694910131887185799 150614390542365197830778699)
      ·
        refine ⟨225921585813547796746168049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150614390542365197830778699 225921585813547796746168049)
        ·
          refine ⟨169441189360160847559626037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225921585813547796746168049 169441189360160847559626037)
          ·
            refine ⟨15885111502515079458714941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169441189360160847559626037 15885111502515079458714941)
            ·
              refine ⟨5956916813443154797018103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15885111502515079458714941 5956916813443154797018103)
              ·
                refine ⟨8935375220164732195527155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956916813443154797018103 8935375220164732195527155)
                ·
                  refine ⟨13403062830247098293290733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8935375220164732195527155 13403062830247098293290733)
                  ·
                    refine ⟨5026148561342661859984025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13403062830247098293290733 5026148561342661859984025)
                    ·
                      refine ⟨3769611421006996394988019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026148561342661859984025 3769611421006996394988019)
                      ·
                        rfl

theorem cell23_7341292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 3, 2].length) (baseStart_7341292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341292 prefixEnd_7341292 := by exact prefixLift 7341292
  have htrace : WordTrace (prefixWord ++ tailWord_7341292) baseStart_7341292 baseEnd_7341292 := by
    simpa [prefixWord, tailWord_7341292, baseEnd_7341292] using wordTrace_append hprefix tailTrace_7341292
  have hstable : (prefixWord ++ tailWord_7341292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341292).length < 2 ^ (prefixWord ++ tailWord_7341292).sum := by decide
  have hdescent : baseEnd_7341292 < baseStart_7341292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341401 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 8]
def baseStart_7341401 : Nat := 118140960795 + 7341401 * 2 ^ 59
def prefixEnd_7341401 : Nat := 4983230072969 + 3 ^ 40 * 7341401 * 2
def baseEnd_7341401 : Nat := 418851932266481829836113

theorem tailTrace_7341401 : CollatzResearch.WordTrace tailWord_7341401 prefixEnd_7341401 418851932266481829836113 := by
  unfold tailWord_7341401
  simp only [CollatzResearch.WordTrace]
  refine ⟨267762892076365463314880057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178508594717576975543253371 267762892076365463314880057)
  ·
    refine ⟨200822169057274097486160043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267762892076365463314880057 200822169057274097486160043)
    ·
      refine ⟨301233253585911146229240065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200822169057274097486160043 301233253585911146229240065)
      ·
        refine ⟨225924940189433359671930049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301233253585911146229240065 225924940189433359671930049)
        ·
          refine ⟨169443705142075019753947537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225924940189433359671930049 169443705142075019753947537)
          ·
            refine ⟨127082778856556264815460653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169443705142075019753947537 127082778856556264815460653)
            ·
              refine ⟨47656042071208599305797745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127082778856556264815460653 47656042071208599305797745)
              ·
                refine ⟨35742031553406449479348309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47656042071208599305797745 35742031553406449479348309)
                ·
                  refine ⟨418851932266481829836113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35742031553406449479348309 418851932266481829836113)
                  ·
                    rfl

theorem cell23_7341401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 8].length) (baseStart_7341401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341401 prefixEnd_7341401 := by exact prefixLift 7341401
  have htrace : WordTrace (prefixWord ++ tailWord_7341401) baseStart_7341401 baseEnd_7341401 := by
    simpa [prefixWord, tailWord_7341401, baseEnd_7341401] using wordTrace_append hprefix tailTrace_7341401
  have hstable : (prefixWord ++ tailWord_7341401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341401).length < 2 ^ (prefixWord ++ tailWord_7341401).sum := by decide
  have hdescent : baseEnd_7341401 < baseStart_7341401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341445 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 3, 1, 3]
def baseStart_7341445 : Nat := 118140960795 + 7341445 * 2 ^ 59
def prefixEnd_7341445 : Nat := 4983230072969 + 3 ^ 40 * 7341445 * 2
def baseEnd_7341445 : Nat := 3769689983547134296374815

theorem tailTrace_7341445 : CollatzResearch.WordTrace tailWord_7341445 prefixEnd_7341445 3769689983547134296374815 := by
  unfold tailWord_7341445
  simp only [CollatzResearch.WordTrace]
  refine ⟨267764496888206058829481789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178509664592137372552987859 267764496888206058829481789)
  ·
    refine ⟨100411686333077272061055671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267764496888206058829481789 100411686333077272061055671)
    ·
      refine ⟨150617529499615908091583507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100411686333077272061055671 150617529499615908091583507)
      ·
        refine ⟨225926294249423862137375261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150617529499615908091583507 225926294249423862137375261)
        ·
          refine ⟨84722360343533948301515723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225926294249423862137375261 84722360343533948301515723)
          ·
            refine ⟨127083540515300922452273585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84722360343533948301515723 127083540515300922452273585)
            ·
              refine ⟨95312655386475691839205189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127083540515300922452273585 95312655386475691839205189)
              ·
                refine ⟨17871122884964192219850973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95312655386475691839205189 17871122884964192219850973)
                ·
                  refine ⟨6701671081861572082444115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17871122884964192219850973 6701671081861572082444115)
                  ·
                    refine ⟨10052506622792358123666173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6701671081861572082444115 10052506622792358123666173)
                    ·
                      refine ⟨3769689983547134296374815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10052506622792358123666173 3769689983547134296374815)
                      ·
                        rfl

theorem cell23_7341445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_7341445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341445 prefixEnd_7341445 := by exact prefixLift 7341445
  have htrace : WordTrace (prefixWord ++ tailWord_7341445) baseStart_7341445 baseEnd_7341445 := by
    simpa [prefixWord, tailWord_7341445, baseEnd_7341445] using wordTrace_append hprefix tailTrace_7341445
  have hstable : (prefixWord ++ tailWord_7341445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341445).length < 2 ^ (prefixWord ++ tailWord_7341445).sum := by decide
  have hdescent : baseEnd_7341445 < baseStart_7341445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341479 : List Nat := [1, 1, 6, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_7341479 : Nat := 118140960795 + 7341479 * 2 ^ 59
def prefixEnd_7341479 : Nat := 4983230072969 + 3 ^ 40 * 7341479 * 2
def baseEnd_7341479 : Nat := 3769707441889387163349659

theorem tailTrace_7341479 : CollatzResearch.WordTrace tailWord_7341479 prefixEnd_7341479 3769707441889387163349659 := by
  unfold tailWord_7341479
  simp only [CollatzResearch.WordTrace]
  refine ⟨267765736970082882636219491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178510491313388588424146327 267765736970082882636219491)
  ·
    refine ⟨401648605455124323954329237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267765736970082882636219491 401648605455124323954329237)
    ·
      refine ⟨18827278380708952685359183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 401648605455124323954329237 18827278380708952685359183)
      ·
        refine ⟨28240917571063429028038775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18827278380708952685359183 28240917571063429028038775)
        ·
          refine ⟨42361376356595143542058163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28240917571063429028038775 42361376356595143542058163)
          ·
            refine ⟨63542064534892715313087245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42361376356595143542058163 63542064534892715313087245)
            ·
              refine ⟨23828274200584768242407717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63542064534892715313087245 23828274200584768242407717)
              ·
                refine ⟨4467801412609644045451447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23828274200584768242407717 4467801412609644045451447)
                ·
                  refine ⟨6701702118914466068177171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467801412609644045451447 6701702118914466068177171)
                  ·
                    refine ⟨10052553178371699102265757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6701702118914466068177171 10052553178371699102265757)
                    ·
                      refine ⟨3769707441889387163349659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10052553178371699102265757 3769707441889387163349659)
                      ·
                        rfl

theorem cell23_7341479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_7341479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341479 prefixEnd_7341479 := by exact prefixLift 7341479
  have htrace : WordTrace (prefixWord ++ tailWord_7341479) baseStart_7341479 baseEnd_7341479 := by
    simpa [prefixWord, tailWord_7341479, baseEnd_7341479] using wordTrace_append hprefix tailTrace_7341479
  have hstable : (prefixWord ++ tailWord_7341479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341479).length < 2 ^ (prefixWord ++ tailWord_7341479).sum := by decide
  have hdescent : baseEnd_7341479 < baseStart_7341479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341495 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 2, 4]
def baseStart_7341495 : Nat := 118140960795 + 7341495 * 2 ^ 59
def prefixEnd_7341495 : Nat := 4983230072969 + 3 ^ 40 * 7341495 * 2
def baseEnd_7341495 : Nat := 1256571885859953033583195

theorem tailTrace_7341495 : CollatzResearch.WordTrace tailWord_7341495 prefixEnd_7341495 1256571885859953033583195 := by
  unfold tailWord_7341495
  simp only [CollatzResearch.WordTrace]
  refine ⟨267766320538024917368801939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178510880358683278245867959 267766320538024917368801939)
  ·
    refine ⟨401649480807037376053202909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267766320538024917368801939 401649480807037376053202909)
    ·
      refine ⟨150618555302639016019951091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401649480807037376053202909 150618555302639016019951091)
      ·
        refine ⟨225927832953958524029926637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150618555302639016019951091 225927832953958524029926637)
        ·
          refine ⟨84722937357734446511222489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225927832953958524029926637 84722937357734446511222489)
          ·
            refine ⟨63542203018300834883416867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84722937357734446511222489 63542203018300834883416867)
            ·
              refine ⟨95313304527451252325125301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63542203018300834883416867 95313304527451252325125301)
              ·
                refine ⟨8935622299448554905480497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95313304527451252325125301 8935622299448554905480497)
                ·
                  refine ⟨6701716724586416179110373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8935622299448554905480497 6701716724586416179110373)
                  ·
                    refine ⟨1256571885859953033583195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6701716724586416179110373 1256571885859953033583195)
                    ·
                      rfl

theorem cell23_7341495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_7341495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341495 prefixEnd_7341495 := by exact prefixLift 7341495
  have htrace : WordTrace (prefixWord ++ tailWord_7341495) baseStart_7341495 baseEnd_7341495 := by
    simpa [prefixWord, tailWord_7341495, baseEnd_7341495] using wordTrace_append hprefix tailTrace_7341495
  have hstable : (prefixWord ++ tailWord_7341495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341495).length < 2 ^ (prefixWord ++ tailWord_7341495).sum := by decide
  have hdescent : baseEnd_7341495 < baseStart_7341495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341519 : List Nat := [1, 1, 2, 1, 1, 4, 3, 5, 1, 2, 2]
def baseStart_7341519 : Nat := 118140960795 + 7341519 * 2 ^ 59
def prefixEnd_7341519 : Nat := 4983230072969 + 3 ^ 40 * 7341519 * 2
def baseEnd_7341519 : Nat := 3769727981115567006849475

theorem tailTrace_7341519 : CollatzResearch.WordTrace tailWord_7341519 prefixEnd_7341519 3769727981115567006849475 := by
  unfold tailWord_7341519
  simp only [CollatzResearch.WordTrace]
  refine ⟨267767195889937969467675611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178511463926625312978450407 267767195889937969467675611)
  ·
    refine ⟨401650793834906954201513417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267767195889937969467675611 401650793834906954201513417)
    ·
      refine ⟨301238095376180215651135063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401650793834906954201513417 301238095376180215651135063)
      ·
        refine ⟨451857143064270323476702595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301238095376180215651135063 451857143064270323476702595)
        ·
          refine ⟨677785714596405485215053893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451857143064270323476702595 677785714596405485215053893)
          ·
            refine ⟨127084821486826028477822605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 677785714596405485215053893 127084821486826028477822605)
            ·
              refine ⟨47656808057559760679183477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127084821486826028477822605 47656808057559760679183477)
              ·
                refine ⟨4467825755396227563673451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47656808057559760679183477 4467825755396227563673451)
                ·
                  refine ⟨6701738633094341345510177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467825755396227563673451 6701738633094341345510177)
                  ·
                    refine ⟨5026303974820756009132633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6701738633094341345510177 5026303974820756009132633)
                    ·
                      refine ⟨3769727981115567006849475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026303974820756009132633 3769727981115567006849475)
                      ·
                        rfl

theorem cell23_7341519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 1, 2, 2].length) (baseStart_7341519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341519 prefixEnd_7341519 := by exact prefixLift 7341519
  have htrace : WordTrace (prefixWord ++ tailWord_7341519) baseStart_7341519 baseEnd_7341519 := by
    simpa [prefixWord, tailWord_7341519, baseEnd_7341519] using wordTrace_append hprefix tailTrace_7341519
  have hstable : (prefixWord ++ tailWord_7341519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341519).length < 2 ^ (prefixWord ++ tailWord_7341519).sum := by decide
  have hdescent : baseEnd_7341519 < baseStart_7341519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341549 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_7341549 : Nat := 118140960795 + 7341549 * 2 ^ 59
def prefixEnd_7341549 : Nat := 4983230072969 + 3 ^ 40 * 7341549 * 2
def baseEnd_7341549 : Nat := 3769743385535201889474337

theorem tailTrace_7341549 : CollatzResearch.WordTrace tailWord_7341549 prefixEnd_7341549 3769743385535201889474337 := by
  unfold tailWord_7341549
  simp only [CollatzResearch.WordTrace]
  refine ⟨267768290079829284591267701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178512193386552856394178467 267768290079829284591267701)
  ·
    refine ⟨25103277194983995430431347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267768290079829284591267701 25103277194983995430431347)
    ·
      refine ⟨37654915792475993145647021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25103277194983995430431347 37654915792475993145647021)
      ·
        refine ⟨14120593422178497429617633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37654915792475993145647021 14120593422178497429617633)
        ·
          refine ⟨10590445066633873072213225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14120593422178497429617633 10590445066633873072213225)
          ·
            refine ⟨7942833799975404804159919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10590445066633873072213225 7942833799975404804159919)
            ·
              refine ⟨11914250699963107206239879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942833799975404804159919 11914250699963107206239879)
              ·
                refine ⟨17871376049944660809359819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11914250699963107206239879 17871376049944660809359819)
                ·
                  refine ⟨26807064074916991214039729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17871376049944660809359819 26807064074916991214039729)
                  ·
                    refine ⟨20105298056187743410529797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26807064074916991214039729 20105298056187743410529797)
                    ·
                      refine ⟨3769743385535201889474337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20105298056187743410529797 3769743385535201889474337)
                      ·
                        rfl

theorem cell23_7341549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_7341549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341549 prefixEnd_7341549 := by exact prefixLift 7341549
  have htrace : WordTrace (prefixWord ++ tailWord_7341549) baseStart_7341549 baseEnd_7341549 := by
    simpa [prefixWord, tailWord_7341549, baseEnd_7341549] using wordTrace_append hprefix tailTrace_7341549
  have hstable : (prefixWord ++ tailWord_7341549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341549).length < 2 ^ (prefixWord ++ tailWord_7341549).sum := by decide
  have hdescent : baseEnd_7341549 < baseStart_7341549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341552 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 3]
def baseStart_7341552 : Nat := 118140960795 + 7341552 * 2 ^ 59
def prefixEnd_7341552 : Nat := 4983230072969 + 3 ^ 40 * 7341552 * 2
def baseEnd_7341552 : Nat := 3769744925977165377736823

theorem tailTrace_7341552 : CollatzResearch.WordTrace tailWord_7341552 prefixEnd_7341552 3769744925977165377736823 := by
  unfold tailWord_7341552
  simp only [CollatzResearch.WordTrace]
  refine ⟨133884199749409208051813455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178512266332545610735751273 133884199749409208051813455)
  ·
    refine ⟨200826299624113812077720183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133884199749409208051813455 200826299624113812077720183)
    ·
      refine ⟨301239449436170718116580275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200826299624113812077720183 301239449436170718116580275)
      ·
        refine ⟨451859174154256077174870413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301239449436170718116580275 451859174154256077174870413)
        ·
          refine ⟨169447190307846028940576405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451859174154256077174870413 169447190307846028940576405)
          ·
            refine ⟨7942837045680282606589519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169447190307846028940576405 7942837045680282606589519)
            ·
              refine ⟨11914255568520423909884279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942837045680282606589519 11914255568520423909884279)
              ·
                refine ⟨17871383352780635864826419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11914255568520423909884279 17871383352780635864826419)
                ·
                  refine ⟨26807075029170953797239629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17871383352780635864826419 26807075029170953797239629)
                  ·
                    refine ⟨10052653135939107673964861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26807075029170953797239629 10052653135939107673964861)
                    ·
                      refine ⟨3769744925977165377736823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10052653135939107673964861 3769744925977165377736823)
                      ·
                        rfl

theorem cell23_7341552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 3].length) (baseStart_7341552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341552 prefixEnd_7341552 := by exact prefixLift 7341552
  have htrace : WordTrace (prefixWord ++ tailWord_7341552) baseStart_7341552 baseEnd_7341552 := by
    simpa [prefixWord, tailWord_7341552, baseEnd_7341552] using wordTrace_append hprefix tailTrace_7341552
  have hstable : (prefixWord ++ tailWord_7341552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341552).length < 2 ^ (prefixWord ++ tailWord_7341552).sum := by decide
  have hdescent : baseEnd_7341552 < baseStart_7341552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341570 : List Nat := [3, 4, 1, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_7341570 : Nat := 118140960795 + 7341570 * 2 ^ 59
def prefixEnd_7341570 : Nat := 4983230072969 + 3 ^ 40 * 7341570 * 2
def baseEnd_7341570 : Nat := 3769754168628946307311741

theorem tailTrace_7341570 : CollatzResearch.WordTrace tailWord_7341570 prefixEnd_7341570 3769754168628946307311741 := by
  unfold tailWord_7341570
  simp only [CollatzResearch.WordTrace]
  refine ⟨66942264003188301294445541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178512704008502136785188109 66942264003188301294445541)
  ·
    refine ⟨12551674500597806492708539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66942264003188301294445541 12551674500597806492708539)
    ·
      refine ⟨18827511750896709739062809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12551674500597806492708539 18827511750896709739062809)
      ·
        refine ⟨14120633813172532304297107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18827511750896709739062809 14120633813172532304297107)
        ·
          refine ⟨21180950719758798456445661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14120633813172532304297107 21180950719758798456445661)
          ·
            refine ⟨7942856519909549421167123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21180950719758798456445661 7942856519909549421167123)
            ·
              refine ⟨11914284779864324131750685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942856519909549421167123 11914284779864324131750685)
              ·
                refine ⟨4467856792449121549406507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11914284779864324131750685 4467856792449121549406507)
                ·
                  refine ⟨6701785188673682324109761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467856792449121549406507 6701785188673682324109761)
                  ·
                    refine ⟨5026338891505261743082321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6701785188673682324109761 5026338891505261743082321)
                    ·
                      refine ⟨3769754168628946307311741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026338891505261743082321 3769754168628946307311741)
                      ·
                        rfl

theorem cell23_7341570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_7341570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341570 prefixEnd_7341570 := by exact prefixLift 7341570
  have htrace : WordTrace (prefixWord ++ tailWord_7341570) baseStart_7341570 baseEnd_7341570 := by
    simpa [prefixWord, tailWord_7341570, baseEnd_7341570] using wordTrace_append hprefix tailTrace_7341570
  have hstable : (prefixWord ++ tailWord_7341570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341570).length < 2 ^ (prefixWord ++ tailWord_7341570).sum := by decide
  have hdescent : baseEnd_7341570 < baseStart_7341570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341603 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 2, 1, 3]
def baseStart_7341603 : Nat := 118140960795 + 7341603 * 2 ^ 59
def prefixEnd_7341603 : Nat := 4983230072969 + 3 ^ 40 * 7341603 * 2
def baseEnd_7341603 : Nat := 3769771113490544678199089

theorem tailTrace_7341603 : CollatzResearch.WordTrace tailWord_7341603 prefixEnd_7341603 3769771113490544678199089 := by
  unfold tailWord_7341603
  simp only [CollatzResearch.WordTrace]
  refine ⟨267770259621633651813733463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178513506414422434542488975 267770259621633651813733463)
  ·
    refine ⟨401655389432450477720600195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267770259621633651813733463 401655389432450477720600195)
    ·
      refine ⟨602483084148675716580900293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401655389432450477720600195 602483084148675716580900293)
      ·
        refine ⟨112965578277876696858918805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 602483084148675716580900293 112965578277876696858918805)
        ·
          refine ⟨5295261481775470165261819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112965578277876696858918805 5295261481775470165261819)
          ·
            refine ⟨7942892222663205247892729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295261481775470165261819 7942892222663205247892729)
            ·
              refine ⟨5957169166997403935919547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7942892222663205247892729 5957169166997403935919547)
              ·
                refine ⟨8935753750496105903879321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5957169166997403935919547 8935753750496105903879321)
                ·
                  refine ⟨6701815312872079427909491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8935753750496105903879321 6701815312872079427909491)
                  ·
                    refine ⟨10052722969308119141864237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6701815312872079427909491 10052722969308119141864237)
                    ·
                      refine ⟨3769771113490544678199089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10052722969308119141864237 3769771113490544678199089)
                      ·
                        rfl

theorem cell23_7341603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_7341603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341603 prefixEnd_7341603 := by exact prefixLift 7341603
  have htrace : WordTrace (prefixWord ++ tailWord_7341603) baseStart_7341603 baseEnd_7341603 := by
    simpa [prefixWord, tailWord_7341603, baseEnd_7341603] using wordTrace_append hprefix tailTrace_7341603
  have hstable : (prefixWord ++ tailWord_7341603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341603).length < 2 ^ (prefixWord ++ tailWord_7341603).sum := by decide
  have hdescent : baseEnd_7341603 < baseStart_7341603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341652 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_7341652 : Nat := 118140960795 + 7341652 * 2 ^ 59
def prefixEnd_7341652 : Nat := 4983230072969 + 3 ^ 40 * 7341652 * 2
def baseEnd_7341652 : Nat := 3769796274042614986486363

theorem tailTrace_7341652 : CollatzResearch.WordTrace tailWord_7341652 prefixEnd_7341652 3769796274042614986486363 := by
  unfold tailWord_7341652
  simp only [CollatzResearch.WordTrace]
  refine ⟨133886023399228066591133605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178514697865637422121511473 133886023399228066591133605)
  ·
    refine ⟨25103629387355262485837551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133886023399228066591133605 25103629387355262485837551)
    ·
      refine ⟨37655444081032893728756327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25103629387355262485837551 37655444081032893728756327)
      ·
        refine ⟨56483166121549340593134491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37655444081032893728756327 56483166121549340593134491)
        ·
          refine ⟨84724749182324010889701737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56483166121549340593134491 84724749182324010889701737)
          ·
            refine ⟨63543561886743008167276303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84724749182324010889701737 63543561886743008167276303)
            ·
              refine ⟨95315342830114512250914455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63543561886743008167276303 95315342830114512250914455)
              ·
                refine ⟨142973014245171768376371683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95315342830114512250914455 142973014245171768376371683)
                ·
                  refine ⟨214459521367757652564557525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142973014245171768376371683 214459521367757652564557525)
                  ·
                    refine ⟨5026395032056819981981817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 214459521367757652564557525 5026395032056819981981817)
                    ·
                      refine ⟨3769796274042614986486363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026395032056819981981817 3769796274042614986486363)
                      ·
                        rfl

theorem cell23_7341652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_7341652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341652 prefixEnd_7341652 := by exact prefixLift 7341652
  have htrace : WordTrace (prefixWord ++ tailWord_7341652) baseStart_7341652 baseEnd_7341652 := by
    simpa [prefixWord, tailWord_7341652, baseEnd_7341652] using wordTrace_append hprefix tailTrace_7341652
  have hstable : (prefixWord ++ tailWord_7341652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341652).length < 2 ^ (prefixWord ++ tailWord_7341652).sum := by decide
  have hdescent : baseEnd_7341652 < baseStart_7341652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341655 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_7341655 : Nat := 118140960795 + 7341655 * 2 ^ 59
def prefixEnd_7341655 : Nat := 4983230072969 + 3 ^ 40 * 7341655 * 2
def baseEnd_7341655 : Nat := 3769797814484578474748849

theorem tailTrace_7341655 : CollatzResearch.WordTrace tailWord_7341655 prefixEnd_7341655 3769797814484578474748849 := by
  unfold tailWord_7341655
  simp only [CollatzResearch.WordTrace]
  refine ⟨267772156217445264694626419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178514770811630176463084279 267772156217445264694626419)
  ·
    refine ⟨401658234326167897041939629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267772156217445264694626419 401658234326167897041939629)
    ·
      refine ⟨150621837872312961390727361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401658234326167897041939629 150621837872312961390727361)
      ·
        refine ⟨112966378404234721043045521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150621837872312961390727361 112966378404234721043045521)
        ·
          refine ⟨84724783803176040782284141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112966378404234721043045521 84724783803176040782284141)
          ·
            refine ⟨31771793926191015293356553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84724783803176040782284141 31771793926191015293356553)
            ·
              refine ⟨23828845444643261470017415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31771793926191015293356553 23828845444643261470017415)
              ·
                refine ⟨35743268166964892205026123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23828845444643261470017415 35743268166964892205026123)
                ·
                  refine ⟨53614902250447338307539185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35743268166964892205026123 53614902250447338307539185)
                  ·
                    refine ⟨40211176687835503730654389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53614902250447338307539185 40211176687835503730654389)
                    ·
                      refine ⟨3769797814484578474748849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40211176687835503730654389 3769797814484578474748849)
                      ·
                        rfl

theorem cell23_7341655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_7341655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341655 prefixEnd_7341655 := by exact prefixLift 7341655
  have htrace : WordTrace (prefixWord ++ tailWord_7341655) baseStart_7341655 baseEnd_7341655 := by
    simpa [prefixWord, tailWord_7341655, baseEnd_7341655] using wordTrace_append hprefix tailTrace_7341655
  have hstable : (prefixWord ++ tailWord_7341655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341655).length < 2 ^ (prefixWord ++ tailWord_7341655).sum := by decide
  have hdescent : baseEnd_7341655 < baseStart_7341655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341665 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_7341665 : Nat := 118140960795 + 7341665 * 2 ^ 59
def prefixEnd_7341665 : Nat := 4983230072969 + 3 ^ 40 * 7341665 * 2
def baseEnd_7341665 : Nat := 3769802949291123435623803

theorem tailTrace_7341665 : CollatzResearch.WordTrace tailWord_7341665 prefixEnd_7341665 3769802949291123435623803 := by
  unfold tailWord_7341665
  simp only [CollatzResearch.WordTrace]
  refine ⟨267772520947409036402490449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178515013964939357601660299 267772520947409036402490449)
  ·
    refine ⟨200829390710556777301867837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267772520947409036402490449 200829390710556777301867837)
    ·
      refine ⟨75311021516458791488200439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200829390710556777301867837 75311021516458791488200439)
      ·
        refine ⟨112966532274688187232300659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75311021516458791488200439 112966532274688187232300659)
        ·
          refine ⟨169449798412032280848450989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112966532274688187232300659 169449798412032280848450989)
          ·
            refine ⟨63543674404512105318169121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169449798412032280848450989 63543674404512105318169121)
            ·
              refine ⟨47657755803384078988626841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63543674404512105318169121 47657755803384078988626841)
              ·
                refine ⟨35743316852538059241470131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47657755803384078988626841 35743316852538059241470131)
                ·
                  refine ⟨53614975278807088862205197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35743316852538059241470131 53614975278807088862205197)
                  ·
                    refine ⟨20105615729552658323326949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53614975278807088862205197 20105615729552658323326949)
                    ·
                      refine ⟨3769802949291123435623803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20105615729552658323326949 3769802949291123435623803)
                      ·
                        rfl

theorem cell23_7341665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_7341665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341665 prefixEnd_7341665 := by exact prefixLift 7341665
  have htrace : WordTrace (prefixWord ++ tailWord_7341665) baseStart_7341665 baseEnd_7341665 := by
    simpa [prefixWord, tailWord_7341665, baseEnd_7341665] using wordTrace_append hprefix tailTrace_7341665
  have hstable : (prefixWord ++ tailWord_7341665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341665).length < 2 ^ (prefixWord ++ tailWord_7341665).sum := by decide
  have hdescent : baseEnd_7341665 < baseStart_7341665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341682 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_7341682 : Nat := 118140960795 + 7341682 * 2 ^ 59
def prefixEnd_7341682 : Nat := 4983230072969 + 3 ^ 40 * 7341682 * 2
def baseEnd_7341682 : Nat := 3769811678462249869111225

theorem tailTrace_7341682 : CollatzResearch.WordTrace tailWord_7341682 prefixEnd_7341682 3769811678462249869111225 := by
  unfold tailWord_7341682
  simp only [CollatzResearch.WordTrace]
  refine ⟨66943285247086862076464825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178515427325564965537239533 66943285247086862076464825)
  ·
    refine ⟨50207463935315146557348619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66943285247086862076464825 50207463935315146557348619)
    ·
      refine ⟨75311195902972719836022929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50207463935315146557348619 75311195902972719836022929)
      ·
        refine ⟨56483396927229539877017197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75311195902972719836022929 56483396927229539877017197)
        ·
          refine ⟨21181273847711077453881449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56483396927229539877017197 21181273847711077453881449)
          ·
            refine ⟨15885955385783308090411087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21181273847711077453881449 15885955385783308090411087)
            ·
              refine ⟨23828933078674962135616631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15885955385783308090411087 23828933078674962135616631)
              ·
                refine ⟨35743399618012443203424947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23828933078674962135616631 35743399618012443203424947)
                ·
                  refine ⟨53615099427018664805137421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35743399618012443203424947 53615099427018664805137421)
                  ·
                    refine ⟨20105662285131999301926533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53615099427018664805137421 20105662285131999301926533)
                    ·
                      refine ⟨3769811678462249869111225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20105662285131999301926533 3769811678462249869111225)
                      ·
                        rfl

theorem cell23_7341682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_7341682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341682 prefixEnd_7341682 := by exact prefixLift 7341682
  have htrace : WordTrace (prefixWord ++ tailWord_7341682) baseStart_7341682 baseEnd_7341682 := by
    simpa [prefixWord, tailWord_7341682, baseEnd_7341682] using wordTrace_append hprefix tailTrace_7341682
  have hstable : (prefixWord ++ tailWord_7341682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341682).length < 2 ^ (prefixWord ++ tailWord_7341682).sum := by decide
  have hdescent : baseEnd_7341682 < baseStart_7341682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341715 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 3]
def baseStart_7341715 : Nat := 118140960795 + 7341715 * 2 ^ 59
def prefixEnd_7341715 : Nat := 4983230072969 + 3 ^ 40 * 7341715 * 2
def baseEnd_7341715 : Nat := 3769828623323848239998573

theorem tailTrace_7341715 : CollatzResearch.WordTrace tailWord_7341715 prefixEnd_7341715 3769828623323848239998573 := by
  unfold tailWord_7341715
  simp only [CollatzResearch.WordTrace]
  refine ⟨267774344597227894941810599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178516229731485263294540399 267774344597227894941810599)
  ·
    refine ⟨401661516895841842412715899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267774344597227894941810599 401661516895841842412715899)
    ·
      refine ⟨602492275343762763619073849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401661516895841842412715899 602492275343762763619073849)
      ·
        refine ⟨451869206507822072714305387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602492275343762763619073849 451869206507822072714305387)
        ·
          refine ⟨677803809761733109071458081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451869206507822072714305387 677803809761733109071458081)
          ·
            refine ⟨508352857321299831803593561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677803809761733109071458081 508352857321299831803593561)
            ·
              refine ⟨381264642990974873852695171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508352857321299831803593561 381264642990974873852695171)
              ·
                refine ⟨571896964486462310779042757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381264642990974873852695171 571896964486462310779042757)
                ·
                  refine ⟨107230680841211683271070517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 571896964486462310779042757 107230680841211683271070517)
                  ·
                    refine ⟨10052876328863595306662861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107230680841211683271070517 10052876328863595306662861)
                    ·
                      refine ⟨3769828623323848239998573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10052876328863595306662861 3769828623323848239998573)
                      ·
                        rfl

theorem cell23_7341715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 3].length) (baseStart_7341715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341715 prefixEnd_7341715 := by exact prefixLift 7341715
  have htrace : WordTrace (prefixWord ++ tailWord_7341715) baseStart_7341715 baseEnd_7341715 := by
    simpa [prefixWord, tailWord_7341715, baseEnd_7341715] using wordTrace_append hprefix tailTrace_7341715
  have hstable : (prefixWord ++ tailWord_7341715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341715).length < 2 ^ (prefixWord ++ tailWord_7341715).sum := by decide
  have hdescent : baseEnd_7341715 < baseStart_7341715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341725 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_7341725 : Nat := 118140960795 + 7341725 * 2 ^ 59
def prefixEnd_7341725 : Nat := 4983230072969 + 3 ^ 40 * 7341725 * 2
def baseEnd_7341725 : Nat := 3769833758130393200873527

theorem tailTrace_7341725 : CollatzResearch.WordTrace tailWord_7341725 prefixEnd_7341725 3769833758130393200873527 := by
  unfold tailWord_7341725
  simp only [CollatzResearch.WordTrace]
  refine ⟨267774709327191666649674629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178516472884794444433116419 267774709327191666649674629)
  ·
    refine ⟨50207757998848437496813993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267774709327191666649674629 50207757998848437496813993)
    ·
      refine ⟨37655818499136328122610495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50207757998848437496813993 37655818499136328122610495)
      ·
        refine ⟨56483727748704492183915743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37655818499136328122610495 56483727748704492183915743)
        ·
          refine ⟨84725591623056738275873615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56483727748704492183915743 84725591623056738275873615)
          ·
            refine ⟨127088387434585107413810423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84725591623056738275873615 127088387434585107413810423)
            ·
              refine ⟨190632581151877661120715635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127088387434585107413810423 190632581151877661120715635)
              ·
                refine ⟨285948871727816491681073453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190632581151877661120715635 285948871727816491681073453)
                ·
                  refine ⟨107230826897931184380402545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285948871727816491681073453 107230826897931184380402545)
                  ·
                    refine ⟨80423120173448388285301909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107230826897931184380402545 80423120173448388285301909)
                    ·
                      refine ⟨3769833758130393200873527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80423120173448388285301909 3769833758130393200873527)
                      ·
                        rfl

theorem cell23_7341725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_7341725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341725 prefixEnd_7341725 := by exact prefixLift 7341725
  have htrace : WordTrace (prefixWord ++ tailWord_7341725) baseStart_7341725 baseEnd_7341725 := by
    simpa [prefixWord, tailWord_7341725, baseEnd_7341725] using wordTrace_append hprefix tailTrace_7341725
  have hstable : (prefixWord ++ tailWord_7341725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341725).length < 2 ^ (prefixWord ++ tailWord_7341725).sum := by decide
  have hdescent : baseEnd_7341725 < baseStart_7341725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341759 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 2, 3, 2]
def baseStart_7341759 : Nat := 118140960795 + 7341759 * 2 ^ 59
def prefixEnd_7341759 : Nat := 4983230072969 + 3 ^ 40 * 7341759 * 2
def baseEnd_7341759 : Nat := 3769851216472646067848371

theorem tailTrace_7341759 : CollatzResearch.WordTrace tailWord_7341759 prefixEnd_7341759 3769851216472646067848371 := by
  unfold tailWord_7341759
  simp only [CollatzResearch.WordTrace]
  refine ⟨267775949409068490456412331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178517299606045660304274887 267775949409068490456412331)
  ·
    refine ⟨401663924113602735684618497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267775949409068490456412331 401663924113602735684618497)
    ·
      refine ⟨301247943085202051763463873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401663924113602735684618497 301247943085202051763463873)
      ·
        refine ⟨225935957313901538822597905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301247943085202051763463873 225935957313901538822597905)
        ·
          refine ⟨169451967985426154116948429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225935957313901538822597905 169451967985426154116948429)
          ·
            refine ⟨63544487994534807793855661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169451967985426154116948429 63544487994534807793855661)
            ·
              refine ⟨23829182997950552922695873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63544487994534807793855661 23829182997950552922695873)
              ·
                refine ⟨17871887248462914692021905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23829182997950552922695873 17871887248462914692021905)
                ·
                  refine ⟨13403915436347186019016429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17871887248462914692021905 13403915436347186019016429)
                  ·
                    refine ⟨5026468288630194757131161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13403915436347186019016429 5026468288630194757131161)
                    ·
                      refine ⟨3769851216472646067848371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026468288630194757131161 3769851216472646067848371)
                      ·
                        rfl

theorem cell23_7341759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 3, 2].length) (baseStart_7341759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341759 prefixEnd_7341759 := by exact prefixLift 7341759
  have htrace : WordTrace (prefixWord ++ tailWord_7341759) baseStart_7341759 baseEnd_7341759 := by
    simpa [prefixWord, tailWord_7341759, baseEnd_7341759] using wordTrace_append hprefix tailTrace_7341759
  have hstable : (prefixWord ++ tailWord_7341759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341759).length < 2 ^ (prefixWord ++ tailWord_7341759).sum := by decide
  have hdescent : baseEnd_7341759 < baseStart_7341759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341765 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_7341765 : Nat := 118140960795 + 7341765 * 2 ^ 59
def prefixEnd_7341765 : Nat := 4983230072969 + 3 ^ 40 * 7341765 * 2
def baseEnd_7341765 : Nat := 1256618099118857681457781

theorem tailTrace_7341765 : CollatzResearch.WordTrace tailWord_7341765 prefixEnd_7341765 1256618099118857681457781 := by
  unfold tailWord_7341765
  simp only [CollatzResearch.WordTrace]
  refine ⟨267776168247046753481130749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178517445498031168987420499 267776168247046753481130749)
  ·
    refine ⟨100416063092642532555424031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267776168247046753481130749 100416063092642532555424031)
    ·
      refine ⟨150624094638963798833136047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100416063092642532555424031 150624094638963798833136047)
      ·
        refine ⟨225936141958445698249704071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150624094638963798833136047 225936141958445698249704071)
        ·
          refine ⟨338904212937668547374556107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225936141958445698249704071 338904212937668547374556107)
          ·
            refine ⟨508356319406502821061834161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338904212937668547374556107 508356319406502821061834161)
            ·
              refine ⟨381267239554877115796375621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508356319406502821061834161 381267239554877115796375621)
              ·
                refine ⟨71487607416539459211820429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381267239554877115796375621 71487607416539459211820429)
                ·
                  refine ⟨26807852781202297204432661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71487607416539459211820429 26807852781202297204432661)
                  ·
                    refine ⟨1256618099118857681457781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26807852781202297204432661 1256618099118857681457781)
                    ·
                      rfl

theorem cell23_7341765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_7341765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341765 prefixEnd_7341765 := by exact prefixLift 7341765
  have htrace : WordTrace (prefixWord ++ tailWord_7341765) baseStart_7341765 baseEnd_7341765 := by
    simpa [prefixWord, tailWord_7341765, baseEnd_7341765] using wordTrace_append hprefix tailTrace_7341765
  have hstable : (prefixWord ++ tailWord_7341765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341765).length < 2 ^ (prefixWord ++ tailWord_7341765).sum := by decide
  have hdescent : baseEnd_7341765 < baseStart_7341765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341773 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 6]
def baseStart_7341773 : Nat := 118140960795 + 7341773 * 2 ^ 59
def prefixEnd_7341773 : Nat := 4983230072969 + 3 ^ 40 * 7341773 * 2
def baseEnd_7341773 : Nat := 418873156133534334785923

theorem tailTrace_7341773 : CollatzResearch.WordTrace tailWord_7341773 prefixEnd_7341773 418873156133534334785923 := by
  unfold tailWord_7341773
  simp only [CollatzResearch.WordTrace]
  refine ⟨267776460031017770847421973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178517640020678513898281315 267776460031017770847421973)
  ·
    refine ⟨12552021563953958008472905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 267776460031017770847421973 12552021563953958008472905)
    ·
      refine ⟨9414016172965468506354679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12552021563953958008472905 9414016172965468506354679)
      ·
        refine ⟨14121024259448202759532019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9414016172965468506354679 14121024259448202759532019)
        ·
          refine ⟨21181536389172304139298029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14121024259448202759532019 21181536389172304139298029)
          ·
            refine ⟨7943076145939614052236761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21181536389172304139298029 7943076145939614052236761)
            ·
              refine ⟨5957307109454710539177571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7943076145939614052236761 5957307109454710539177571)
              ·
                refine ⟨8935960664182065808766357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5957307109454710539177571 8935960664182065808766357)
                ·
                  refine ⟨418873156133534334785923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8935960664182065808766357 418873156133534334785923)
                  ·
                    rfl

theorem cell23_7341773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_7341773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341773 prefixEnd_7341773 := by exact prefixLift 7341773
  have htrace : WordTrace (prefixWord ++ tailWord_7341773) baseStart_7341773 baseEnd_7341773 := by
    simpa [prefixWord, tailWord_7341773, baseEnd_7341773] using wordTrace_append hprefix tailTrace_7341773
  have hstable : (prefixWord ++ tailWord_7341773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341773).length < 2 ^ (prefixWord ++ tailWord_7341773).sum := by decide
  have hdescent : baseEnd_7341773 < baseStart_7341773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341802 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_7341802 : Nat := 118140960795 + 7341802 * 2 ^ 59
def prefixEnd_7341802 : Nat := 4983230072969 + 3 ^ 40 * 7341802 * 2
def baseEnd_7341802 : Nat := 3769873296140789399610673

theorem tailTrace_7341802 : CollatzResearch.WordTrace tailWord_7341802 prefixEnd_7341802 3769873296140789399610673 := by
  unfold tailWord_7341802
  simp only [CollatzResearch.WordTrace]
  refine ⟨66944379436978177200056915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178518345165275139200151773 66944379436978177200056915)
  ·
    refine ⟨100416569155467265800085373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66944379436978177200056915 100416569155467265800085373)
    ·
      refine ⟨37656213433300224675032015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100416569155467265800085373 37656213433300224675032015)
      ·
        refine ⟨56484320149950337012548023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37656213433300224675032015 56484320149950337012548023)
        ·
          refine ⟨84726480224925505518822035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56484320149950337012548023 84726480224925505518822035)
          ·
            refine ⟨127089720337388258278233053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84726480224925505518822035 127089720337388258278233053)
            ·
              refine ⟨47658645126520596854337395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127089720337388258278233053 47658645126520596854337395)
              ·
                refine ⟨71487967689780895281506093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47658645126520596854337395 71487967689780895281506093)
                ·
                  refine ⟨26807987883667835730564785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71487967689780895281506093 26807987883667835730564785)
                  ·
                    refine ⟨20105990912750876797923589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26807987883667835730564785 20105990912750876797923589)
                    ·
                      refine ⟨3769873296140789399610673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20105990912750876797923589 3769873296140789399610673)
                      ·
                        rfl

theorem cell23_7341802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_7341802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341802 prefixEnd_7341802 := by exact prefixLift 7341802
  have htrace : WordTrace (prefixWord ++ tailWord_7341802) baseStart_7341802 baseEnd_7341802 := by
    simpa [prefixWord, tailWord_7341802, baseEnd_7341802] using wordTrace_append hprefix tailTrace_7341802
  have hstable : (prefixWord ++ tailWord_7341802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341802).length < 2 ^ (prefixWord ++ tailWord_7341802).sum := by decide
  have hdescent : baseEnd_7341802 < baseStart_7341802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341806 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_7341806 : Nat := 118140960795 + 7341806 * 2 ^ 59
def prefixEnd_7341806 : Nat := 4983230072969 + 3 ^ 40 * 7341806 * 2
def baseEnd_7341806 : Nat := 3769875350063407383960655

theorem tailTrace_7341806 : CollatzResearch.WordTrace tailWord_7341806 prefixEnd_7341806 3769875350063407383960655 := by
  unfold tailWord_7341806
  simp only [CollatzResearch.WordTrace]
  refine ⟨33472207954987277185421659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178518442426598811655582181 33472207954987277185421659)
  ·
    refine ⟨50208311932480915778132489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33472207954987277185421659 50208311932480915778132489)
    ·
      refine ⟨37656233949360686833599367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50208311932480915778132489 37656233949360686833599367)
      ·
        refine ⟨56484350924041030250399051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37656233949360686833599367 56484350924041030250399051)
        ·
          refine ⟨84726526386061545375598577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56484350924041030250399051 84726526386061545375598577)
          ·
            refine ⟨63544894789546159031698933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84726526386061545375598577 63544894789546159031698933)
            ·
              refine ⟨5957333886519952409221775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63544894789546159031698933 5957333886519952409221775)
              ·
                refine ⟨8936000829779928613832663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5957333886519952409221775 8936000829779928613832663)
                ·
                  refine ⟨13404001244669892920748995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8936000829779928613832663 13404001244669892920748995)
                  ·
                    refine ⟨20106001867004839381123493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13404001244669892920748995 20106001867004839381123493)
                    ·
                      refine ⟨3769875350063407383960655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20106001867004839381123493 3769875350063407383960655)
                      ·
                        rfl

theorem cell23_7341806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_7341806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341806 prefixEnd_7341806 := by exact prefixLift 7341806
  have htrace : WordTrace (prefixWord ++ tailWord_7341806) baseStart_7341806 baseEnd_7341806 := by
    simpa [prefixWord, tailWord_7341806, baseEnd_7341806] using wordTrace_append hprefix tailTrace_7341806
  have hstable : (prefixWord ++ tailWord_7341806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341806).length < 2 ^ (prefixWord ++ tailWord_7341806).sum := by decide
  have hdescent : baseEnd_7341806 < baseStart_7341806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341809 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 5]
def baseStart_7341809 : Nat := 118140960795 + 7341809 * 2 ^ 59
def prefixEnd_7341809 : Nat := 4983230072969 + 3 ^ 40 * 7341809 * 2
def baseEnd_7341809 : Nat := 3769876890505370872223141

theorem tailTrace_7341809 : CollatzResearch.WordTrace tailWord_7341809 prefixEnd_7341809 3769876890505370872223141 := by
  unfold tailWord_7341809
  simp only [CollatzResearch.WordTrace]
  refine ⟨267777773058887348995732481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178518515372591565997154987 267777773058887348995732481)
  ·
    refine ⟨200833329794165511746799361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267777773058887348995732481 200833329794165511746799361)
    ·
      refine ⟨150624997345624133810099521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200833329794165511746799361 150624997345624133810099521)
      ·
        refine ⟨112968748009218100357574641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150624997345624133810099521 112968748009218100357574641)
        ·
          refine ⟨84726561006913575268180981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112968748009218100357574641 84726561006913575268180981)
          ·
            refine ⟨7943115094398147681391967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84726561006913575268180981 7943115094398147681391967)
            ·
              refine ⟨11914672641597221522087951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943115094398147681391967 11914672641597221522087951)
              ·
                refine ⟨17872008962395832283131927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11914672641597221522087951 17872008962395832283131927)
                ·
                  refine ⟨26808013443593748424697891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17872008962395832283131927 26808013443593748424697891)
                  ·
                    refine ⟨40212020165390622637046837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26808013443593748424697891 40212020165390622637046837)
                    ·
                      refine ⟨3769876890505370872223141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40212020165390622637046837 3769876890505370872223141)
                      ·
                        rfl

theorem cell23_7341809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_7341809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341809 prefixEnd_7341809 := by exact prefixLift 7341809
  have htrace : WordTrace (prefixWord ++ tailWord_7341809) baseStart_7341809 baseEnd_7341809 := by
    simpa [prefixWord, tailWord_7341809, baseEnd_7341809] using wordTrace_append hprefix tailTrace_7341809
  have hstable : (prefixWord ++ tailWord_7341809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341809).length < 2 ^ (prefixWord ++ tailWord_7341809).sum := by decide
  have hdescent : baseEnd_7341809 < baseStart_7341809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341844 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_7341844 : Nat := 118140960795 + 7341844 * 2 ^ 59
def prefixEnd_7341844 : Nat := 4983230072969 + 3 ^ 40 * 7341844 * 2
def baseEnd_7341844 : Nat := 3769894862328278235285481

theorem tailTrace_7341844 : CollatzResearch.WordTrace tailWord_7341844 prefixEnd_7341844 3769894862328278235285481 := by
  unfold tailWord_7341844
  simp only [CollatzResearch.WordTrace]
  refine ⟨133889524806880274986628293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178519366409173699982171057 133889524806880274986628293)
  ·
    refine ⟨25104285901290051559992805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133889524806880274986628293 25104285901290051559992805)
    ·
      refine ⟨4707053606491884667498651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25104285901290051559992805 4707053606491884667498651)
      ·
        refine ⟨7060580409737827001247977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707053606491884667498651 7060580409737827001247977)
        ·
          refine ⟨5295435307303370250935983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7060580409737827001247977 5295435307303370250935983)
          ·
            refine ⟨7943152960955055376403975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295435307303370250935983 7943152960955055376403975)
            ·
              refine ⟨11914729441432583064605963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943152960955055376403975 11914729441432583064605963)
              ·
                refine ⟨17872094162148874596908945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11914729441432583064605963 17872094162148874596908945)
                ·
                  refine ⟨13404070621611655947681709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17872094162148874596908945 13404070621611655947681709)
                  ·
                    refine ⟨5026526483104370980380641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13404070621611655947681709 5026526483104370980380641)
                    ·
                      refine ⟨3769894862328278235285481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026526483104370980380641 3769894862328278235285481)
                      ·
                        rfl

theorem cell23_7341844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_7341844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341844 prefixEnd_7341844 := by exact prefixLift 7341844
  have htrace : WordTrace (prefixWord ++ tailWord_7341844) baseStart_7341844 baseEnd_7341844 := by
    simpa [prefixWord, tailWord_7341844, baseEnd_7341844] using wordTrace_append hprefix tailTrace_7341844
  have hstable : (prefixWord ++ tailWord_7341844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341844).length < 2 ^ (prefixWord ++ tailWord_7341844).sum := by decide
  have hdescent : baseEnd_7341844 < baseStart_7341844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341852 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_7341852 : Nat := 118140960795 + 7341852 * 2 ^ 59
def prefixEnd_7341852 : Nat := 4983230072969 + 3 ^ 40 * 7341852 * 2
def baseEnd_7341852 : Nat := 3769898970173514203985443

theorem tailTrace_7341852 : CollatzResearch.WordTrace tailWord_7341852 prefixEnd_7341852 3769898970173514203985443 := by
  unfold tailWord_7341852
  simp only [CollatzResearch.WordTrace]
  refine ⟨133889670698865783669773905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178519560931821044893031873 133889670698865783669773905)
  ·
    refine ⟨100417253024149337752330429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133889670698865783669773905 100417253024149337752330429)
    ·
      refine ⟨37656469884056001657123911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100417253024149337752330429 37656469884056001657123911)
      ·
        refine ⟨56484704826084002485685867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37656469884056001657123911 56484704826084002485685867)
        ·
          refine ⟨84727057239126003728528801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56484704826084002485685867 84727057239126003728528801)
          ·
            refine ⟨63545292929344502796396601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84727057239126003728528801 63545292929344502796396601)
            ·
              refine ⟨47658969697008377097297451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63545292929344502796396601 47658969697008377097297451)
              ·
                refine ⟨71488454545512565645946177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47658969697008377097297451 71488454545512565645946177)
                ·
                  refine ⟨53616340909134424234459633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71488454545512565645946177 53616340909134424234459633)
                  ·
                    refine ⟨40212255681850818175844725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53616340909134424234459633 40212255681850818175844725)
                    ·
                      refine ⟨3769898970173514203985443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40212255681850818175844725 3769898970173514203985443)
                      ·
                        rfl

theorem cell23_7341852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_7341852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341852 prefixEnd_7341852 := by exact prefixLift 7341852
  have htrace : WordTrace (prefixWord ++ tailWord_7341852) baseStart_7341852 baseEnd_7341852 := by
    simpa [prefixWord, tailWord_7341852, baseEnd_7341852] using wordTrace_append hprefix tailTrace_7341852
  have hstable : (prefixWord ++ tailWord_7341852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341852).length < 2 ^ (prefixWord ++ tailWord_7341852).sum := by decide
  have hdescent : baseEnd_7341852 < baseStart_7341852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341873 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 2, 1, 3]
def baseStart_7341873 : Nat := 118140960795 + 7341873 * 2 ^ 59
def prefixEnd_7341873 : Nat := 4983230072969 + 3 ^ 40 * 7341873 * 2
def baseEnd_7341873 : Nat := 3769909753267258621822847

theorem tailTrace_7341873 : CollatzResearch.WordTrace tailWord_7341873 prefixEnd_7341873 3769909753267258621822847 := by
  unfold tailWord_7341873
  simp only [CollatzResearch.WordTrace]
  refine ⟨267780107330655487926062273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178520071553770325284041515 267780107330655487926062273)
  ·
    refine ⟨200835080497991615944546705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267780107330655487926062273 200835080497991615944546705)
    ·
      refine ⟨150626310373493711958410029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200835080497991615944546705 150626310373493711958410029)
      ·
        refine ⟨56484866390060141984403761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150626310373493711958410029 56484866390060141984403761)
        ·
          refine ⟨42363649792545106488302821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56484866390060141984403761 42363649792545106488302821)
          ·
            refine ⟨7943184336102207466556779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42363649792545106488302821 7943184336102207466556779)
            ·
              refine ⟨11914776504153311199835169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943184336102207466556779 11914776504153311199835169)
              ·
                refine ⟨8936082378114983399876377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11914776504153311199835169 8936082378114983399876377)
                ·
                  refine ⟨6702061783586237549907283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8936082378114983399876377 6702061783586237549907283)
                  ·
                    refine ⟨10053092675379356324860925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6702061783586237549907283 10053092675379356324860925)
                    ·
                      refine ⟨3769909753267258621822847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10053092675379356324860925 3769909753267258621822847)
                      ·
                        rfl

theorem cell23_7341873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_7341873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341873 prefixEnd_7341873 := by exact prefixLift 7341873
  have htrace : WordTrace (prefixWord ++ tailWord_7341873) baseStart_7341873 baseEnd_7341873 := by
    simpa [prefixWord, tailWord_7341873, baseEnd_7341873] using wordTrace_append hprefix tailTrace_7341873
  have hstable : (prefixWord ++ tailWord_7341873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341873).length < 2 ^ (prefixWord ++ tailWord_7341873).sum := by decide
  have hdescent : baseEnd_7341873 < baseStart_7341873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341896 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 1, 4, 2]
def baseStart_7341896 : Nat := 118140960795 + 7341896 * 2 ^ 59
def prefixEnd_7341896 : Nat := 4983230072969 + 3 ^ 40 * 7341896 * 2
def baseEnd_7341896 : Nat := 3769921563322312031835241

theorem tailTrace_7341896 : CollatzResearch.WordTrace tailWord_7341896 prefixEnd_7341896 3769921563322312031835241 := by
  unfold tailWord_7341896
  simp only [CollatzResearch.WordTrace]
  refine ⟨133890473104786081427074771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178520630806381441902766361 133890473104786081427074771)
  ·
    refine ⟨200835709657179122140612157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133890473104786081427074771 200835709657179122140612157)
    ·
      refine ⟨75313391121442170802729559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200835709657179122140612157 75313391121442170802729559)
      ·
        refine ⟨112970086682163256204094339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75313391121442170802729559 112970086682163256204094339)
        ·
          refine ⟨169455130023244884306141509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112970086682163256204094339 169455130023244884306141509)
          ·
            refine ⟨31772836879358415807401533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169455130023244884306141509 31772836879358415807401533)
            ·
              refine ⟨11914813829759405927775575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31772836879358415807401533 11914813829759405927775575)
              ·
                refine ⟨17872220744639108891663363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11914813829759405927775575 17872220744639108891663363)
                ·
                  refine ⟨26808331116958663337495045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17872220744639108891663363 26808331116958663337495045)
                  ·
                    refine ⟨5026562084429749375780321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26808331116958663337495045 5026562084429749375780321)
                    ·
                      refine ⟨3769921563322312031835241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026562084429749375780321 3769921563322312031835241)
                      ·
                        rfl

theorem cell23_7341896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_7341896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341896 prefixEnd_7341896 := by exact prefixLift 7341896
  have htrace : WordTrace (prefixWord ++ tailWord_7341896) baseStart_7341896 baseEnd_7341896 := by
    simpa [prefixWord, tailWord_7341896, baseEnd_7341896] using wordTrace_append hprefix tailTrace_7341896
  have hstable : (prefixWord ++ tailWord_7341896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341896).length < 2 ^ (prefixWord ++ tailWord_7341896).sum := by decide
  have hdescent : baseEnd_7341896 < baseStart_7341896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341916 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_7341916 : Nat := 118140960795 + 7341916 * 2 ^ 59
def prefixEnd_7341916 : Nat := 4983230072969 + 3 ^ 40 * 7341916 * 2
def baseEnd_7341916 : Nat := 3769931832935401953585149

theorem tailTrace_7341916 : CollatzResearch.WordTrace tailWord_7341916 prefixEnd_7341916 3769931832935401953585149 := by
  unfold tailWord_7341916
  simp only [CollatzResearch.WordTrace]
  refine ⟨133890837834749853134938801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178521117112999804179918401 133890837834749853134938801)
  ·
    refine ⟨100418128376062389851204101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133890837834749853134938801 100418128376062389851204101)
    ·
      refine ⟨18828399070511698097100769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100418128376062389851204101 18828399070511698097100769)
      ·
        refine ⟨14121299302883773572825577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18828399070511698097100769 14121299302883773572825577)
        ·
          refine ⟨10590974477162830179619183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14121299302883773572825577 10590974477162830179619183)
          ·
            refine ⟨15886461715744245269428775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10590974477162830179619183 15886461715744245269428775)
            ·
              refine ⟨23829692573616367904143163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15886461715744245269428775 23829692573616367904143163)
              ·
                refine ⟨35744538860424551856214745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23829692573616367904143163 35744538860424551856214745)
                ·
                  refine ⟨26808404145318413892161059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35744538860424551856214745 26808404145318413892161059)
                  ·
                    refine ⟨40212606217977620838241589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26808404145318413892161059 40212606217977620838241589)
                    ·
                      refine ⟨3769931832935401953585149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40212606217977620838241589 3769931832935401953585149)
                      ·
                        rfl

theorem cell23_7341916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_7341916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341916 prefixEnd_7341916 := by exact prefixLift 7341916
  have htrace : WordTrace (prefixWord ++ tailWord_7341916) baseStart_7341916 baseEnd_7341916 := by
    simpa [prefixWord, tailWord_7341916, baseEnd_7341916] using wordTrace_append hprefix tailTrace_7341916
  have hstable : (prefixWord ++ tailWord_7341916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341916).length < 2 ^ (prefixWord ++ tailWord_7341916).sum := by decide
  have hdescent : baseEnd_7341916 < baseStart_7341916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341939 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 2, 5, 2]
def baseStart_7341939 : Nat := 118140960795 + 7341939 * 2 ^ 59
def prefixEnd_7341939 : Nat := 4983230072969 + 3 ^ 40 * 7341939 * 2
def baseEnd_7341939 : Nat := 3769943642990455363597543

theorem tailTrace_7341939 : CollatzResearch.WordTrace tailWord_7341939 prefixEnd_7341939 3769943642990455363597543 := by
  unfold tailWord_7341939
  simp only [CollatzResearch.WordTrace]
  refine ⟨267782514548416381197964871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178521676365610920798643247 267782514548416381197964871)
  ·
    refine ⟨401673771822624571796947307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267782514548416381197964871 401673771822624571796947307)
    ·
      refine ⟨602510657733936857695420961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401673771822624571796947307 602510657733936857695420961)
      ·
        refine ⟨451882993300452643271565721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602510657733936857695420961 451882993300452643271565721)
        ·
          refine ⟨338912244975339482453674291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451882993300452643271565721 338912244975339482453674291)
          ·
            refine ⟨508368367463009223680511437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338912244975339482453674291 508368367463009223680511437)
            ·
              refine ⟨190638137798628458880191789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508368367463009223680511437 190638137798628458880191789)
              ·
                refine ⟨71489301674485672080071921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190638137798628458880191789 71489301674485672080071921)
                ·
                  refine ⟨53616976255864254060053941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71489301674485672080071921 53616976255864254060053941)
                  ·
                    refine ⟨5026591523987273818130057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53616976255864254060053941 5026591523987273818130057)
                    ·
                      refine ⟨3769943642990455363597543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026591523987273818130057 3769943642990455363597543)
                      ·
                        rfl

theorem cell23_7341939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 5, 2].length) (baseStart_7341939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341939 prefixEnd_7341939 := by exact prefixLift 7341939
  have htrace : WordTrace (prefixWord ++ tailWord_7341939) baseStart_7341939 baseEnd_7341939 := by
    simpa [prefixWord, tailWord_7341939, baseEnd_7341939] using wordTrace_append hprefix tailTrace_7341939
  have hstable : (prefixWord ++ tailWord_7341939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341939).length < 2 ^ (prefixWord ++ tailWord_7341939).sum := by decide
  have hdescent : baseEnd_7341939 < baseStart_7341939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7341969 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_7341969 : Nat := 118140960795 + 7341969 * 2 ^ 59
def prefixEnd_7341969 : Nat := 4983230072969 + 3 ^ 40 * 7341969 * 2
def baseEnd_7341969 : Nat := 3769959047410090246222405

theorem tailTrace_7341969 : CollatzResearch.WordTrace tailWord_7341969 prefixEnd_7341969 3769959047410090246222405 := by
  unfold tailWord_7341969
  simp only [CollatzResearch.WordTrace]
  refine ⟨267783608738307696321556961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178522405825538464214371307 267783608738307696321556961)
  ·
    refine ⟨200837706553730772241167721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267783608738307696321556961 200837706553730772241167721)
    ·
      refine ⟨150628279915298079180875791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200837706553730772241167721 150628279915298079180875791)
      ·
        refine ⟨225942419872947118771313687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150628279915298079180875791 225942419872947118771313687)
        ·
          refine ⟨338913629809420678156970531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225942419872947118771313687 338913629809420678156970531)
          ·
            refine ⟨508370444714131017235455797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338913629809420678156970531 508370444714131017235455797)
            ·
              refine ⟨47659729191949782865823981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 508370444714131017235455797 47659729191949782865823981)
              ·
                refine ⟨17872398446981168574683993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47659729191949782865823981 17872398446981168574683993)
                ·
                  refine ⟨13404298835235876431012995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17872398446981168574683993 13404298835235876431012995)
                  ·
                    refine ⟨20106448252853814646519493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13404298835235876431012995 20106448252853814646519493)
                    ·
                      refine ⟨3769959047410090246222405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20106448252853814646519493 3769959047410090246222405)
                      ·
                        rfl

theorem cell23_7341969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_7341969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7341969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7341969 prefixEnd_7341969 := by exact prefixLift 7341969
  have htrace : WordTrace (prefixWord ++ tailWord_7341969) baseStart_7341969 baseEnd_7341969 := by
    simpa [prefixWord, tailWord_7341969, baseEnd_7341969] using wordTrace_append hprefix tailTrace_7341969
  have hstable : (prefixWord ++ tailWord_7341969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7341969).length < 2 ^ (prefixWord ++ tailWord_7341969).sum := by decide
  have hdescent : baseEnd_7341969 < baseStart_7341969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7341969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342009 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 6]
def baseStart_7342009 : Nat := 118140960795 + 7342009 * 2 ^ 59
def prefixEnd_7342009 : Nat := 4983230072969 + 3 ^ 40 * 7342009 * 2
def baseEnd_7342009 : Nat := 418886620737363343302469

theorem tailTrace_7342009 : CollatzResearch.WordTrace tailWord_7342009 prefixEnd_7342009 418886620737363343302469 := by
  unfold tailWord_7342009
  simp only [CollatzResearch.WordTrace]
  refine ⟨267785067658162783153013081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178523378438775188768675387 267785067658162783153013081)
  ·
    refine ⟨200838800743622087364759811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267785067658162783153013081 200838800743622087364759811)
    ·
      refine ⟨301258201115433131047139717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200838800743622087364759811 301258201115433131047139717)
      ·
        refine ⟨56485912709143712071338697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301258201115433131047139717 56485912709143712071338697)
        ·
          refine ⟨42364434531857784053504023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56485912709143712071338697 42364434531857784053504023)
          ·
            refine ⟨63546651797786676080256035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42364434531857784053504023 63546651797786676080256035)
            ·
              refine ⟨95319977696680014120384053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63546651797786676080256035 95319977696680014120384053)
              ·
                refine ⟨8936247909063751323786005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95319977696680014120384053 8936247909063751323786005)
                ·
                  refine ⟨418886620737363343302469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8936247909063751323786005 418886620737363343302469)
                  ·
                    rfl

theorem cell23_7342009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 6].length) (baseStart_7342009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342009 prefixEnd_7342009 := by exact prefixLift 7342009
  have htrace : WordTrace (prefixWord ++ tailWord_7342009) baseStart_7342009 baseEnd_7342009 := by
    simpa [prefixWord, tailWord_7342009, baseEnd_7342009] using wordTrace_append hprefix tailTrace_7342009
  have hstable : (prefixWord ++ tailWord_7342009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342009).length < 2 ^ (prefixWord ++ tailWord_7342009).sum := by decide
  have hdescent : baseEnd_7342009 < baseStart_7342009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342059 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 4]
def baseStart_7342059 : Nat := 118140960795 + 7342059 * 2 ^ 59
def prefixEnd_7342059 : Nat := 4983230072969 + 3 ^ 40 * 7342059 * 2
def baseEnd_7342059 : Nat := 3770005260668994894096991

theorem tailTrace_7342059 : CollatzResearch.WordTrace tailWord_7342059 prefixEnd_7342059 3770005260668994894096991 := by
  unfold tailWord_7342059
  simp only [CollatzResearch.WordTrace]
  refine ⟨267786891307981641692333231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178524594205321094461555487 267786891307981641692333231)
  ·
    refine ⟨401680336961972462538499847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267786891307981641692333231 401680336961972462538499847)
    ·
      refine ⟨602520505442958693807749771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401680336961972462538499847 602520505442958693807749771)
      ·
        refine ⟨903780758164438040711624657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602520505442958693807749771 903780758164438040711624657)
        ·
          refine ⟨677835568623328530533718493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903780758164438040711624657 677835568623328530533718493)
          ·
            refine ⟨254188338233748198950144435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 677835568623328530533718493 254188338233748198950144435)
            ·
              refine ⟨381282507350622298425216653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254188338233748198950144435 381282507350622298425216653)
              ·
                refine ⟨142980940256483361909456245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381282507350622298425216653 142980940256483361909456245)
                ·
                  refine ⟨13404463149045315179011523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142980940256483361909456245 13404463149045315179011523)
                  ·
                    refine ⟨20106694723567972768517285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13404463149045315179011523 20106694723567972768517285)
                    ·
                      refine ⟨3770005260668994894096991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20106694723567972768517285 3770005260668994894096991)
                      ·
                        rfl

theorem cell23_7342059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 4].length) (baseStart_7342059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342059 prefixEnd_7342059 := by exact prefixLift 7342059
  have htrace : WordTrace (prefixWord ++ tailWord_7342059) baseStart_7342059 baseEnd_7342059 := by
    simpa [prefixWord, tailWord_7342059, baseEnd_7342059] using wordTrace_append hprefix tailTrace_7342059
  have hstable : (prefixWord ++ tailWord_7342059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342059).length < 2 ^ (prefixWord ++ tailWord_7342059).sum := by decide
  have hdescent : baseEnd_7342059 < baseStart_7342059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342076 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 2, 6, 2]
def baseStart_7342076 : Nat := 118140960795 + 7342076 * 2 ^ 59
def prefixEnd_7342076 : Nat := 4983230072969 + 3 ^ 40 * 7342076 * 2
def baseEnd_7342076 : Nat := 3770013989840121327584413

theorem tailTrace_7342076 : CollatzResearch.WordTrace tailWord_7342076 prefixEnd_7342076 3770013989840121327584413 := by
  unfold tailWord_7342076
  simp only [CollatzResearch.WordTrace]
  refine ⟨133893755674460026797851041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178525007565946702397134721 133893755674460026797851041)
  ·
    refine ⟨100420316755845020098388281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133893755674460026797851041 100420316755845020098388281)
    ·
      refine ⟨75315237566883765073791211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100420316755845020098388281 75315237566883765073791211)
      ·
        refine ⟨112972856350325647610686817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75315237566883765073791211 112972856350325647610686817)
        ·
          refine ⟨84729642262744235708015113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112972856350325647610686817 84729642262744235708015113)
          ·
            refine ⟨63547231697058176781011335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84729642262744235708015113 63547231697058176781011335)
            ·
              refine ⟨95320847545587265171517003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63547231697058176781011335 95320847545587265171517003)
              ·
                refine ⟨142981271318380897757275505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95320847545587265171517003 142981271318380897757275505)
                ·
                  refine ⟨107235953488785673317956629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142981271318380897757275505 107235953488785673317956629)
                  ·
                    refine ⟨5026685319786828436779217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107235953488785673317956629 5026685319786828436779217)
                    ·
                      refine ⟨3770013989840121327584413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026685319786828436779217 3770013989840121327584413)
                      ·
                        rfl

theorem cell23_7342076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_7342076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342076 prefixEnd_7342076 := by exact prefixLift 7342076
  have htrace : WordTrace (prefixWord ++ tailWord_7342076) baseStart_7342076 baseEnd_7342076 := by
    simpa [prefixWord, tailWord_7342076, baseEnd_7342076] using wordTrace_append hprefix tailTrace_7342076
  have hstable : (prefixWord ++ tailWord_7342076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342076).length < 2 ^ (prefixWord ++ tailWord_7342076).sum := by decide
  have hdescent : baseEnd_7342076 < baseStart_7342076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342079 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 3]
def baseStart_7342079 : Nat := 118140960795 + 7342079 * 2 ^ 59
def prefixEnd_7342079 : Nat := 4983230072969 + 3 ^ 40 * 7342079 * 2
def baseEnd_7342079 : Nat := 3770015530282084815846899

theorem tailTrace_7342079 : CollatzResearch.WordTrace tailWord_7342079 prefixEnd_7342079 3770015530282084815846899 := by
  unfold tailWord_7342079
  simp only [CollatzResearch.WordTrace]
  refine ⟨267787620767909185108061291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178525080511939456738707527 267787620767909185108061291)
  ·
    refine ⟨401681431151863777662091937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267787620767909185108061291 401681431151863777662091937)
    ·
      refine ⟨301261073363897833246568953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401681431151863777662091937 301261073363897833246568953)
      ·
        refine ⟨225945805022923374934926715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301261073363897833246568953 225945805022923374934926715)
        ·
          refine ⟨338918707534385062402390073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225945805022923374934926715 338918707534385062402390073)
          ·
            refine ⟨254189030650788796801792555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338918707534385062402390073 254189030650788796801792555)
            ·
              refine ⟨381283545976183195202688833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254189030650788796801792555 381283545976183195202688833)
              ·
                refine ⟨285962659482137396402016625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381283545976183195202688833 285962659482137396402016625)
                ·
                  refine ⟨214471994611603047301512469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285962659482137396402016625 214471994611603047301512469)
                  ·
                    refine ⟨10053374747418892842258397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214471994611603047301512469 10053374747418892842258397)
                    ·
                      refine ⟨3770015530282084815846899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10053374747418892842258397 3770015530282084815846899)
                      ·
                        rfl

theorem cell23_7342079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_7342079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342079 prefixEnd_7342079 := by exact prefixLift 7342079
  have htrace : WordTrace (prefixWord ++ tailWord_7342079) baseStart_7342079 baseEnd_7342079 := by
    simpa [prefixWord, tailWord_7342079, baseEnd_7342079] using wordTrace_append hprefix tailTrace_7342079
  have hstable : (prefixWord ++ tailWord_7342079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342079).length < 2 ^ (prefixWord ++ tailWord_7342079).sum := by decide
  have hdescent : baseEnd_7342079 < baseStart_7342079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342087 : List Nat := [1, 1, 4, 3, 1, 4, 1, 3, 1, 1, 3]
def baseStart_7342087 : Nat := 118140960795 + 7342087 * 2 ^ 59
def prefixEnd_7342087 : Nat := 4983230072969 + 3 ^ 40 * 7342087 * 2
def baseEnd_7342087 : Nat := 3770019638127320784546863

theorem tailTrace_7342087 : CollatzResearch.WordTrace tailWord_7342087 prefixEnd_7342087 3770019638127320784546863 := by
  unfold tailWord_7342087
  simp only [CollatzResearch.WordTrace]
  refine ⟨267787912551880202474352515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178525275034586801649568343 267787912551880202474352515)
  ·
    refine ⟨401681868827820303711528773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267787912551880202474352515 401681868827820303711528773)
    ·
      refine ⟨75315350405216306945911645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401681868827820303711528773 75315350405216306945911645)
      ·
        refine ⟨28243256401956115104716867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75315350405216306945911645 28243256401956115104716867)
        ·
          refine ⟨42364884602934172657075301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28243256401956115104716867 42364884602934172657075301)
          ·
            refine ⟨7943415863050157373201619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42364884602934172657075301 7943415863050157373201619)
            ·
              refine ⟨11915123794575236059802429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943415863050157373201619 11915123794575236059802429)
              ·
                refine ⟨4468171422965713522425911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11915123794575236059802429 4468171422965713522425911)
                ·
                  refine ⟨6702257134448570283638867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468171422965713522425911 6702257134448570283638867)
                  ·
                    refine ⟨10053385701672855425458301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6702257134448570283638867 10053385701672855425458301)
                    ·
                      refine ⟨3770019638127320784546863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10053385701672855425458301 3770019638127320784546863)
                      ·
                        rfl

theorem cell23_7342087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_7342087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342087 prefixEnd_7342087 := by exact prefixLift 7342087
  have htrace : WordTrace (prefixWord ++ tailWord_7342087) baseStart_7342087 baseEnd_7342087 := by
    simpa [prefixWord, tailWord_7342087, baseEnd_7342087] using wordTrace_append hprefix tailTrace_7342087
  have hstable : (prefixWord ++ tailWord_7342087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342087).length < 2 ^ (prefixWord ++ tailWord_7342087).sum := by decide
  have hdescent : baseEnd_7342087 < baseStart_7342087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342130 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_7342130 : Nat := 118140960795 + 7342130 * 2 ^ 59
def prefixEnd_7342130 : Nat := 4983230072969 + 3 ^ 40 * 7342130 * 2
def baseEnd_7342130 : Nat := 3770041717795464116309165

theorem tailTrace_7342130 : CollatzResearch.WordTrace tailWord_7342130 prefixEnd_7342130 3770041717795464116309165 := by
  unfold tailWord_7342130
  simp only [CollatzResearch.WordTrace]
  refine ⟨66947370222681105204541961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178526320593816280545445229 66947370222681105204541961)
  ·
    refine ⟨50210527667010828903406471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66947370222681105204541961 50210527667010828903406471)
    ·
      refine ⟨75315791500516243355109707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50210527667010828903406471 75315791500516243355109707)
      ·
        refine ⟨112973687250774365032664561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75315791500516243355109707 112973687250774365032664561)
        ·
          refine ⟨84730265438080773774498421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112973687250774365032664561 84730265438080773774498421)
          ·
            refine ⟨7943462384820072541359227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84730265438080773774498421 7943462384820072541359227)
            ·
              refine ⟨11915193577230108812038841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943462384820072541359227 11915193577230108812038841)
              ·
                refine ⟨8936395182922581609029131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11915193577230108812038841 8936395182922581609029131)
                ·
                  refine ⟨13404592774383872413543697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8936395182922581609029131 13404592774383872413543697)
                  ·
                    refine ⟨10053444580787904310157773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13404592774383872413543697 10053444580787904310157773)
                    ·
                      refine ⟨3770041717795464116309165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10053444580787904310157773 3770041717795464116309165)
                      ·
                        rfl

theorem cell23_7342130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_7342130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342130 prefixEnd_7342130 := by exact prefixLift 7342130
  have htrace : WordTrace (prefixWord ++ tailWord_7342130) baseStart_7342130 baseEnd_7342130 := by
    simpa [prefixWord, tailWord_7342130, baseEnd_7342130] using wordTrace_append hprefix tailTrace_7342130
  have hstable : (prefixWord ++ tailWord_7342130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342130).length < 2 ^ (prefixWord ++ tailWord_7342130).sum := by decide
  have hdescent : baseEnd_7342130 < baseStart_7342130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342159 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 4, 6]
def baseStart_7342159 : Nat := 118140960795 + 7342159 * 2 ^ 59
def prefixEnd_7342159 : Nat := 4983230072969 + 3 ^ 40 * 7342159 * 2
def baseEnd_7342159 : Nat := 1256685536244814834282177

theorem tailTrace_7342159 : CollatzResearch.WordTrace tailWord_7342159 prefixEnd_7342159 1256685536244814834282177 := by
  unfold tailWord_7342159
  simp only [CollatzResearch.WordTrace]
  refine ⟨267790538607619358770973531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178527025738412905847315687 267790538607619358770973531)
  ·
    refine ⟨401685807911429038156460297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267790538607619358770973531 401685807911429038156460297)
    ·
      refine ⟨301264355933571778617345223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401685807911429038156460297 301264355933571778617345223)
      ·
        refine ⟨451896533900357667926017835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301264355933571778617345223 451896533900357667926017835)
        ·
          refine ⟨677844800850536501889026753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451896533900357667926017835 677844800850536501889026753)
          ·
            refine ⟨508383600637902376416770065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677844800850536501889026753 508383600637902376416770065)
            ·
              refine ⟨381287700478426782312577549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508383600637902376416770065 381287700478426782312577549)
              ·
                refine ⟨142982887679410043367216581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381287700478426782312577549 142982887679410043367216581)
                ·
                  refine ⟨26809291439889383131353109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142982887679410043367216581 26809291439889383131353109)
                  ·
                    refine ⟨1256685536244814834282177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26809291439889383131353109 1256685536244814834282177)
                    ·
                      rfl

theorem cell23_7342159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_7342159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342159 prefixEnd_7342159 := by exact prefixLift 7342159
  have htrace : WordTrace (prefixWord ++ tailWord_7342159) baseStart_7342159 baseEnd_7342159 := by
    simpa [prefixWord, tailWord_7342159, baseEnd_7342159] using wordTrace_append hprefix tailTrace_7342159
  have hstable : (prefixWord ++ tailWord_7342159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342159).length < 2 ^ (prefixWord ++ tailWord_7342159).sum := by decide
  have hdescent : baseEnd_7342159 < baseStart_7342159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342176 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 2, 6]
def baseStart_7342176 : Nat := 118140960795 + 7342176 * 2 ^ 59
def prefixEnd_7342176 : Nat := 4983230072969 + 3 ^ 40 * 7342176 * 2
def baseEnd_7342176 : Nat := 1256688445968523645444651

theorem tailTrace_7342176 : CollatzResearch.WordTrace tailWord_7342176 prefixEnd_7342176 1256688445968523645444651 := by
  unfold tailWord_7342176
  simp only [CollatzResearch.WordTrace]
  refine ⟨133895579324278885337171191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178527439099038513782894921 133895579324278885337171191)
  ·
    refine ⟨200843368986418328005756787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133895579324278885337171191 200843368986418328005756787)
    ·
      refine ⟨301265053479627492008635181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200843368986418328005756787 301265053479627492008635181)
      ·
        refine ⟨112974395054860309503238193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301265053479627492008635181 112974395054860309503238193)
        ·
          refine ⟨84730796291145232127428645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112974395054860309503238193 84730796291145232127428645)
          ·
            refine ⟨15887024304589731023892871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84730796291145232127428645 15887024304589731023892871)
            ·
              refine ⟨23830536456884596535839307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15887024304589731023892871 23830536456884596535839307)
              ·
                refine ⟨35745804685326894803758961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23830536456884596535839307 35745804685326894803758961)
                ·
                  refine ⟨26809353513995171102819221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35745804685326894803758961 26809353513995171102819221)
                  ·
                    refine ⟨1256688445968523645444651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26809353513995171102819221 1256688445968523645444651)
                    ·
                      rfl

theorem cell23_7342176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_7342176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342176 prefixEnd_7342176 := by exact prefixLift 7342176
  have htrace : WordTrace (prefixWord ++ tailWord_7342176) baseStart_7342176 baseEnd_7342176 := by
    simpa [prefixWord, tailWord_7342176, baseEnd_7342176] using wordTrace_append hprefix tailTrace_7342176
  have hstable : (prefixWord ++ tailWord_7342176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342176).length < 2 ^ (prefixWord ++ tailWord_7342176).sum := by decide
  have hdescent : baseEnd_7342176 < baseStart_7342176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342234 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2]
def baseStart_7342234 : Nat := 118140960795 + 7342234 * 2 ^ 59
def prefixEnd_7342234 : Nat := 4983230072969 + 3 ^ 40 * 7342234 * 2
def baseEnd_7342234 : Nat := 3770095119783531709408687

theorem tailTrace_7342234 : CollatzResearch.WordTrace tailWord_7342234 prefixEnd_7342234 3770095119783531709408687 := by
  unfold tailWord_7342234
  simp only [CollatzResearch.WordTrace]
  refine ⟨66948318520586911644988439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178528849388231764386635837 66948318520586911644988439)
  ·
    refine ⟨100422477780880367467482659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66948318520586911644988439 100422477780880367467482659)
    ·
      refine ⟨150633716671320551201223989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100422477780880367467482659 150633716671320551201223989)
      ·
        refine ⟨14121910937936301675114749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150633716671320551201223989 14121910937936301675114749)
        ·
          refine ⟨5295716601726113128168031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14121910937936301675114749 5295716601726113128168031)
          ·
            refine ⟨7943574902589169692252047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295716601726113128168031 7943574902589169692252047)
            ·
              refine ⟨11915362353883754538378071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943574902589169692252047 11915362353883754538378071)
              ·
                refine ⟨17873043530825631807567107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11915362353883754538378071 17873043530825631807567107)
                ·
                  refine ⟨26809565296238447711350661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17873043530825631807567107 26809565296238447711350661)
                  ·
                    refine ⟨5026793493044708945878249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26809565296238447711350661 5026793493044708945878249)
                    ·
                      refine ⟨3770095119783531709408687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026793493044708945878249 3770095119783531709408687)
                      ·
                        rfl

theorem cell23_7342234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_7342234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342234 prefixEnd_7342234 := by exact prefixLift 7342234
  have htrace : WordTrace (prefixWord ++ tailWord_7342234) baseStart_7342234 baseEnd_7342234 := by
    simpa [prefixWord, tailWord_7342234, baseEnd_7342234] using wordTrace_append hprefix tailTrace_7342234
  have hstable : (prefixWord ++ tailWord_7342234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342234).length < 2 ^ (prefixWord ++ tailWord_7342234).sum := by decide
  have hdescent : baseEnd_7342234 < baseStart_7342234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342236 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_7342236 : Nat := 118140960795 + 7342236 * 2 ^ 59
def prefixEnd_7342236 : Nat := 4983230072969 + 3 ^ 40 * 7342236 * 2
def baseEnd_7342236 : Nat := 1256698715581613567194559

theorem tailTrace_7342236 : CollatzResearch.WordTrace tailWord_7342236 prefixEnd_7342236 1256698715581613567194559 := by
  unfold tailWord_7342236
  simp only [CollatzResearch.WordTrace]
  refine ⟨133896673514170200460763281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178528898018893600614351041 133896673514170200460763281)
  ·
    refine ⟨100422505135627650345572461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133896673514170200460763281 100422505135627650345572461)
    ·
      refine ⟨37658439425860368879589673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100422505135627650345572461 37658439425860368879589673)
      ·
        refine ⟨28243829569395276659692255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37658439425860368879589673 28243829569395276659692255)
        ·
          refine ⟨42365744354092914989538383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28243829569395276659692255 42365744354092914989538383)
          ·
            refine ⟨63548616531139372484307575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42365744354092914989538383 63548616531139372484307575)
            ·
              refine ⟨95322924796709058726461363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63548616531139372484307575 95322924796709058726461363)
              ·
                refine ⟨142984387195063588089692045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95322924796709058726461363 142984387195063588089692045)
                ·
                  refine ⟨53619145198148845533634517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142984387195063588089692045 53619145198148845533634517)
                  ·
                    refine ⟨1256698715581613567194559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53619145198148845533634517 1256698715581613567194559)
                    ·
                      rfl

theorem cell23_7342236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_7342236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342236 prefixEnd_7342236 := by exact prefixLift 7342236
  have htrace : WordTrace (prefixWord ++ tailWord_7342236) baseStart_7342236 baseEnd_7342236 := by
    simpa [prefixWord, tailWord_7342236, baseEnd_7342236] using wordTrace_append hprefix tailTrace_7342236
  have hstable : (prefixWord ++ tailWord_7342236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342236).length < 2 ^ (prefixWord ++ tailWord_7342236).sum := by decide
  have hdescent : baseEnd_7342236 < baseStart_7342236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342253 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_7342253 : Nat := 118140960795 + 7342253 * 2 ^ 59
def prefixEnd_7342253 : Nat := 4983230072969 + 3 ^ 40 * 7342253 * 2
def baseEnd_7342253 : Nat := 1256701625305322378357033

theorem tailTrace_7342253 : CollatzResearch.WordTrace tailWord_7342253 prefixEnd_7342253 1256701625305322378357033 := by
  unfold tailWord_7342253
  simp only [CollatzResearch.WordTrace]
  refine ⟨267793967069278812824895413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178529311379519208549930275 267793967069278812824895413)
  ·
    refine ⟨25105684412744888702333945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267793967069278812824895413 25105684412744888702333945)
    ·
      refine ⟨18829263309558666526750459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25105684412744888702333945 18829263309558666526750459)
      ·
        refine ⟨28243894964337999790125689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18829263309558666526750459 28243894964337999790125689)
        ·
          refine ⟨21182921223253499842594267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28243894964337999790125689 21182921223253499842594267)
          ·
            refine ⟨31774381834880249763891401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21182921223253499842594267 31774381834880249763891401)
            ·
              refine ⟨23830786376160187322918551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31774381834880249763891401 23830786376160187322918551)
              ·
                refine ⟨35746179564240280984377827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23830786376160187322918551 35746179564240280984377827)
                ·
                  refine ⟨53619269346360421476566741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35746179564240280984377827 53619269346360421476566741)
                  ·
                    refine ⟨1256701625305322378357033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53619269346360421476566741 1256701625305322378357033)
                    ·
                      rfl

theorem cell23_7342253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_7342253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342253 prefixEnd_7342253 := by exact prefixLift 7342253
  have htrace : WordTrace (prefixWord ++ tailWord_7342253) baseStart_7342253 baseEnd_7342253 := by
    simpa [prefixWord, tailWord_7342253, baseEnd_7342253] using wordTrace_append hprefix tailTrace_7342253
  have hstable : (prefixWord ++ tailWord_7342253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342253).length < 2 ^ (prefixWord ++ tailWord_7342253).sum := by decide
  have hdescent : baseEnd_7342253 < baseStart_7342253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342257 : List Nat := [1, 2, 2, 5, 2, 2, 1, 3, 5]
def baseStart_7342257 : Nat := 118140960795 + 7342257 * 2 ^ 59
def prefixEnd_7342257 : Nat := 4983230072969 + 3 ^ 40 * 7342257 * 2
def baseEnd_7342257 : Nat := 418900769982065013269009

theorem tailTrace_7342257 : CollatzResearch.WordTrace tailWord_7342257 prefixEnd_7342257 418900769982065013269009 := by
  unfold tailWord_7342257
  simp only [CollatzResearch.WordTrace]
  refine ⟨267794112961264321508041025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178529408640842881005360683 267794112961264321508041025)
  ·
    refine ⟨200845584720948241131030769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267794112961264321508041025 200845584720948241131030769)
    ·
      refine ⟨150634188540711180848273077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200845584720948241131030769 150634188540711180848273077)
      ·
        refine ⟨14121955175691673204525601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150634188540711180848273077 14121955175691673204525601)
        ·
          refine ⟨10591466381768754903394201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14121955175691673204525601 10591466381768754903394201)
          ·
            refine ⟨7943599786326566177545651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10591466381768754903394201 7943599786326566177545651)
            ·
              refine ⟨11915399679489849266318477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943599786326566177545651 11915399679489849266318477)
              ·
                refine ⟨4468274879808693474869429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11915399679489849266318477 4468274879808693474869429)
                ·
                  refine ⟨418900769982065013269009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4468274879808693474869429 418900769982065013269009)
                  ·
                    rfl

theorem cell23_7342257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 5].length) (baseStart_7342257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342257 prefixEnd_7342257 := by exact prefixLift 7342257
  have htrace : WordTrace (prefixWord ++ tailWord_7342257) baseStart_7342257 baseEnd_7342257 := by
    simpa [prefixWord, tailWord_7342257, baseEnd_7342257] using wordTrace_append hprefix tailTrace_7342257
  have hstable : (prefixWord ++ tailWord_7342257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342257).length < 2 ^ (prefixWord ++ tailWord_7342257).sum := by decide
  have hdescent : baseEnd_7342257 < baseStart_7342257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342270 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_7342270 : Nat := 118140960795 + 7342270 * 2 ^ 59
def prefixEnd_7342270 : Nat := 4983230072969 + 3 ^ 40 * 7342270 * 2
def baseEnd_7342270 : Nat := 1256704535029031189519507

theorem tailTrace_7342270 : CollatzResearch.WordTrace tailWord_7342270 prefixEnd_7342270 1256704535029031189519507 := by
  unfold tailWord_7342270
  simp only [CollatzResearch.WordTrace]
  refine ⟨33474323388777153091033033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178529724740144816485509509 33474323388777153091033033)
  ·
    refine ⟨25105742541582864818274775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33474323388777153091033033 25105742541582864818274775)
    ·
      refine ⟨37658613812374297227412163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25105742541582864818274775 37658613812374297227412163)
      ·
        refine ⟨56487920718561445841118245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37658613812374297227412163 56487920718561445841118245)
        ·
          refine ⟨10591485134730271095209671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56487920718561445841118245 10591485134730271095209671)
          ·
            refine ⟨15887227702095406642814507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10591485134730271095209671 15887227702095406642814507)
            ·
              refine ⟨23830841553143109964221761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15887227702095406642814507 23830841553143109964221761)
              ·
                refine ⟨17873131164857332473166321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23830841553143109964221761 17873131164857332473166321)
                ·
                  refine ⟨13404848373642999354874741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17873131164857332473166321 13404848373642999354874741)
                  ·
                    refine ⟨1256704535029031189519507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13404848373642999354874741 1256704535029031189519507)
                    ·
                      rfl

theorem cell23_7342270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_7342270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342270 prefixEnd_7342270 := by exact prefixLift 7342270
  have htrace : WordTrace (prefixWord ++ tailWord_7342270) baseStart_7342270 baseEnd_7342270 := by
    simpa [prefixWord, tailWord_7342270, baseEnd_7342270] using wordTrace_append hprefix tailTrace_7342270
  have hstable : (prefixWord ++ tailWord_7342270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342270).length < 2 ^ (prefixWord ++ tailWord_7342270).sum := by decide
  have hdescent : baseEnd_7342270 < baseStart_7342270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342307 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7342307 : Nat := 118140960795 + 7342307 * 2 ^ 59
def prefixEnd_7342307 : Nat := 4983230072969 + 3 ^ 40 * 7342307 * 2
def baseEnd_7342307 : Nat := 3770132603871309923795851

theorem tailTrace_7342307 : CollatzResearch.WordTrace tailWord_7342307 prefixEnd_7342307 3770132603871309923795851 := by
  unfold tailWord_7342307
  simp only [CollatzResearch.WordTrace]
  refine ⟨267795936611083180047361175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178530624407388786698240783 267795936611083180047361175)
  ·
    refine ⟨401693904916624770071041763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267795936611083180047361175 401693904916624770071041763)
    ·
      refine ⟨602540857374937155106562645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401693904916624770071041763 602540857374937155106562645)
      ·
        refine ⟨7061025672362544786405031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 602540857374937155106562645 7061025672362544786405031)
        ·
          refine ⟨10591538508543817179607547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7061025672362544786405031 10591538508543817179607547)
          ·
            refine ⟨15887307762815725769411321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10591538508543817179607547 15887307762815725769411321)
            ·
              refine ⟨11915480822111794327058491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15887307762815725769411321 11915480822111794327058491)
              ·
                refine ⟨17873221233167691490587737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11915480822111794327058491 17873221233167691490587737)
                ·
                  refine ⟨13404915924875768617940803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17873221233167691490587737 13404915924875768617940803)
                  ·
                    refine ⟨20107373887313652926911205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13404915924875768617940803 20107373887313652926911205)
                    ·
                      refine ⟨3770132603871309923795851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20107373887313652926911205 3770132603871309923795851)
                      ·
                        rfl

theorem cell23_7342307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7342307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342307 prefixEnd_7342307 := by exact prefixLift 7342307
  have htrace : WordTrace (prefixWord ++ tailWord_7342307) baseStart_7342307 baseEnd_7342307 := by
    simpa [prefixWord, tailWord_7342307, baseEnd_7342307] using wordTrace_append hprefix tailTrace_7342307
  have hstable : (prefixWord ++ tailWord_7342307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342307).length < 2 ^ (prefixWord ++ tailWord_7342307).sum := by decide
  have hdescent : baseEnd_7342307 < baseStart_7342307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342350 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2]
def baseStart_7342350 : Nat := 118140960795 + 7342350 * 2 ^ 59
def prefixEnd_7342350 : Nat := 4983230072969 + 3 ^ 40 * 7342350 * 2
def baseEnd_7342350 : Nat := 3770154683539453255558153

theorem tailTrace_7342350 : CollatzResearch.WordTrace tailWord_7342350 prefixEnd_7342350 3770154683539453255558153 := by
  unfold tailWord_7342350
  simp only [CollatzResearch.WordTrace]
  refine ⟨33474688118740924798897063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178531669966618265594117669 33474688118740924798897063)
  ·
    refine ⟨50212032178111387198345595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33474688118740924798897063 50212032178111387198345595)
    ·
      refine ⟨75318048267167080797518393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50212032178111387198345595 75318048267167080797518393)
      ·
        refine ⟨56488536200375310598138795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75318048267167080797518393 56488536200375310598138795)
        ·
          refine ⟨84732804300562965897208193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56488536200375310598138795 84732804300562965897208193)
          ·
            refine ⟨63549603225422224422906145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84732804300562965897208193 63549603225422224422906145)
            ·
              refine ⟨47662202419066668317179609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63549603225422224422906145 47662202419066668317179609)
              ·
                refine ⟨35746651814300001237884707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47662202419066668317179609 35746651814300001237884707)
                ·
                  refine ⟨53619977721450001856827061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35746651814300001237884707 53619977721450001856827061)
                  ·
                    refine ⟨5026872911385937674077537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53619977721450001856827061 5026872911385937674077537)
                    ·
                      refine ⟨3770154683539453255558153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026872911385937674077537 3770154683539453255558153)
                      ·
                        rfl

theorem cell23_7342350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_7342350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342350 prefixEnd_7342350 := by exact prefixLift 7342350
  have htrace : WordTrace (prefixWord ++ tailWord_7342350) baseStart_7342350 baseEnd_7342350 := by
    simpa [prefixWord, tailWord_7342350, baseEnd_7342350] using wordTrace_append hprefix tailTrace_7342350
  have hstable : (prefixWord ++ tailWord_7342350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342350).length < 2 ^ (prefixWord ++ tailWord_7342350).sum := by decide
  have hdescent : baseEnd_7342350 < baseStart_7342350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342363 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 4]
def baseStart_7342363 : Nat := 118140960795 + 7342363 * 2 ^ 59
def prefixEnd_7342363 : Nat := 4983230072969 + 3 ^ 40 * 7342363 * 2
def baseEnd_7342363 : Nat := 3770161358787961704695593

theorem tailTrace_7342363 : CollatzResearch.WordTrace tailWord_7342363 prefixEnd_7342363 3770161358787961704695593 := by
  unfold tailWord_7342363
  simp only [CollatzResearch.WordTrace]
  refine ⟨267797979098880301611399743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178531986065920201074266495 267797979098880301611399743)
  ·
    refine ⟨401696968648320452417099615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267797979098880301611399743 401696968648320452417099615)
    ·
      refine ⟨602545452972480678625649423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401696968648320452417099615 602545452972480678625649423)
      ·
        refine ⟨903818179458721017938474135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602545452972480678625649423 903818179458721017938474135)
        ·
          refine ⟨1355727269188081526907711203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903818179458721017938474135 1355727269188081526907711203)
          ·
            refine ⟨2033590903782122290361566805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355727269188081526907711203 2033590903782122290361566805)
            ·
              refine ⟨23831143403696745590174611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2033590903782122290361566805 23831143403696745590174611)
              ·
                refine ⟨35746715105545118385261917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23831143403696745590174611 35746715105545118385261917)
                ·
                  refine ⟨13405018164579419394473219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35746715105545118385261917 13405018164579419394473219)
                  ·
                    refine ⟨20107527246869129091709829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13405018164579419394473219 20107527246869129091709829)
                    ·
                      refine ⟨3770161358787961704695593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20107527246869129091709829 3770161358787961704695593)
                      ·
                        rfl

theorem cell23_7342363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 4].length) (baseStart_7342363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342363 prefixEnd_7342363 := by exact prefixLift 7342363
  have htrace : WordTrace (prefixWord ++ tailWord_7342363) baseStart_7342363 baseEnd_7342363 := by
    simpa [prefixWord, tailWord_7342363, baseEnd_7342363] using wordTrace_append hprefix tailTrace_7342363
  have hstable : (prefixWord ++ tailWord_7342363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342363).length < 2 ^ (prefixWord ++ tailWord_7342363).sum := by decide
  have hdescent : baseEnd_7342363 < baseStart_7342363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342367 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 2, 3, 2]
def baseStart_7342367 : Nat := 118140960795 + 7342367 * 2 ^ 59
def prefixEnd_7342367 : Nat := 4983230072969 + 3 ^ 40 * 7342367 * 2
def baseEnd_7342367 : Nat := 3770163412710579689045575

theorem tailTrace_7342367 : CollatzResearch.WordTrace tailWord_7342367 prefixEnd_7342367 3770163412710579689045575 := by
  unfold tailWord_7342367
  simp only [CollatzResearch.WordTrace]
  refine ⟨267798124990865810294545355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178532083327243873529696903 267798124990865810294545355)
  ·
    refine ⟨401697187486298715441818033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267798124990865810294545355 401697187486298715441818033)
    ·
      refine ⟨301272890614724036581363525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401697187486298715441818033 301272890614724036581363525)
      ·
        refine ⟨56488666990260756859005661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301272890614724036581363525 56488666990260756859005661)
        ·
          refine ⟨21183250121347783822127123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56488666990260756859005661 21183250121347783822127123)
          ·
            refine ⟨31774875182021675733190685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21183250121347783822127123 31774875182021675733190685)
            ·
              refine ⟨11915578193258128399946507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31774875182021675733190685 11915578193258128399946507)
              ·
                refine ⟨17873367289887192599919761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11915578193258128399946507 17873367289887192599919761)
                ·
                  refine ⟨13405025467415394449939821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17873367289887192599919761 13405025467415394449939821)
                  ·
                    refine ⟨5026884550280772918727433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13405025467415394449939821 5026884550280772918727433)
                    ·
                      refine ⟨3770163412710579689045575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026884550280772918727433 3770163412710579689045575)
                      ·
                        rfl

theorem cell23_7342367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_7342367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342367 prefixEnd_7342367 := by exact prefixLift 7342367
  have htrace : WordTrace (prefixWord ++ tailWord_7342367) baseStart_7342367 baseEnd_7342367 := by
    simpa [prefixWord, tailWord_7342367, baseEnd_7342367] using wordTrace_append hprefix tailTrace_7342367
  have hstable : (prefixWord ++ tailWord_7342367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342367).length < 2 ^ (prefixWord ++ tailWord_7342367).sum := by decide
  have hdescent : baseEnd_7342367 < baseStart_7342367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342407 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 2, 4]
def baseStart_7342407 : Nat := 118140960795 + 7342407 * 2 ^ 59
def prefixEnd_7342407 : Nat := 4983230072969 + 3 ^ 40 * 7342407 * 2
def baseEnd_7342407 : Nat := 1256727983978919844181797

theorem tailTrace_7342407 : CollatzResearch.WordTrace tailWord_7342407 prefixEnd_7342407 1256727983978919844181797 := by
  unfold tailWord_7342407
  simp only [CollatzResearch.WordTrace]
  refine ⟨267799583910720897126001475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178533055940480598084000983 267799583910720897126001475)
  ·
    refine ⟨401699375866081345689002213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267799583910720897126001475 401699375866081345689002213)
    ·
      refine ⟨75318632974890252316687915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401699375866081345689002213 75318632974890252316687915)
      ·
        refine ⟨112977949462335378475031873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75318632974890252316687915 112977949462335378475031873)
        ·
          refine ⟨84733462096751533856273905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112977949462335378475031873 84733462096751533856273905)
          ·
            refine ⟨63550096572563650392205429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84733462096751533856273905 63550096572563650392205429)
            ·
              refine ⟨5957821553677842224269259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63550096572563650392205429 5957821553677842224269259)
              ·
                refine ⟨8936732330516763336403889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5957821553677842224269259 8936732330516763336403889)
                ·
                  refine ⟨6702549247887572502302917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8936732330516763336403889 6702549247887572502302917)
                  ·
                    refine ⟨1256727983978919844181797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6702549247887572502302917 1256727983978919844181797)
                    ·
                      rfl

theorem cell23_7342407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_7342407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342407 prefixEnd_7342407 := by exact prefixLift 7342407
  have htrace : WordTrace (prefixWord ++ tailWord_7342407) baseStart_7342407 baseEnd_7342407 := by
    simpa [prefixWord, tailWord_7342407, baseEnd_7342407] using wordTrace_append hprefix tailTrace_7342407
  have hstable : (prefixWord ++ tailWord_7342407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342407).length < 2 ^ (prefixWord ++ tailWord_7342407).sum := by decide
  have hdescent : baseEnd_7342407 < baseStart_7342407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342417 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 1, 2, 3]
def baseStart_7342417 : Nat := 118140960795 + 7342417 * 2 ^ 59
def prefixEnd_7342417 : Nat := 4983230072969 + 3 ^ 40 * 7342417 * 2
def baseEnd_7342417 : Nat := 3770189086743304493420345

theorem tailTrace_7342417 : CollatzResearch.WordTrace tailWord_7342417 prefixEnd_7342417 3770189086743304493420345 := by
  unfold tailWord_7342417
  simp only [CollatzResearch.WordTrace]
  refine ⟨267799948640684668833865505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178533299093789779222577003 267799948640684668833865505)
  ·
    refine ⟨200849961480513501625399129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267799948640684668833865505 200849961480513501625399129)
    ·
      refine ⟨150637471110385126219049347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200849961480513501625399129 150637471110385126219049347)
      ·
        refine ⟨225956206665577689328574021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150637471110385126219049347 225956206665577689328574021)
        ·
          refine ⟨42366788749795816749107629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225956206665577689328574021 42366788749795816749107629)
          ·
            refine ⟨15887545781173431280915361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42366788749795816749107629 15887545781173431280915361)
            ·
              refine ⟨11915659335880073460686521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15887545781173431280915361 11915659335880073460686521)
              ·
                refine ⟨8936744501910055095514891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11915659335880073460686521 8936744501910055095514891)
                ·
                  refine ⟨13405116752865082643272337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8936744501910055095514891 13405116752865082643272337)
                  ·
                    refine ⟨10053837564648811982454253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13405116752865082643272337 10053837564648811982454253)
                    ·
                      refine ⟨3770189086743304493420345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10053837564648811982454253 3770189086743304493420345)
                      ·
                        rfl

theorem cell23_7342417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_7342417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342417 prefixEnd_7342417 := by exact prefixLift 7342417
  have htrace : WordTrace (prefixWord ++ tailWord_7342417) baseStart_7342417 baseEnd_7342417 := by
    simpa [prefixWord, tailWord_7342417, baseEnd_7342417] using wordTrace_append hprefix tailTrace_7342417
  have hstable : (prefixWord ++ tailWord_7342417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342417).length < 2 ^ (prefixWord ++ tailWord_7342417).sum := by decide
  have hdescent : baseEnd_7342417 < baseStart_7342417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342420 : List Nat := [2, 4, 1, 1, 2, 2, 4, 7]
def baseStart_7342420 : Nat := 118140960795 + 7342420 * 2 ^ 59
def prefixEnd_7342420 : Nat := 4983230072969 + 3 ^ 40 * 7342420 * 2
def baseEnd_7342420 : Nat := 139636689895750665988253

theorem tailTrace_7342420 : CollatzResearch.WordTrace tailWord_7342420 prefixEnd_7342420 139636689895750665988253 := by
  unfold tailWord_7342420
  simp only [CollatzResearch.WordTrace]
  refine ⟨133900029029836900173112357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178533372039782533564149809 133900029029836900173112357)
  ·
    refine ⟨25106255443094418782458567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133900029029836900173112357 25106255443094418782458567)
    ·
      refine ⟨37659383164641628173687851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25106255443094418782458567 37659383164641628173687851)
      ·
        refine ⟨56489074746962442260531777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37659383164641628173687851 56489074746962442260531777)
        ·
          refine ⟨42366806060221831695398833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56489074746962442260531777 42366806060221831695398833)
          ·
            refine ⟨31775104545166373771549125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42366806060221831695398833 31775104545166373771549125)
            ·
              refine ⟨5957832102218695082165461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31775104545166373771549125 5957832102218695082165461)
              ·
                refine ⟨139636689895750665988253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5957832102218695082165461 139636689895750665988253)
                ·
                  rfl

theorem cell23_7342420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 7].length) (baseStart_7342420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342420 prefixEnd_7342420 := by exact prefixLift 7342420
  have htrace : WordTrace (prefixWord ++ tailWord_7342420) baseStart_7342420 baseEnd_7342420 := by
    simpa [prefixWord, tailWord_7342420, baseEnd_7342420] using wordTrace_append hprefix tailTrace_7342420
  have hstable : (prefixWord ++ tailWord_7342420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342420).length < 2 ^ (prefixWord ++ tailWord_7342420).sum := by decide
  have hdescent : baseEnd_7342420 < baseStart_7342420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342487 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 6, 2, 2]
def baseStart_7342487 : Nat := 118140960795 + 7342487 * 2 ^ 59
def prefixEnd_7342487 : Nat := 4983230072969 + 3 ^ 40 * 7342487 * 2
def baseEnd_7342487 : Nat := 3770225030389119219545023

theorem tailTrace_7342487 : CollatzResearch.WordTrace tailWord_7342487 prefixEnd_7342487 3770225030389119219545023 := by
  unfold tailWord_7342487
  simp only [CollatzResearch.WordTrace]
  refine ⟨267802501750431070788913715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178535001166954047192609143 267802501750431070788913715)
  ·
    refine ⟨401703752625646606183370573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267802501750431070788913715 401703752625646606183370573)
    ·
      refine ⟨150638907234617477318763965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401703752625646606183370573 150638907234617477318763965)
      ·
        refine ⟨56489590212981553994536487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150638907234617477318763965 56489590212981553994536487)
        ·
          refine ⟨84734385319472330991804731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56489590212981553994536487 84734385319472330991804731)
          ·
            refine ⟨127101577979208496487707097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84734385319472330991804731 127101577979208496487707097)
            ·
              refine ⟨95326183484406372365780323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127101577979208496487707097 95326183484406372365780323)
              ·
                refine ⟨142989275226609558548670485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95326183484406372365780323 142989275226609558548670485)
                ·
                  refine ⟨6702622276247323056968929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142989275226609558548670485 6702622276247323056968929)
                  ·
                    refine ⟨5026966707185492292726697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6702622276247323056968929 5026966707185492292726697)
                    ·
                      refine ⟨3770225030389119219545023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5026966707185492292726697 3770225030389119219545023)
                      ·
                        rfl

theorem cell23_7342487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_7342487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342487 prefixEnd_7342487 := by exact prefixLift 7342487
  have htrace : WordTrace (prefixWord ++ tailWord_7342487) baseStart_7342487 baseEnd_7342487 := by
    simpa [prefixWord, tailWord_7342487, baseEnd_7342487] using wordTrace_append hprefix tailTrace_7342487
  have hstable : (prefixWord ++ tailWord_7342487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342487).length < 2 ^ (prefixWord ++ tailWord_7342487).sum := by decide
  have hdescent : baseEnd_7342487 < baseStart_7342487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342490 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_7342490 : Nat := 118140960795 + 7342490 * 2 ^ 59
def prefixEnd_7342490 : Nat := 4983230072969 + 3 ^ 40 * 7342490 * 2
def baseEnd_7342490 : Nat := 3770226570831082707807509

theorem tailTrace_7342490 : CollatzResearch.WordTrace tailWord_7342490 prefixEnd_7342490 3770226570831082707807509 := by
  unfold tailWord_7342490
  simp only [CollatzResearch.WordTrace]
  refine ⟨66950652792355050575318231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178535074112946801534181949 66950652792355050575318231)
  ·
    refine ⟨100425979188532575862977347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66950652792355050575318231 100425979188532575862977347)
    ·
      refine ⟨150638968782798863794466021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100425979188532575862977347 150638968782798863794466021)
      ·
        refine ⟨28244806646774786961462379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150638968782798863794466021 28244806646774786961462379)
        ·
          refine ⟨42367209970162180442193569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28244806646774786961462379 42367209970162180442193569)
          ·
            refine ⟨31775407477621635331645177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42367209970162180442193569 31775407477621635331645177)
            ·
              refine ⟨23831555608216226498733883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31775407477621635331645177 23831555608216226498733883)
              ·
                refine ⟨35747333412324339748100825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23831555608216226498733883 35747333412324339748100825)
                ·
                  refine ⟨26810500059243254811075619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35747333412324339748100825 26810500059243254811075619)
                  ·
                    refine ⟨40215750088864882216613429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26810500059243254811075619 40215750088864882216613429)
                    ·
                      refine ⟨3770226570831082707807509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40215750088864882216613429 3770226570831082707807509)
                      ·
                        rfl

theorem cell23_7342490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_7342490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342490 prefixEnd_7342490 := by exact prefixLift 7342490
  have htrace : WordTrace (prefixWord ++ tailWord_7342490) baseStart_7342490 baseEnd_7342490 := by
    simpa [prefixWord, tailWord_7342490, baseEnd_7342490] using wordTrace_append hprefix tailTrace_7342490
  have hstable : (prefixWord ++ tailWord_7342490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342490).length < 2 ^ (prefixWord ++ tailWord_7342490).sum := by decide
  have hdescent : baseEnd_7342490 < baseStart_7342490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342517 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_7342517 : Nat := 118140960795 + 7342517 * 2 ^ 59
def prefixEnd_7342517 : Nat := 4983230072969 + 3 ^ 40 * 7342517 * 2
def baseEnd_7342517 : Nat := 3770240434808754102169885

theorem tailTrace_7342517 : CollatzResearch.WordTrace tailWord_7342517 prefixEnd_7342517 3770240434808754102169885 := by
  unfold tailWord_7342517
  simp only [CollatzResearch.WordTrace]
  refine ⟨267803595940322385912505805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178535730626881590608337203 267803595940322385912505805)
  ·
    refine ⟨100426348477620894717189677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267803595940322385912505805 100426348477620894717189677)
    ·
      refine ⟨37659880679107835518946129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100426348477620894717189677 37659880679107835518946129)
      ·
        refine ⟨28244910509330876639209597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37659880679107835518946129 28244910509330876639209597)
        ·
          refine ⟨10591841440999078739703599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28244910509330876639209597 10591841440999078739703599)
          ·
            refine ⟨15887762161498618109555399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10591841440999078739703599 15887762161498618109555399)
            ·
              refine ⟨23831643242247927164333099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15887762161498618109555399 23831643242247927164333099)
              ·
                refine ⟨35747464863371890746499649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23831643242247927164333099 35747464863371890746499649)
                ·
                  refine ⟨26810598647528918059874737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35747464863371890746499649 26810598647528918059874737)
                  ·
                    refine ⟨20107948985646688544906053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26810598647528918059874737 20107948985646688544906053)
                    ·
                      refine ⟨3770240434808754102169885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20107948985646688544906053 3770240434808754102169885)
                      ·
                        rfl

theorem cell23_7342517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_7342517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342517 prefixEnd_7342517 := by exact prefixLift 7342517
  have htrace : WordTrace (prefixWord ++ tailWord_7342517) baseStart_7342517 baseEnd_7342517 := by
    simpa [prefixWord, tailWord_7342517, baseEnd_7342517] using wordTrace_append hprefix tailTrace_7342517
  have hstable : (prefixWord ++ tailWord_7342517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342517).length < 2 ^ (prefixWord ++ tailWord_7342517).sum := by decide
  have hdescent : baseEnd_7342517 < baseStart_7342517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342533 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_7342533 : Nat := 118140960795 + 7342533 * 2 ^ 59
def prefixEnd_7342533 : Nat := 4983230072969 + 3 ^ 40 * 7342533 * 2
def baseEnd_7342533 : Nat := 3770248650499226039569811

theorem tailTrace_7342533 : CollatzResearch.WordTrace tailWord_7342533 prefixEnd_7342533 3770248650499226039569811 := by
  unfold tailWord_7342533
  simp only [CollatzResearch.WordTrace]
  refine ⟨267804179508264420645088253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178536119672176280430058835 267804179508264420645088253)
  ·
    refine ⟨100426567315599157741908095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267804179508264420645088253 100426567315599157741908095)
    ·
      refine ⟨150639850973398736612862143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100426567315599157741908095 150639850973398736612862143)
      ·
        refine ⟨225959776460098104919293215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150639850973398736612862143 225959776460098104919293215)
        ·
          refine ⟨338939664690147157378939823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225959776460098104919293215 338939664690147157378939823)
          ·
            refine ⟨508409497035220736068409735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338939664690147157378939823 508409497035220736068409735)
            ·
              refine ⟨762614245552831104102614603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508409497035220736068409735 762614245552831104102614603)
              ·
                refine ⟨1143921368329246656153921905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762614245552831104102614603 1143921368329246656153921905)
                ·
                  refine ⟨857941026246934992115441429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1143921368329246656153921905 857941026246934992115441429)
                  ·
                    refine ⟨40215985605325077755411317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 857941026246934992115441429 40215985605325077755411317)
                    ·
                      refine ⟨3770248650499226039569811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40215985605325077755411317 3770248650499226039569811)
                      ·
                        rfl

theorem cell23_7342533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_7342533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342533 prefixEnd_7342533 := by exact prefixLift 7342533
  have htrace : WordTrace (prefixWord ++ tailWord_7342533) baseStart_7342533 baseEnd_7342533 := by
    simpa [prefixWord, tailWord_7342533, baseEnd_7342533] using wordTrace_append hprefix tailTrace_7342533
  have hstable : (prefixWord ++ tailWord_7342533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342533).length < 2 ^ (prefixWord ++ tailWord_7342533).sum := by decide
  have hdescent : baseEnd_7342533 < baseStart_7342533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342560 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 4]
def baseStart_7342560 : Nat := 118140960795 + 7342560 * 2 ^ 59
def prefixEnd_7342560 : Nat := 4983230072969 + 3 ^ 40 * 7342560 * 2
def baseEnd_7342560 : Nat := 3770262514476897433932187

theorem tailTrace_7342560 : CollatzResearch.WordTrace tailWord_7342560 prefixEnd_7342560 3770262514476897433932187 := by
  unfold tailWord_7342560
  simp only [CollatzResearch.WordTrace]
  refine ⟨133902582139583302128160567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178536776186111069504214089 133902582139583302128160567)
  ·
    refine ⟨200853873209374953192240851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133902582139583302128160567 200853873209374953192240851)
    ·
      refine ⟨301280809814062429788361277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200853873209374953192240851 301280809814062429788361277)
      ·
        refine ⟨112980303680273411170635479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301280809814062429788361277 112980303680273411170635479)
        ·
          refine ⟨169470455520410116755953219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112980303680273411170635479 169470455520410116755953219)
          ·
            refine ⟨254205683280615175133929829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169470455520410116755953219 254205683280615175133929829)
            ·
              refine ⟨47663565615115345337611843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254205683280615175133929829 47663565615115345337611843)
              ·
                refine ⟨71495348422673018006417765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47663565615115345337611843 71495348422673018006417765)
                ·
                  refine ⟨13405377829251190876203331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71495348422673018006417765 13405377829251190876203331)
                  ·
                    refine ⟨20108066743876786314304997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13405377829251190876203331 20108066743876786314304997)
                    ·
                      refine ⟨3770262514476897433932187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20108066743876786314304997 3770262514476897433932187)
                      ·
                        rfl

theorem cell23_7342560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_7342560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342560 prefixEnd_7342560 := by exact prefixLift 7342560
  have htrace : WordTrace (prefixWord ++ tailWord_7342560) baseStart_7342560 baseEnd_7342560 := by
    simpa [prefixWord, tailWord_7342560, baseEnd_7342560] using wordTrace_append hprefix tailTrace_7342560
  have hstable : (prefixWord ++ tailWord_7342560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342560).length < 2 ^ (prefixWord ++ tailWord_7342560).sum := by decide
  have hdescent : baseEnd_7342560 < baseStart_7342560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342577 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 2, 4, 2]
def baseStart_7342577 : Nat := 118140960795 + 7342577 * 2 ^ 59
def prefixEnd_7342577 : Nat := 4983230072969 + 3 ^ 40 * 7342577 * 2
def baseEnd_7342577 : Nat := 3770271243648023867419609

theorem tailTrace_7342577 : CollatzResearch.WordTrace tailWord_7342577 prefixEnd_7342577 3770271243648023867419609 := by
  unfold tailWord_7342577
  simp only [CollatzResearch.WordTrace]
  refine ⟨267805784320105016159689985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178537189546736677439793323 267805784320105016159689985)
  ·
    refine ⟨200854338240078762119767489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267805784320105016159689985 200854338240078762119767489)
    ·
      refine ⟨150640753680059071589825617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200854338240078762119767489 150640753680059071589825617)
      ·
        refine ⟨112980565260044303692369213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150640753680059071589825617 112980565260044303692369213)
        ·
          refine ⟨42367711972516613884638455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112980565260044303692369213 42367711972516613884638455)
          ·
            refine ⟨63551567958774920826957683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42367711972516613884638455 63551567958774920826957683)
            ·
              refine ⟨95327351938162381240436525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63551567958774920826957683 95327351938162381240436525)
              ·
                refine ⟨35747756976810892965163697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95327351938162381240436525 35747756976810892965163697)
                ·
                  refine ⟨26810817732608169723872773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35747756976810892965163697 26810817732608169723872773)
                  ·
                    refine ⟨5027028324864031823226145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26810817732608169723872773 5027028324864031823226145)
                    ·
                      refine ⟨3770271243648023867419609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027028324864031823226145 3770271243648023867419609)
                      ·
                        rfl

theorem cell23_7342577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_7342577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342577 prefixEnd_7342577 := by exact prefixLift 7342577
  have htrace : WordTrace (prefixWord ++ tailWord_7342577) baseStart_7342577 baseEnd_7342577 := by
    simpa [prefixWord, tailWord_7342577, baseEnd_7342577] using wordTrace_append hprefix tailTrace_7342577
  have hstable : (prefixWord ++ tailWord_7342577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342577).length < 2 ^ (prefixWord ++ tailWord_7342577).sum := by decide
  have hdescent : baseEnd_7342577 < baseStart_7342577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342634 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 6]
def baseStart_7342634 : Nat := 118140960795 + 7342634 * 2 ^ 59
def prefixEnd_7342634 : Nat := 4983230072969 + 3 ^ 40 * 7342634 * 2
def baseEnd_7342634 : Nat := 418922279116147793822983

theorem tailTrace_7342634 : CollatzResearch.WordTrace tailWord_7342634 prefixEnd_7342634 418922279116147793822983 := by
  unfold tailWord_7342634
  simp only [CollatzResearch.WordTrace]
  refine ⟨66951965820224628723628739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178538575520599009929676637 66951965820224628723628739)
  ·
    refine ⟨100427948730336943085443109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66951965820224628723628739 100427948730336943085443109)
    ·
      refine ⟨18830240386938176828520583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100427948730336943085443109 18830240386938176828520583)
      ·
        refine ⟨28245360580407265242780875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18830240386938176828520583 28245360580407265242780875)
        ·
          refine ⟨42368040870610897864171313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28245360580407265242780875 42368040870610897864171313)
          ·
            refine ⟨31776030652958173398128485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42368040870610897864171313 31776030652958173398128485)
            ·
              refine ⟨5958005747429657512149091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31776030652958173398128485 5958005747429657512149091)
              ·
                refine ⟨8937008621144486268223637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5958005747429657512149091 8937008621144486268223637)
                ·
                  refine ⟨418922279116147793822983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8937008621144486268223637 418922279116147793822983)
                  ·
                    rfl

theorem cell23_7342634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_7342634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342634 prefixEnd_7342634 := by exact prefixLift 7342634
  have htrace : WordTrace (prefixWord ++ tailWord_7342634) baseStart_7342634 baseEnd_7342634 := by
    simpa [prefixWord, tailWord_7342634, baseEnd_7342634] using wordTrace_append hprefix tailTrace_7342634
  have hstable : (prefixWord ++ tailWord_7342634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342634).length < 2 ^ (prefixWord ++ tailWord_7342634).sum := by decide
  have hdescent : baseEnd_7342634 < baseStart_7342634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342667 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 4]
def baseStart_7342667 : Nat := 118140960795 + 7342667 * 2 ^ 59
def prefixEnd_7342667 : Nat := 4983230072969 + 3 ^ 40 * 7342667 * 2
def baseEnd_7342667 : Nat := 3770317456906928515294195

theorem tailTrace_7342667 : CollatzResearch.WordTrace tailWord_7342667 prefixEnd_7342667 3770317456906928515294195 := by
  unfold tailWord_7342667
  simp only [CollatzResearch.WordTrace]
  refine ⟨267809066889778961530466255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178539377926519307686977503 267809066889778961530466255)
  ·
    refine ⟨401713600334668442295699383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267809066889778961530466255 401713600334668442295699383)
    ·
      refine ⟨602570400502002663443549075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401713600334668442295699383 602570400502002663443549075)
      ·
        refine ⟨903855600753003995165323613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602570400502002663443549075 903855600753003995165323613)
        ·
          refine ⟨338945850282376498186996355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 903855600753003995165323613 338945850282376498186996355)
          ·
            refine ⟨508418775423564747280494533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338945850282376498186996355 508418775423564747280494533)
            ·
              refine ⟨95328520391918390115092725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 508418775423564747280494533 95328520391918390115092725)
              ·
                refine ⟨8937048786742349073289943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95328520391918390115092725 8937048786742349073289943)
                ·
                  refine ⟨13405573180113523609934915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8937048786742349073289943 13405573180113523609934915)
                  ·
                    refine ⟨20108359770170285414902373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13405573180113523609934915 20108359770170285414902373)
                    ·
                      refine ⟨3770317456906928515294195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20108359770170285414902373 3770317456906928515294195)
                      ·
                        rfl

theorem cell23_7342667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 4].length) (baseStart_7342667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342667 prefixEnd_7342667 := by exact prefixLift 7342667
  have htrace : WordTrace (prefixWord ++ tailWord_7342667) baseStart_7342667 baseEnd_7342667 := by
    simpa [prefixWord, tailWord_7342667, baseEnd_7342667] using wordTrace_append hprefix tailTrace_7342667
  have hstable : (prefixWord ++ tailWord_7342667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342667).length < 2 ^ (prefixWord ++ tailWord_7342667).sum := by decide
  have hdescent : baseEnd_7342667 < baseStart_7342667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342677 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 4, 4]
def baseStart_7342677 : Nat := 118140960795 + 7342677 * 2 ^ 59
def prefixEnd_7342677 : Nat := 4983230072969 + 3 ^ 40 * 7342677 * 2
def baseEnd_7342677 : Nat := 1256774197237824492056383

theorem tailTrace_7342677 : CollatzResearch.WordTrace tailWord_7342677 prefixEnd_7342677 1256774197237824492056383 := by
  unfold tailWord_7342677
  simp only [CollatzResearch.WordTrace]
  refine ⟨267809431619742733238330285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178539621079828488825553523 267809431619742733238330285)
  ·
    refine ⟨100428536857403524964373857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267809431619742733238330285 100428536857403524964373857)
    ·
      refine ⟨75321402643052643723280393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100428536857403524964373857 75321402643052643723280393)
      ·
        refine ⟨56491051982289482792460295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75321402643052643723280393 56491051982289482792460295)
        ·
          refine ⟨84736577973434224188690443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56491051982289482792460295 84736577973434224188690443)
          ·
            refine ⟨127104866960151336283035665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84736577973434224188690443 127104866960151336283035665)
            ·
              refine ⟨95328650220113502212276749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127104866960151336283035665 95328650220113502212276749)
              ·
                refine ⟨35748243832542563329603781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95328650220113502212276749 35748243832542563329603781)
                ·
                  refine ⟨6702795718601730624300709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35748243832542563329603781 6702795718601730624300709)
                  ·
                    refine ⟨1256774197237824492056383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6702795718601730624300709 1256774197237824492056383)
                    ·
                      rfl

theorem cell23_7342677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_7342677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342677 prefixEnd_7342677 := by exact prefixLift 7342677
  have htrace : WordTrace (prefixWord ++ tailWord_7342677) baseStart_7342677 baseEnd_7342677 := by
    simpa [prefixWord, tailWord_7342677, baseEnd_7342677] using wordTrace_append hprefix tailTrace_7342677
  have hstable : (prefixWord ++ tailWord_7342677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342677).length < 2 ^ (prefixWord ++ tailWord_7342677).sum := by decide
  have hdescent : baseEnd_7342677 < baseStart_7342677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342680 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_7342680 : Nat := 118140960795 + 7342680 * 2 ^ 59
def prefixEnd_7342680 : Nat := 4983230072969 + 3 ^ 40 * 7342680 * 2
def baseEnd_7342680 : Nat := 3770324132155436964431635

theorem tailTrace_7342680 : CollatzResearch.WordTrace tailWord_7342680 prefixEnd_7342680 3770324132155436964431635 := by
  unfold tailWord_7342680
  simp only [CollatzResearch.WordTrace]
  refine ⟨133904770519365932375344747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178539694025821243167126329 133904770519365932375344747)
  ·
    refine ⟨200857155779048898563017121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133904770519365932375344747 200857155779048898563017121)
    ·
      refine ⟨150642866834286673922262841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200857155779048898563017121 150642866834286673922262841)
      ·
        refine ⟨112982150125715005441697131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150642866834286673922262841 112982150125715005441697131)
        ·
          refine ⟨169473225188572508162545697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112982150125715005441697131 169473225188572508162545697)
          ·
            refine ⟨127104918891429381121909273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169473225188572508162545697 127104918891429381121909273)
            ·
              refine ⟨95328689168572035841431955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127104918891429381121909273 95328689168572035841431955)
              ·
                refine ⟨142993033752858053762147933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95328689168572035841431955 142993033752858053762147933)
                ·
                  refine ⟨53622387657321770160805475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142993033752858053762147933 53622387657321770160805475)
                  ·
                    refine ⟨80433581485982655241208213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53622387657321770160805475 80433581485982655241208213)
                    ·
                      refine ⟨3770324132155436964431635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80433581485982655241208213 3770324132155436964431635)
                      ·
                        rfl

theorem cell23_7342680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_7342680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342680 prefixEnd_7342680 := by exact prefixLift 7342680
  have htrace : WordTrace (prefixWord ++ tailWord_7342680) baseStart_7342680 baseEnd_7342680 := by
    simpa [prefixWord, tailWord_7342680, baseEnd_7342680] using wordTrace_append hprefix tailTrace_7342680
  have hstable : (prefixWord ++ tailWord_7342680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342680).length < 2 ^ (prefixWord ++ tailWord_7342680).sum := by decide
  have hdescent : baseEnd_7342680 < baseStart_7342680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342701 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_7342701 : Nat := 118140960795 + 7342701 * 2 ^ 59
def prefixEnd_7342701 : Nat := 4983230072969 + 3 ^ 40 * 7342701 * 2
def baseEnd_7342701 : Nat := 3770334915249181382269039

theorem tailTrace_7342701 : CollatzResearch.WordTrace tailWord_7342701 prefixEnd_7342701 3770334915249181382269039 := by
  unfold tailWord_7342701
  simp only [CollatzResearch.WordTrace]
  refine ⟨267810306971655785337203957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178540204647770523558135971 267810306971655785337203957)
  ·
    refine ⟨25107216278592729875362871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267810306971655785337203957 25107216278592729875362871)
    ·
      refine ⟨37660824417889094813044307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25107216278592729875362871 37660824417889094813044307)
      ·
        refine ⟨56491236626833642219566461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37660824417889094813044307 56491236626833642219566461)
        ·
          refine ⟨21184213735062615832337423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56491236626833642219566461 21184213735062615832337423)
          ·
            refine ⟨31776320602593923748506135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21184213735062615832337423 31776320602593923748506135)
            ·
              refine ⟨47664480903890885622759203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31776320602593923748506135 47664480903890885622759203)
              ·
                refine ⟨71496721355836328434138805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47664480903890885622759203 71496721355836328434138805)
                ·
                  refine ⟨6702817627109655790700513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71496721355836328434138805 6702817627109655790700513)
                  ·
                    refine ⟨5027113220332241843025385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6702817627109655790700513 5027113220332241843025385)
                    ·
                      refine ⟨3770334915249181382269039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027113220332241843025385 3770334915249181382269039)
                      ·
                        rfl

theorem cell23_7342701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_7342701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342701 prefixEnd_7342701 := by exact prefixLift 7342701
  have htrace : WordTrace (prefixWord ++ tailWord_7342701) baseStart_7342701 baseEnd_7342701 := by
    simpa [prefixWord, tailWord_7342701, baseEnd_7342701] using wordTrace_append hprefix tailTrace_7342701
  have hstable : (prefixWord ++ tailWord_7342701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342701).length < 2 ^ (prefixWord ++ tailWord_7342701).sum := by decide
  have hdescent : baseEnd_7342701 < baseStart_7342701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342769 : List Nat := [1, 2, 2, 6, 2, 1, 1, 3, 1, 2, 2]
def baseStart_7342769 : Nat := 118140960795 + 7342769 * 2 ^ 59
def prefixEnd_7342769 : Nat := 4983230072969 + 3 ^ 40 * 7342769 * 2
def baseEnd_7342769 : Nat := 3770369831933687116218727

theorem tailTrace_7342769 : CollatzResearch.WordTrace tailWord_7342769 prefixEnd_7342769 3770369831933687116218727 := by
  unfold tailWord_7342769
  simp only [CollatzResearch.WordTrace]
  refine ⟨267812787135409432950679361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178541858090272955300452907 267812787135409432950679361)
  ·
    refine ⟨200859590351557074713009521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267812787135409432950679361 200859590351557074713009521)
    ·
      refine ⟨150644692763667806034757141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200859590351557074713009521 150644692763667806034757141)
      ·
        refine ⟨7061469973296928407879241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150644692763667806034757141 7061469973296928407879241)
        ·
          refine ⟨5296102479972696305909431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7061469973296928407879241 5296102479972696305909431)
          ·
            refine ⟨7944153719959044458864147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296102479972696305909431 7944153719959044458864147)
            ·
              refine ⟨11916230579938566688296221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7944153719959044458864147 11916230579938566688296221)
              ·
                refine ⟨4468586467476962508111083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11916230579938566688296221 4468586467476962508111083)
                ·
                  refine ⟨6702879701215443762166625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468586467476962508111083 6702879701215443762166625)
                  ·
                    refine ⟨5027159775911582821624969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6702879701215443762166625 5027159775911582821624969)
                    ·
                      refine ⟨3770369831933687116218727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027159775911582821624969 3770369831933687116218727)
                      ·
                        rfl

theorem cell23_7342769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_7342769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342769 prefixEnd_7342769 := by exact prefixLift 7342769
  have htrace : WordTrace (prefixWord ++ tailWord_7342769) baseStart_7342769 baseEnd_7342769 := by
    simpa [prefixWord, tailWord_7342769, baseEnd_7342769] using wordTrace_append hprefix tailTrace_7342769
  have hstable : (prefixWord ++ tailWord_7342769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342769).length < 2 ^ (prefixWord ++ tailWord_7342769).sum := by decide
  have hdescent : baseEnd_7342769 < baseStart_7342769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342777 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 1, 6, 3]
def baseStart_7342777 : Nat := 118140960795 + 7342777 * 2 ^ 59
def prefixEnd_7342777 : Nat := 4983230072969 + 3 ^ 40 * 7342777 * 2
def baseEnd_7342777 : Nat := 3770373939778923084918689

theorem tailTrace_7342777 : CollatzResearch.WordTrace tailWord_7342777 prefixEnd_7342777 3770373939778923084918689 := by
  unfold tailWord_7342777
  simp only [CollatzResearch.WordTrace]
  refine ⟨267813078919380450316970585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178542052612920300211313723 267813078919380450316970585)
  ·
    refine ⟨200859809189535337737727939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267813078919380450316970585 200859809189535337737727939)
    ·
      refine ⟨301289713784303006606591909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200859809189535337737727939 301289713784303006606591909)
      ·
        refine ⟨56491821334556813738735983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301289713784303006606591909 56491821334556813738735983)
        ·
          refine ⟨84737732001835220608103975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56491821334556813738735983 84737732001835220608103975)
          ·
            refine ⟨127106598002752830912155963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84737732001835220608103975 127106598002752830912155963)
            ·
              refine ⟨190659897004129246368233945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127106598002752830912155963 190659897004129246368233945)
              ·
                refine ⟨142994922753096934776175459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190659897004129246368233945 142994922753096934776175459)
                ·
                  refine ⟨214492384129645402164263189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142994922753096934776175459 214492384129645402164263189)
                  ·
                    refine ⟨10054330506077128226449837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214492384129645402164263189 10054330506077128226449837)
                    ·
                      refine ⟨3770373939778923084918689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10054330506077128226449837 3770373939778923084918689)
                      ·
                        rfl

theorem cell23_7342777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_7342777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342777 prefixEnd_7342777 := by exact prefixLift 7342777
  have htrace : WordTrace (prefixWord ++ tailWord_7342777) baseStart_7342777 baseEnd_7342777 := by
    simpa [prefixWord, tailWord_7342777, baseEnd_7342777] using wordTrace_append hprefix tailTrace_7342777
  have hstable : (prefixWord ++ tailWord_7342777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342777).length < 2 ^ (prefixWord ++ tailWord_7342777).sum := by decide
  have hdescent : baseEnd_7342777 < baseStart_7342777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342802 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_7342802 : Nat := 118140960795 + 7342802 * 2 ^ 59
def prefixEnd_7342802 : Nat := 4983230072969 + 3 ^ 40 * 7342802 * 2
def baseEnd_7342802 : Nat := 3770386776795285487106075

theorem tailTrace_7342802 : CollatzResearch.WordTrace tailWord_7342802 prefixEnd_7342802 3770386776795285487106075 := by
  unfold tailWord_7342802
  simp only [CollatzResearch.WordTrace]
  refine ⟨66953497686072469896657665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178542660496193253057753773 66953497686072469896657665)
  ·
    refine ⟨50215123264554352422493249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66953497686072469896657665 50215123264554352422493249)
    ·
      refine ⟨37661342448415764316869937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50215123264554352422493249 37661342448415764316869937)
      ·
        refine ⟨28246006836311823237652453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37661342448415764316869937 28246006836311823237652453)
        ·
          refine ⟨5296126281808466857059835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28246006836311823237652453 5296126281808466857059835)
          ·
            refine ⟨7944189422712700285589753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296126281808466857059835 7944189422712700285589753)
            ·
              refine ⟨5958142067034525214192315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7944189422712700285589753 5958142067034525214192315)
              ·
                refine ⟨8937213100551787821288473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5958142067034525214192315 8937213100551787821288473)
                ·
                  refine ⟨6702909825413840865966355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8937213100551787821288473 6702909825413840865966355)
                  ·
                    refine ⟨10054364738120761298949533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6702909825413840865966355 10054364738120761298949533)
                    ·
                      refine ⟨3770386776795285487106075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10054364738120761298949533 3770386776795285487106075)
                      ·
                        rfl

theorem cell23_7342802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_7342802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342802 prefixEnd_7342802 := by exact prefixLift 7342802
  have htrace : WordTrace (prefixWord ++ tailWord_7342802) baseStart_7342802 baseEnd_7342802 := by
    simpa [prefixWord, tailWord_7342802, baseEnd_7342802] using wordTrace_append hprefix tailTrace_7342802
  have hstable : (prefixWord ++ tailWord_7342802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342802).length < 2 ^ (prefixWord ++ tailWord_7342802).sum := by decide
  have hdescent : baseEnd_7342802 < baseStart_7342802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342808 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 2, 2, 2]
def baseStart_7342808 : Nat := 118140960795 + 7342808 * 2 ^ 59
def prefixEnd_7342808 : Nat := 4983230072969 + 3 ^ 40 * 7342808 * 2
def baseEnd_7342808 : Nat := 3770389857679212463631047

theorem tailTrace_7342808 : CollatzResearch.WordTrace tailWord_7342808 prefixEnd_7342808 3770389857679212463631047 := by
  unfold tailWord_7342808
  simp only [CollatzResearch.WordTrace]
  refine ⟨133907104791134071305674539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178542806388178761740899385 133907104791134071305674539)
  ·
    refine ⟨200860657186701106958511809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133907104791134071305674539 200860657186701106958511809)
    ·
      refine ⟨150645492890025830218883857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200860657186701106958511809 150645492890025830218883857)
      ·
        refine ⟨112984119667519372664162893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150645492890025830218883857 112984119667519372664162893)
        ·
          refine ⟨42369044875319764749061085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112984119667519372664162893 42369044875319764749061085)
          ·
            refine ⟨15888391828244911780897907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42369044875319764749061085 15888391828244911780897907)
            ·
              refine ⟨23832587742367367671346861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15888391828244911780897907 23832587742367367671346861)
              ·
                refine ⟨8937220403387762876755073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23832587742367367671346861 8937220403387762876755073)
                ·
                  refine ⟨6702915302540822157566305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8937220403387762876755073 6702915302540822157566305)
                  ·
                    refine ⟨5027186476905616618174729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6702915302540822157566305 5027186476905616618174729)
                    ·
                      refine ⟨3770389857679212463631047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027186476905616618174729 3770389857679212463631047)
                      ·
                        rfl

theorem cell23_7342808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_7342808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342808 prefixEnd_7342808 := by exact prefixLift 7342808
  have htrace : WordTrace (prefixWord ++ tailWord_7342808) baseStart_7342808 baseEnd_7342808 := by
    simpa [prefixWord, tailWord_7342808, baseEnd_7342808] using wordTrace_append hprefix tailTrace_7342808
  have hstable : (prefixWord ++ tailWord_7342808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342808).length < 2 ^ (prefixWord ++ tailWord_7342808).sum := by decide
  have hdescent : baseEnd_7342808 < baseStart_7342808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342844 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_7342844 : Nat := 118140960795 + 7342844 * 2 ^ 59
def prefixEnd_7342844 : Nat := 4983230072969 + 3 ^ 40 * 7342844 * 2
def baseEnd_7342844 : Nat := 1256802780994258107593627

theorem tailTrace_7342844 : CollatzResearch.WordTrace tailWord_7342844 prefixEnd_7342844 1256802780994258107593627 := by
  unfold tailWord_7342844
  simp only [CollatzResearch.WordTrace]
  refine ⟨133907761305068860379829793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178543681740091813839773057 133907761305068860379829793)
  ·
    refine ⟨100430820978801645284872345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133907761305068860379829793 100430820978801645284872345)
    ·
      refine ⟨75323115734101233963654259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100430820978801645284872345 75323115734101233963654259)
      ·
        refine ⟨112984673601151850945481389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75323115734101233963654259 112984673601151850945481389)
        ·
          refine ⟨42369252600431944104555521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112984673601151850945481389 42369252600431944104555521)
          ·
            refine ⟨31776939450323958078416641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42369252600431944104555521 31776939450323958078416641)
            ·
              refine ⟨23832704587742968558812481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31776939450323958078416641 23832704587742968558812481)
              ·
                refine ⟨17874528440807226419109361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23832704587742968558812481 17874528440807226419109361)
                ·
                  refine ⟨13405896330605419814332021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17874528440807226419109361 13405896330605419814332021)
                  ·
                    refine ⟨1256802780994258107593627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13405896330605419814332021 1256802780994258107593627)
                    ·
                      rfl

theorem cell23_7342844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_7342844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342844 prefixEnd_7342844 := by exact prefixLift 7342844
  have htrace : WordTrace (prefixWord ++ tailWord_7342844) baseStart_7342844 baseEnd_7342844 := by
    simpa [prefixWord, tailWord_7342844, baseEnd_7342844] using wordTrace_append hprefix tailTrace_7342844
  have hstable : (prefixWord ++ tailWord_7342844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342844).length < 2 ^ (prefixWord ++ tailWord_7342844).sum := by decide
  have hdescent : baseEnd_7342844 < baseStart_7342844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342847 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 4]
def baseStart_7342847 : Nat := 118140960795 + 7342847 * 2 ^ 59
def prefixEnd_7342847 : Nat := 4983230072969 + 3 ^ 40 * 7342847 * 2
def baseEnd_7342847 : Nat := 3770409883424737811043367

theorem tailTrace_7342847 : CollatzResearch.WordTrace tailWord_7342847 prefixEnd_7342847 3770409883424737811043367 := by
  unfold tailWord_7342847
  simp only [CollatzResearch.WordTrace]
  refine ⟨267815632029126852272018795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178543754686084568181345863 267815632029126852272018795)
  ·
    refine ⟨401723448043690278408028193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267815632029126852272018795 401723448043690278408028193)
    ·
      refine ⟨301292586032767708806021145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401723448043690278408028193 301292586032767708806021145)
      ·
        refine ⟨225969439524575781604515859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301292586032767708806021145 225969439524575781604515859)
        ·
          refine ⟨338954159286863672406773789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225969439524575781604515859 338954159286863672406773789)
          ·
            refine ⟨127107809732573877152540171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338954159286863672406773789 127107809732573877152540171)
            ·
              refine ⟨190661714598860815728810257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127107809732573877152540171 190661714598860815728810257)
              ·
                refine ⟨142996285949145611796607693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190661714598860815728810257 142996285949145611796607693)
                ·
                  refine ⟨53623607230929604423727885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142996285949145611796607693 53623607230929604423727885)
                  ·
                    refine ⟨20108852711598601658897957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53623607230929604423727885 20108852711598601658897957)
                    ·
                      refine ⟨3770409883424737811043367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20108852711598601658897957 3770409883424737811043367)
                      ·
                        rfl

theorem cell23_7342847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_7342847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342847 prefixEnd_7342847 := by exact prefixLift 7342847
  have htrace : WordTrace (prefixWord ++ tailWord_7342847) baseStart_7342847 baseEnd_7342847 := by
    simpa [prefixWord, tailWord_7342847, baseEnd_7342847] using wordTrace_append hprefix tailTrace_7342847
  have hstable : (prefixWord ++ tailWord_7342847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342847).length < 2 ^ (prefixWord ++ tailWord_7342847).sum := by decide
  have hdescent : baseEnd_7342847 < baseStart_7342847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342891 : List Nat := [1, 1, 1, 1, 2, 1, 2, 9, 1, 4]
def baseStart_7342891 : Nat := 118140960795 + 7342891 * 2 ^ 59
def prefixEnd_7342891 : Nat := 4983230072969 + 3 ^ 40 * 7342891 * 2
def baseEnd_7342891 : Nat := 1256810825524511879631055

theorem tailTrace_7342891 : CollatzResearch.WordTrace tailWord_7342891 prefixEnd_7342891 1256810825524511879631055 := by
  unfold tailWord_7342891
  simp only [CollatzResearch.WordTrace]
  refine ⟨267817236840967447786620527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178544824560644965191080351 267817236840967447786620527)
  ·
    refine ⟨401725855261451171679930791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267817236840967447786620527 401725855261451171679930791)
    ·
      refine ⟨602588782892176757519896187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401725855261451171679930791 602588782892176757519896187)
      ·
        refine ⟨903883174338265136279844281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602588782892176757519896187 903883174338265136279844281)
        ·
          refine ⟨677912380753698852209883211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903883174338265136279844281 677912380753698852209883211)
          ·
            refine ⟨1016868571130548278314824817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677912380753698852209883211 1016868571130548278314824817)
            ·
              refine ⟨762651428347911208736118613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016868571130548278314824817 762651428347911208736118613)
              ·
                refine ⟨4468660712976042238688195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 762651428347911208736118613 4468660712976042238688195)
                ·
                  refine ⟨6702991069464063358032293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468660712976042238688195 6702991069464063358032293)
                  ·
                    refine ⟨1256810825524511879631055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6702991069464063358032293 1256810825524511879631055)
                    ·
                      rfl

theorem cell23_7342891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 1, 4].length) (baseStart_7342891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342891 prefixEnd_7342891 := by exact prefixLift 7342891
  have htrace : WordTrace (prefixWord ++ tailWord_7342891) baseStart_7342891 baseEnd_7342891 := by
    simpa [prefixWord, tailWord_7342891, baseEnd_7342891] using wordTrace_append hprefix tailTrace_7342891
  have hstable : (prefixWord ++ tailWord_7342891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342891).length < 2 ^ (prefixWord ++ tailWord_7342891).sum := by decide
  have hdescent : baseEnd_7342891 < baseStart_7342891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342917 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_7342917 : Nat := 118140960795 + 7342917 * 2 ^ 59
def prefixEnd_7342917 : Nat := 4983230072969 + 3 ^ 40 * 7342917 * 2
def baseEnd_7342917 : Nat := 1256815275690184179056015

theorem tailTrace_7342917 : CollatzResearch.WordTrace tailWord_7342917 prefixEnd_7342917 1256815275690184179056015 := by
  unfold tailWord_7342917
  simp only [CollatzResearch.WordTrace]
  refine ⟨267818185138873254227067005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178545456759248836151378003 267818185138873254227067005)
  ·
    refine ⟨100431819427077470335150127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267818185138873254227067005 100431819427077470335150127)
    ·
      refine ⟨150647729140616205502725191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100431819427077470335150127 150647729140616205502725191)
      ·
        refine ⟨225971593710924308254087787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150647729140616205502725191 225971593710924308254087787)
        ·
          refine ⟨338957390566386462381131681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225971593710924308254087787 338957390566386462381131681)
          ·
            refine ⟨254218042924789846785848761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338957390566386462381131681 254218042924789846785848761)
            ·
              refine ⟨190663532193592385089386571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254218042924789846785848761 190663532193592385089386571)
              ·
                refine ⟨285995298290388577634079857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190663532193592385089386571 285995298290388577634079857)
                ·
                  refine ⟨214496473717791433225559893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285995298290388577634079857 214496473717791433225559893)
                  ·
                    refine ⟨1256815275690184179056015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 214496473717791433225559893 1256815275690184179056015)
                    ·
                      rfl

theorem cell23_7342917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_7342917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342917 prefixEnd_7342917 := by exact prefixLift 7342917
  have htrace : WordTrace (prefixWord ++ tailWord_7342917) baseStart_7342917 baseEnd_7342917 := by
    simpa [prefixWord, tailWord_7342917, baseEnd_7342917] using wordTrace_append hprefix tailTrace_7342917
  have hstable : (prefixWord ++ tailWord_7342917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342917).length < 2 ^ (prefixWord ++ tailWord_7342917).sum := by decide
  have hdescent : baseEnd_7342917 < baseStart_7342917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342921 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 6]
def baseStart_7342921 : Nat := 118140960795 + 7342921 * 2 ^ 59
def prefixEnd_7342921 : Nat := 4983230072969 + 3 ^ 40 * 7342921 * 2
def baseEnd_7342921 : Nat := 418938653443685613502003

theorem tailTrace_7342921 : CollatzResearch.WordTrace tailWord_7342921 prefixEnd_7342921 418938653443685613502003 := by
  unfold tailWord_7342921
  simp only [CollatzResearch.WordTrace]
  refine ⟨267818331030858762910212617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178545554020572508606808411 267818331030858762910212617)
  ·
    refine ⟨200863748273144072182659463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267818331030858762910212617 200863748273144072182659463)
    ·
      refine ⟨301295622409716108273989195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200863748273144072182659463 301295622409716108273989195)
      ·
        refine ⟨451943433614574162410983793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301295622409716108273989195 451943433614574162410983793)
        ·
          refine ⟨338957575210930621808237845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451943433614574162410983793 338957575210930621808237845)
          ·
            refine ⟨15888636338012372897261149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 338957575210930621808237845 15888636338012372897261149)
            ·
              refine ⟨5958238626754639836472931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15888636338012372897261149 5958238626754639836472931)
              ·
                refine ⟨8937357940131959754709397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5958238626754639836472931 8937357940131959754709397)
                ·
                  refine ⟨418938653443685613502003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8937357940131959754709397 418938653443685613502003)
                  ·
                    rfl

theorem cell23_7342921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 6].length) (baseStart_7342921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342921 prefixEnd_7342921 := by exact prefixLift 7342921
  have htrace : WordTrace (prefixWord ++ tailWord_7342921) baseStart_7342921 baseEnd_7342921 := by
    simpa [prefixWord, tailWord_7342921, baseEnd_7342921] using wordTrace_append hprefix tailTrace_7342921
  have hstable : (prefixWord ++ tailWord_7342921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342921).length < 2 ^ (prefixWord ++ tailWord_7342921).sum := by decide
  have hdescent : baseEnd_7342921 < baseStart_7342921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342951 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 1, 5]
def baseStart_7342951 : Nat := 118140960795 + 7342951 * 2 ^ 59
def prefixEnd_7342951 : Nat := 4983230072969 + 3 ^ 40 * 7342951 * 2
def baseEnd_7342951 : Nat := 1256821095137601801380963

theorem tailTrace_7342951 : CollatzResearch.WordTrace tailWord_7342951 prefixEnd_7342951 1256821095137601801380963 := by
  unfold tailWord_7342951
  simp only [CollatzResearch.WordTrace]
  refine ⟨267819425220750078033804707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178546283480500052022536471 267819425220750078033804707)
  ·
    refine ⟨401729137831125117050707061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267819425220750078033804707 401729137831125117050707061)
    ·
      refine ⟨37662106671667979723503787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 401729137831125117050707061 37662106671667979723503787)
      ·
        refine ⟨56493160007501969585255681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37662106671667979723503787 56493160007501969585255681)
        ·
          refine ⟨42369870005626477188941761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56493160007501969585255681 42369870005626477188941761)
          ·
            refine ⟨31777402504219857891706321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42369870005626477188941761 31777402504219857891706321)
            ·
              refine ⟨23833051878164893418779741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31777402504219857891706321 23833051878164893418779741)
              ·
                refine ⟨8937394454311835032042403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23833051878164893418779741 8937394454311835032042403)
                ·
                  refine ⟨13406091681467752548063605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8937394454311835032042403 13406091681467752548063605)
                  ·
                    refine ⟨1256821095137601801380963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13406091681467752548063605 1256821095137601801380963)
                    ·
                      rfl

theorem cell23_7342951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_7342951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342951 prefixEnd_7342951 := by exact prefixLift 7342951
  have htrace : WordTrace (prefixWord ++ tailWord_7342951) baseStart_7342951 baseEnd_7342951 := by
    simpa [prefixWord, tailWord_7342951, baseEnd_7342951] using wordTrace_append hprefix tailTrace_7342951
  have hstable : (prefixWord ++ tailWord_7342951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342951).length < 2 ^ (prefixWord ++ tailWord_7342951).sum := by decide
  have hdescent : baseEnd_7342951 < baseStart_7342951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342965 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_7342965 : Nat := 118140960795 + 7342965 * 2 ^ 59
def prefixEnd_7342965 : Nat := 4983230072969 + 3 ^ 40 * 7342965 * 2
def baseEnd_7342965 : Nat := 3770470474141968349367825

theorem tailTrace_7342965 : CollatzResearch.WordTrace tailWord_7342965 prefixEnd_7342965 3770470474141968349367825 := by
  unfold tailWord_7342965
  simp only [CollatzResearch.WordTrace]
  refine ⟨267819935842699358424814349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178546623895132905616542899 267819935842699358424814349)
  ·
    refine ⟨100432475941012259409305381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267819935842699358424814349 100432475941012259409305381)
    ·
      refine ⟨18831089238939798639244759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100432475941012259409305381 18831089238939798639244759)
      ·
        refine ⟨28246633858409697958867139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18831089238939798639244759 28246633858409697958867139)
        ·
          refine ⟨42369950787614546938300709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28246633858409697958867139 42369950787614546938300709)
          ·
            refine ⟨7944365772677727550931383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42369950787614546938300709 7944365772677727550931383)
            ·
              refine ⟨11916548659016591326397075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7944365772677727550931383 11916548659016591326397075)
              ·
                refine ⟨17874822988524886989595613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11916548659016591326397075 17874822988524886989595613)
                ·
                  refine ⟨6703058620696832621098355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17874822988524886989595613 6703058620696832621098355)
                  ·
                    refine ⟨10054587931045248931647533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6703058620696832621098355 10054587931045248931647533)
                    ·
                      refine ⟨3770470474141968349367825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10054587931045248931647533 3770470474141968349367825)
                      ·
                        rfl

theorem cell23_7342965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_7342965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342965 prefixEnd_7342965 := by exact prefixLift 7342965
  have htrace : WordTrace (prefixWord ++ tailWord_7342965) baseStart_7342965 baseEnd_7342965 := by
    simpa [prefixWord, tailWord_7342965, baseEnd_7342965] using wordTrace_append hprefix tailTrace_7342965
  have hstable : (prefixWord ++ tailWord_7342965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342965).length < 2 ^ (prefixWord ++ tailWord_7342965).sum := by decide
  have hdescent : baseEnd_7342965 < baseStart_7342965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7342988 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 3, 2, 2]
def baseStart_7342988 : Nat := 118140960795 + 7342988 * 2 ^ 59
def prefixEnd_7342988 : Nat := 4983230072969 + 3 ^ 40 * 7342988 * 2
def baseEnd_7342988 : Nat := 3770482284197021759380219

theorem tailTrace_7342988 : CollatzResearch.WordTrace tailWord_7342988 prefixEnd_7342988 3770482284197021759380219 := by
  unfold tailWord_7342988
  simp only [CollatzResearch.WordTrace]
  refine ⟨133910387360808016676450809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178547183147744022235267745 133910387360808016676450809)
  ·
    refine ⟨100432790520606012507338107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133910387360808016676450809 100432790520606012507338107)
    ·
      refine ⟨150649185780909018761007161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100432790520606012507338107 150649185780909018761007161)
      ·
        refine ⟨112986889335681764070755371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150649185780909018761007161 112986889335681764070755371)
        ·
          refine ⟨169480334003522646106133057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112986889335681764070755371 169480334003522646106133057)
          ·
            refine ⟨127110250502641984579599793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169480334003522646106133057 127110250502641984579599793)
            ·
              refine ⟨95332687876981488434699845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127110250502641984579599793 95332687876981488434699845)
              ·
                refine ⟨17874878976934029081506221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95332687876981488434699845 17874878976934029081506221)
                ·
                  refine ⟨6703079616350260905564833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17874878976934029081506221 6703079616350260905564833)
                  ·
                    refine ⟨5027309712262695679173625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6703079616350260905564833 5027309712262695679173625)
                    ·
                      refine ⟨3770482284197021759380219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027309712262695679173625 3770482284197021759380219)
                      ·
                        rfl

theorem cell23_7342988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_7342988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7342988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7342988 prefixEnd_7342988 := by exact prefixLift 7342988
  have htrace : WordTrace (prefixWord ++ tailWord_7342988) baseStart_7342988 baseEnd_7342988 := by
    simpa [prefixWord, tailWord_7342988, baseEnd_7342988] using wordTrace_append hprefix tailTrace_7342988
  have hstable : (prefixWord ++ tailWord_7342988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7342988).length < 2 ^ (prefixWord ++ tailWord_7342988).sum := by decide
  have hdescent : baseEnd_7342988 < baseStart_7342988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7342988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343015 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 2, 4]
def baseStart_7343015 : Nat := 118140960795 + 7343015 * 2 ^ 59
def prefixEnd_7343015 : Nat := 4983230072969 + 3 ^ 40 * 7343015 * 2
def baseEnd_7343015 : Nat := 1256832049391564384580865

theorem tailTrace_7343015 : CollatzResearch.WordTrace tailWord_7343015 prefixEnd_7343015 1256832049391564384580865 := by
  unfold tailWord_7343015
  simp only [CollatzResearch.WordTrace]
  refine ⟨267821759492518216964134499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178547839661678811309422999 267821759492518216964134499)
  ·
    refine ⟨401732639238777325446201749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267821759492518216964134499 401732639238777325446201749)
    ·
      refine ⟨18831217464317687130290707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 401732639238777325446201749 18831217464317687130290707)
      ·
        refine ⟨28246826196476530695436061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18831217464317687130290707 28246826196476530695436061)
        ·
          refine ⟨10592559823678699010788523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28246826196476530695436061 10592559823678699010788523)
          ·
            refine ⟨15888839735518048516182785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10592559823678699010788523 15888839735518048516182785)
            ·
              refine ⟨11916629801638536387137089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15888839735518048516182785 11916629801638536387137089)
              ·
                refine ⟨8937472351228902290352817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11916629801638536387137089 8937472351228902290352817)
                ·
                  refine ⟨6703104263421676717764613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8937472351228902290352817 6703104263421676717764613)
                  ·
                    refine ⟨1256832049391564384580865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6703104263421676717764613 1256832049391564384580865)
                    ·
                      rfl

theorem cell23_7343015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_7343015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343015 prefixEnd_7343015 := by exact prefixLift 7343015
  have htrace : WordTrace (prefixWord ++ tailWord_7343015) baseStart_7343015 baseEnd_7343015 := by
    simpa [prefixWord, tailWord_7343015, baseEnd_7343015] using wordTrace_append hprefix tailTrace_7343015
  have hstable : (prefixWord ++ tailWord_7343015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343015).length < 2 ^ (prefixWord ++ tailWord_7343015).sum := by decide
  have hdescent : baseEnd_7343015 < baseStart_7343015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343028 : List Nat := [2, 5, 2, 1, 1, 1, 3, 8]
def baseStart_7343028 : Nat := 118140960795 + 7343028 * 2 ^ 59
def prefixEnd_7343028 : Nat := 4983230072969 + 3 ^ 40 * 7343028 * 2
def baseEnd_7343028 : Nat := 139648252719377837143705

theorem tailTrace_7343028 : CollatzResearch.WordTrace tailWord_7343028 prefixEnd_7343028 139648252719377837143705 := by
  unfold tailWord_7343028
  simp only [CollatzResearch.WordTrace]
  refine ⟨133911116820735560092178869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178548155760980746789571825 133911116820735560092178869)
  ·
    refine ⟨12554167201943958758641769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133911116820735560092178869 12554167201943958758641769)
    ·
      refine ⟨9415625401457969068981327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12554167201943958758641769 9415625401457969068981327)
      ·
        refine ⟨14123438102186953603471991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9415625401457969068981327 14123438102186953603471991)
        ·
          refine ⟨21185157153280430405207987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14123438102186953603471991 21185157153280430405207987)
          ·
            refine ⟨31777735729920645607811981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21185157153280430405207987 31777735729920645607811981)
            ·
              refine ⟨11916650898720242102929493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31777735729920645607811981 11916650898720242102929493)
              ·
                refine ⟨139648252719377837143705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11916650898720242102929493 139648252719377837143705)
                ·
                  rfl

theorem cell23_7343028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 8].length) (baseStart_7343028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343028 prefixEnd_7343028 := by exact prefixLift 7343028
  have htrace : WordTrace (prefixWord ++ tailWord_7343028) baseStart_7343028 baseEnd_7343028 := by
    simpa [prefixWord, tailWord_7343028, baseEnd_7343028] using wordTrace_append hprefix tailTrace_7343028
  have hstable : (prefixWord ++ tailWord_7343028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343028).length < 2 ^ (prefixWord ++ tailWord_7343028).sum := by decide
  have hdescent : baseEnd_7343028 < baseStart_7343028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343038 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_7343038 : Nat := 118140960795 + 7343038 * 2 ^ 59
def prefixEnd_7343038 : Nat := 4983230072969 + 3 ^ 40 * 7343038 * 2
def baseEnd_7343038 : Nat := 3770507958229746563754989

theorem tailTrace_7343038 : CollatzResearch.WordTrace tailWord_7343038 prefixEnd_7343038 3770507958229746563754989 := by
  unfold tailWord_7343038
  simp only [CollatzResearch.WordTrace]
  refine ⟨33477824796429361486527721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178548398914289927928147845 33477824796429361486527721)
  ·
    refine ⟨25108368597322021114895791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33477824796429361486527721 25108368597322021114895791)
    ·
      refine ⟨37662552895983031672343687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25108368597322021114895791 37662552895983031672343687)
      ·
        refine ⟨56493829343974547508515531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37662552895983031672343687 56493829343974547508515531)
        ·
          refine ⟨84740744015961821262773297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56493829343974547508515531 84740744015961821262773297)
          ·
            refine ⟨63555558011971365947079973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84740744015961821262773297 63555558011971365947079973)
            ·
              refine ⟨11916667127244631115077495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63555558011971365947079973 11916667127244631115077495)
              ·
                refine ⟨17875000690866946672616243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11916667127244631115077495 17875000690866946672616243)
                ·
                  refine ⟨26812501036300420008924365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17875000690866946672616243 26812501036300420008924365)
                  ·
                    refine ⟨10054687888612657503346637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26812501036300420008924365 10054687888612657503346637)
                    ·
                      refine ⟨3770507958229746563754989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10054687888612657503346637 3770507958229746563754989)
                      ·
                        rfl

theorem cell23_7343038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_7343038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343038 prefixEnd_7343038 := by exact prefixLift 7343038
  have htrace : WordTrace (prefixWord ++ tailWord_7343038) baseStart_7343038 baseEnd_7343038 := by
    simpa [prefixWord, tailWord_7343038, baseEnd_7343038] using wordTrace_append hprefix tailTrace_7343038
  have hstable : (prefixWord ++ tailWord_7343038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343038).length < 2 ^ (prefixWord ++ tailWord_7343038).sum := by decide
  have hdescent : baseEnd_7343038 < baseStart_7343038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343065 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 1, 3, 2]
def baseStart_7343065 : Nat := 118140960795 + 7343065 * 2 ^ 59
def prefixEnd_7343065 : Nat := 4983230072969 + 3 ^ 40 * 7343065 * 2
def baseEnd_7343065 : Nat := 3770521822207417958117365

theorem tailTrace_7343065 : CollatzResearch.WordTrace tailWord_7343065 prefixEnd_7343065 3770521822207417958117365 := by
  unfold tailWord_7343065
  simp only [CollatzResearch.WordTrace]
  refine ⟨267823583142337075503454649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178549055428224717002303099 267823583142337075503454649)
  ·
    refine ⟨200867687356752806627590987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267823583142337075503454649 200867687356752806627590987)
    ·
      refine ⟨301301531035129209941386481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200867687356752806627590987 301301531035129209941386481)
      ·
        refine ⟨225976148276346907456039861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301301531035129209941386481 225976148276346907456039861)
        ·
          refine ⟨21185263900907522574003737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225976148276346907456039861 21185263900907522574003737)
          ·
            refine ⟨15888947925680641930502803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21185263900907522574003737 15888947925680641930502803)
            ·
              refine ⟨23833421888520962895754205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15888947925680641930502803 23833421888520962895754205)
              ·
                refine ⟨8937533208195361085907827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23833421888520962895754205 8937533208195361085907827)
                ·
                  refine ⟨13406299812293041628861741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8937533208195361085907827 13406299812293041628861741)
                  ·
                    refine ⟨5027362429609890610823153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13406299812293041628861741 5027362429609890610823153)
                    ·
                      refine ⟨3770521822207417958117365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027362429609890610823153 3770521822207417958117365)
                      ·
                        rfl

theorem cell23_7343065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 3, 2].length) (baseStart_7343065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343065 prefixEnd_7343065 := by exact prefixLift 7343065
  have htrace : WordTrace (prefixWord ++ tailWord_7343065) baseStart_7343065 baseEnd_7343065 := by
    simpa [prefixWord, tailWord_7343065, baseEnd_7343065] using wordTrace_append hprefix tailTrace_7343065
  have hstable : (prefixWord ++ tailWord_7343065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343065).length < 2 ^ (prefixWord ++ tailWord_7343065).sum := by decide
  have hdescent : baseEnd_7343065 < baseStart_7343065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343104 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_7343104 : Nat := 118140960795 + 7343104 * 2 ^ 59
def prefixEnd_7343104 : Nat := 4983230072969 + 3 ^ 40 * 7343104 * 2
def baseEnd_7343104 : Nat := 3770541847952943305529685

theorem tailTrace_7343104 : CollatzResearch.WordTrace tailWord_7343104 prefixEnd_7343104 3770541847952943305529685 := by
  unfold tailWord_7343104
  simp only [CollatzResearch.WordTrace]
  refine ⟨133912502794597892582062183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178550003726130523442749577 133912502794597892582062183)
  ·
    refine ⟨200868754191896838873093275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133912502794597892582062183 200868754191896838873093275)
    ·
      refine ⟨301303131287845258309639913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200868754191896838873093275 301303131287845258309639913)
      ·
        refine ⟨225977348465883943732229935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301303131287845258309639913 225977348465883943732229935)
        ·
          refine ⟨338966022698825915598344903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225977348465883943732229935 338966022698825915598344903)
          ·
            refine ⟨508449034048238873397517355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338966022698825915598344903 508449034048238873397517355)
            ·
              refine ⟨762673551072358310096276033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508449034048238873397517355 762673551072358310096276033)
              ·
                refine ⟨572005163304268732572207025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762673551072358310096276033 572005163304268732572207025)
                ·
                  refine ⟨429003872478201549429155269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572005163304268732572207025 429003872478201549429155269)
                  ·
                    refine ⟨80438226089662790517966613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 429003872478201549429155269 80438226089662790517966613)
                    ·
                      refine ⟨3770541847952943305529685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80438226089662790517966613 3770541847952943305529685)
                      ·
                        rfl

theorem cell23_7343104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_7343104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343104 prefixEnd_7343104 := by exact prefixLift 7343104
  have htrace : WordTrace (prefixWord ++ tailWord_7343104) baseStart_7343104 baseEnd_7343104 := by
    simpa [prefixWord, tailWord_7343104, baseEnd_7343104] using wordTrace_append hprefix tailTrace_7343104
  have hstable : (prefixWord ++ tailWord_7343104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343104).length < 2 ^ (prefixWord ++ tailWord_7343104).sum := by decide
  have hdescent : baseEnd_7343104 < baseStart_7343104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343135 : List Nat := [1, 1, 2, 4, 1, 4, 3, 2, 5]
def baseStart_7343135 : Nat := 118140960795 + 7343135 * 2 ^ 59
def prefixEnd_7343135 : Nat := 4983230072969 + 3 ^ 40 * 7343135 * 2
def baseEnd_7343135 : Nat := 418950862872581409360227

theorem tailTrace_7343135 : CollatzResearch.WordTrace tailWord_7343135 prefixEnd_7343135 418950862872581409360227 := by
  unfold tailWord_7343135
  simp only [CollatzResearch.WordTrace]
  refine ⟨267826136252083477458502859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178550757501388984972335239 267826136252083477458502859)
  ·
    refine ⟨401739204378125216187754289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267826136252083477458502859 401739204378125216187754289)
    ·
      refine ⟨301304403283593912140815717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401739204378125216187754289 301304403283593912140815717)
      ·
        refine ⟨56494575615673858526402947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301304403283593912140815717 56494575615673858526402947)
        ·
          refine ⟨84741863423510787789604421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56494575615673858526402947 84741863423510787789604421)
          ·
            refine ⟨15889099391908272710550829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84741863423510787789604421 15889099391908272710550829)
            ·
              refine ⟨5958412271965602266456561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15889099391908272710550829 5958412271965602266456561)
              ·
                refine ⟨4468809203974201699842421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5958412271965602266456561 4468809203974201699842421)
                ·
                  refine ⟨418950862872581409360227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4468809203974201699842421 418950862872581409360227)
                  ·
                    rfl

theorem cell23_7343135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 5].length) (baseStart_7343135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343135 prefixEnd_7343135 := by exact prefixLift 7343135
  have htrace : WordTrace (prefixWord ++ tailWord_7343135) baseStart_7343135 baseEnd_7343135 := by
    simpa [prefixWord, tailWord_7343135, baseEnd_7343135] using wordTrace_append hprefix tailTrace_7343135
  have hstable : (prefixWord ++ tailWord_7343135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343135).length < 2 ^ (prefixWord ++ tailWord_7343135).sum := by decide
  have hdescent : baseEnd_7343135 < baseStart_7343135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343141 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_7343141 : Nat := 118140960795 + 7343141 * 2 ^ 59
def prefixEnd_7343141 : Nat := 4983230072969 + 3 ^ 40 * 7343141 * 2
def baseEnd_7343141 : Nat := 3770560846737159660767015

theorem tailTrace_7343141 : CollatzResearch.WordTrace tailWord_7343141 prefixEnd_7343141 3770560846737159660767015 := by
  unfold tailWord_7343141
  simp only [CollatzResearch.WordTrace]
  refine ⟨267826355090061740483221277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178550903393374493655480851 267826355090061740483221277)
  ·
    refine ⟨100434883158773152681207979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267826355090061740483221277 100434883158773152681207979)
    ·
      refine ⟨150652324738159729021811969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100434883158773152681207979 150652324738159729021811969)
      ·
        refine ⟨112989243553619796766358977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150652324738159729021811969 112989243553619796766358977)
        ·
          refine ⟨84741932665214847574769233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112989243553619796766358977 84741932665214847574769233)
          ·
            refine ⟨63556449498911135681076925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84741932665214847574769233 63556449498911135681076925)
            ·
              refine ⟨23833668562091675880403847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63556449498911135681076925 23833668562091675880403847)
              ·
                refine ⟨35750502843137513820605771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23833668562091675880403847 35750502843137513820605771)
                ·
                  refine ⟨53625754264706270730908657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35750502843137513820605771 53625754264706270730908657)
                  ·
                    refine ⟨40219315698529703048181493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53625754264706270730908657 40219315698529703048181493)
                    ·
                      refine ⟨3770560846737159660767015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40219315698529703048181493 3770560846737159660767015)
                      ·
                        rfl

theorem cell23_7343141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_7343141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343141 prefixEnd_7343141 := by exact prefixLift 7343141
  have htrace : WordTrace (prefixWord ++ tailWord_7343141) baseStart_7343141 baseEnd_7343141 := by
    simpa [prefixWord, tailWord_7343141, baseEnd_7343141] using wordTrace_append hprefix tailTrace_7343141
  have hstable : (prefixWord ++ tailWord_7343141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343141).length < 2 ^ (prefixWord ++ tailWord_7343141).sum := by decide
  have hdescent : baseEnd_7343141 < baseStart_7343141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343146 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_7343146 : Nat := 118140960795 + 7343146 * 2 ^ 59
def prefixEnd_7343146 : Nat := 4983230072969 + 3 ^ 40 * 7343146 * 2
def baseEnd_7343146 : Nat := 3770563414140432141204493

theorem tailTrace_7343146 : CollatzResearch.WordTrace tailWord_7343146 prefixEnd_7343146 3770563414140432141204493 := by
  unfold tailWord_7343146
  simp only [CollatzResearch.WordTrace]
  refine ⟨66956634363760906584288323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178551024970029084224768861 66956634363760906584288323)
  ·
    refine ⟨100434951545641359876432485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66956634363760906584288323 100434951545641359876432485)
    ·
      refine ⟨18831553414807754976831091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100434951545641359876432485 18831553414807754976831091)
      ·
        refine ⟨28247330122211632465246637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18831553414807754976831091 28247330122211632465246637)
        ·
          refine ⟨10592748795829362174467489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28247330122211632465246637 10592748795829362174467489)
          ·
            refine ⟨7944561596872021630850617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10592748795829362174467489 7944561596872021630850617)
            ·
              refine ⟨5958421197654016223137963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7944561596872021630850617 5958421197654016223137963)
              ·
                refine ⟨8937631796481024334706945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5958421197654016223137963 8937631796481024334706945)
                ·
                  refine ⟨6703223847360768251030209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8937631796481024334706945 6703223847360768251030209)
                  ·
                    refine ⟨5027417885520576188272657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6703223847360768251030209 5027417885520576188272657)
                    ·
                      refine ⟨3770563414140432141204493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027417885520576188272657 3770563414140432141204493)
                      ·
                        rfl

theorem cell23_7343146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_7343146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343146 prefixEnd_7343146 := by exact prefixLift 7343146
  have htrace : WordTrace (prefixWord ++ tailWord_7343146) baseStart_7343146 baseEnd_7343146 := by
    simpa [prefixWord, tailWord_7343146, baseEnd_7343146] using wordTrace_append hprefix tailTrace_7343146
  have hstable : (prefixWord ++ tailWord_7343146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343146).length < 2 ^ (prefixWord ++ tailWord_7343146).sum := by decide
  have hdescent : baseEnd_7343146 < baseStart_7343146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343168 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 4]
def baseStart_7343168 : Nat := 118140960795 + 7343168 * 2 ^ 59
def prefixEnd_7343168 : Nat := 4983230072969 + 3 ^ 40 * 7343168 * 2
def baseEnd_7343168 : Nat := 3770574710714831055129391

theorem tailTrace_7343168 : CollatzResearch.WordTrace tailWord_7343168 prefixEnd_7343168 3770574710714831055129391 := by
  unfold tailWord_7343168
  simp only [CollatzResearch.WordTrace]
  refine ⟨133913669930481962047227079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178551559907309282729636105 133913669930481962047227079)
  ·
    refine ⟨200870504895722943070840619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133913669930481962047227079 200870504895722943070840619)
    ·
      refine ⟨301305757343584414606260929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200870504895722943070840619 301305757343584414606260929)
      ·
        refine ⟨225979318007688310954695697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301305757343584414606260929 225979318007688310954695697)
        ·
          refine ⟨169484488505766233216021773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225979318007688310954695697 169484488505766233216021773)
          ·
            refine ⟨63556683189662337456008165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169484488505766233216021773 63556683189662337456008165)
            ·
              refine ⟨11916878098061688273001531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63556683189662337456008165 11916878098061688273001531)
              ·
                refine ⟨17875317147092532409502297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11916878098061688273001531 17875317147092532409502297)
                ·
                  refine ⟨13406487860319399307126723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17875317147092532409502297 13406487860319399307126723)
                  ·
                    refine ⟨20109731790479098960690085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13406487860319399307126723 20109731790479098960690085)
                    ·
                      refine ⟨3770574710714831055129391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20109731790479098960690085 3770574710714831055129391)
                      ·
                        rfl

theorem cell23_7343168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_7343168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343168 prefixEnd_7343168 := by exact prefixLift 7343168
  have htrace : WordTrace (prefixWord ++ tailWord_7343168) baseStart_7343168 baseEnd_7343168 := by
    simpa [prefixWord, tailWord_7343168, baseEnd_7343168] using wordTrace_append hprefix tailTrace_7343168
  have hstable : (prefixWord ++ tailWord_7343168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343168).length < 2 ^ (prefixWord ++ tailWord_7343168).sum := by decide
  have hdescent : baseEnd_7343168 < baseStart_7343168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343202 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7343202 : Nat := 118140960795 + 7343202 * 2 ^ 59
def prefixEnd_7343202 : Nat := 4983230072969 + 3 ^ 40 * 7343202 * 2
def baseEnd_7343202 : Nat := 3770592169057083922104235

theorem tailTrace_7343202 : CollatzResearch.WordTrace tailWord_7343202 prefixEnd_7343202 3770592169057083922104235 := by
  unfold tailWord_7343202
  simp only [CollatzResearch.WordTrace]
  refine ⟨66957144985710186975297965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178552386628560498600794573 66957144985710186975297965)
  ·
    refine ⟨25108929369641320115736737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66957144985710186975297965 25108929369641320115736737)
    ·
      refine ⟨18831697027230990086802553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25108929369641320115736737 18831697027230990086802553)
      ·
        refine ⟨14123772770423242565101915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18831697027230990086802553 14123772770423242565101915)
        ·
          refine ⟨21185659155634863847652873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14123772770423242565101915 21185659155634863847652873)
          ·
            refine ⟨15889244366726147885739655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21185659155634863847652873 15889244366726147885739655)
            ·
              refine ⟨23833866550089221828609483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15889244366726147885739655 23833866550089221828609483)
              ·
                refine ⟨35750799825133832742914225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23833866550089221828609483 35750799825133832742914225)
                ·
                  refine ⟨26813099868850374557185669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35750799825133832742914225 26813099868850374557185669)
                  ·
                    refine ⟨5027456225409445229472313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26813099868850374557185669 5027456225409445229472313)
                    ·
                      refine ⟨3770592169057083922104235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027456225409445229472313 3770592169057083922104235)
                      ·
                        rfl

theorem cell23_7343202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7343202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343202 prefixEnd_7343202 := by exact prefixLift 7343202
  have htrace : WordTrace (prefixWord ++ tailWord_7343202) baseStart_7343202 baseEnd_7343202 := by
    simpa [prefixWord, tailWord_7343202, baseEnd_7343202] using wordTrace_append hprefix tailTrace_7343202
  have hstable : (prefixWord ++ tailWord_7343202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343202).length < 2 ^ (prefixWord ++ tailWord_7343202).sum := by decide
  have hdescent : baseEnd_7343202 < baseStart_7343202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343251 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 3, 6]
def baseStart_7343251 : Nat := 118140960795 + 7343251 * 2 ^ 59
def prefixEnd_7343251 : Nat := 4983230072969 + 3 ^ 40 * 7343251 * 2
def baseEnd_7343251 : Nat := 1256872443203051410130503

theorem tailTrace_7343251 : CollatzResearch.WordTrace tailWord_7343251 prefixEnd_7343251 1256872443203051410130503 := by
  unfold tailWord_7343251
  simp only [CollatzResearch.WordTrace]
  refine ⟨267830367119663229269725607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178553578079775486179817071 267830367119663229269725607)
  ·
    refine ⟨401745550679494843904588411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267830367119663229269725607 401745550679494843904588411)
    ·
      refine ⟨602618326019242265856882617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401745550679494843904588411 602618326019242265856882617)
      ·
        refine ⟨451963744514431699392661963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602618326019242265856882617 451963744514431699392661963)
        ·
          refine ⟨677945616771647549088992945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451963744514431699392661963 677945616771647549088992945)
          ·
            refine ⟨508459212578735661816744709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677945616771647549088992945 508459212578735661816744709)
            ·
              refine ⟨95336102358512936590639633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 508459212578735661816744709 95336102358512936590639633)
              ·
                refine ⟨71502076768884702442979725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95336102358512936590639633 71502076768884702442979725)
                ·
                  refine ⟨26813278788331763416117397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71502076768884702442979725 26813278788331763416117397)
                  ·
                    refine ⟨1256872443203051410130503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26813278788331763416117397 1256872443203051410130503)
                    ·
                      rfl

theorem cell23_7343251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 6].length) (baseStart_7343251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343251 prefixEnd_7343251 := by exact prefixLift 7343251
  have htrace : WordTrace (prefixWord ++ tailWord_7343251) baseStart_7343251 baseEnd_7343251 := by
    simpa [prefixWord, tailWord_7343251, baseEnd_7343251] using wordTrace_append hprefix tailTrace_7343251
  have hstable : (prefixWord ++ tailWord_7343251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343251).length < 2 ^ (prefixWord ++ tailWord_7343251).sum := by decide
  have hdescent : baseEnd_7343251 < baseStart_7343251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343262 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_7343262 : Nat := 118140960795 + 7343262 * 2 ^ 59
def prefixEnd_7343262 : Nat := 4983230072969 + 3 ^ 40 * 7343262 * 2
def baseEnd_7343262 : Nat := 3770622977896353687353959

theorem tailTrace_7343262 : CollatzResearch.WordTrace tailWord_7343262 prefixEnd_7343262 3770622977896353687353959 := by
  unfold tailWord_7343262
  simp only [CollatzResearch.WordTrace]
  refine ⟨33478846040327922268547005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178553845548415585432250693 33478846040327922268547005)
  ·
    refine ⟨12554567265122970850705127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33478846040327922268547005 12554567265122970850705127)
    ·
      refine ⟨18831850897684456276057691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12554567265122970850705127 18831850897684456276057691)
      ·
        refine ⟨28247776346526684414086537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18831850897684456276057691 28247776346526684414086537)
        ·
          refine ⟨21185832259895013310564903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28247776346526684414086537 21185832259895013310564903)
          ·
            refine ⟨31778748389842519965847355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21185832259895013310564903 31778748389842519965847355)
            ·
              refine ⟨47668122584763779948771033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31778748389842519965847355 47668122584763779948771033)
              ·
                refine ⟨35751091938572834961578275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47668122584763779948771033 35751091938572834961578275)
                ·
                  refine ⟨53626637907859252442367413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35751091938572834961578275 53626637907859252442367413)
                  ·
                    refine ⟨5027497303861804916471945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53626637907859252442367413 5027497303861804916471945)
                    ·
                      refine ⟨3770622977896353687353959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027497303861804916471945 3770622977896353687353959)
                      ·
                        rfl

theorem cell23_7343262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_7343262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343262 prefixEnd_7343262 := by exact prefixLift 7343262
  have htrace : WordTrace (prefixWord ++ tailWord_7343262) baseStart_7343262 baseEnd_7343262 := by
    simpa [prefixWord, tailWord_7343262, baseEnd_7343262] using wordTrace_append hprefix tailTrace_7343262
  have hstable : (prefixWord ++ tailWord_7343262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343262).length < 2 ^ (prefixWord ++ tailWord_7343262).sum := by decide
  have hdescent : baseEnd_7343262 < baseStart_7343262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343295 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 1, 2, 3]
def baseStart_7343295 : Nat := 118140960795 + 7343295 * 2 ^ 59
def prefixEnd_7343295 : Nat := 4983230072969 + 3 ^ 40 * 7343295 * 2
def baseEnd_7343295 : Nat := 3770639922757952058241307

theorem tailTrace_7343295 : CollatzResearch.WordTrace tailWord_7343295 prefixEnd_7343295 3770639922757952058241307 := by
  unfold tailWord_7343295
  simp only [CollatzResearch.WordTrace]
  refine ⟨267831971931503824784327339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178554647954335883189551559 267831971931503824784327339)
  ·
    refine ⟨401747957897255737176491009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267831971931503824784327339 401747957897255737176491009)
    ·
      refine ⟨301310968422941802882368257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401747957897255737176491009 301310968422941802882368257)
      ·
        refine ⟨225983226317206352161776193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301310968422941802882368257 225983226317206352161776193)
        ·
          refine ⟨169487419737904764121332145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225983226317206352161776193 169487419737904764121332145)
          ·
            refine ⟨127115564803428573090999109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169487419737904764121332145 127115564803428573090999109)
            ·
              refine ⟨23834168400642857454562333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127115564803428573090999109 23834168400642857454562333)
              ·
                refine ⟨8937813150241071545460875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23834168400642857454562333 8937813150241071545460875)
                ·
                  refine ⟨13406719725361607318191313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8937813150241071545460875 13406719725361607318191313)
                  ·
                    refine ⟨10055039794021205488643485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13406719725361607318191313 10055039794021205488643485)
                    ·
                      refine ⟨3770639922757952058241307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10055039794021205488643485 3770639922757952058241307)
                      ·
                        rfl

theorem cell23_7343295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_7343295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343295 prefixEnd_7343295 := by exact prefixLift 7343295
  have htrace : WordTrace (prefixWord ++ tailWord_7343295) baseStart_7343295 baseEnd_7343295 := by
    simpa [prefixWord, tailWord_7343295, baseEnd_7343295] using wordTrace_append hprefix tailTrace_7343295
  have hstable : (prefixWord ++ tailWord_7343295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343295).length < 2 ^ (prefixWord ++ tailWord_7343295).sum := by decide
  have hdescent : baseEnd_7343295 < baseStart_7343295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343365 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 3, 4, 2]
def baseStart_7343365 : Nat := 118140960795 + 7343365 * 2 ^ 59
def prefixEnd_7343365 : Nat := 4983230072969 + 3 ^ 40 * 7343365 * 2
def baseEnd_7343365 : Nat := 3770675866403766784365985

theorem tailTrace_7343365 : CollatzResearch.WordTrace tailWord_7343365 prefixEnd_7343365 3770675866403766784365985 := by
  unfold tailWord_7343365
  simp only [CollatzResearch.WordTrace]
  refine ⟨267834525041250226739375549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178556350027500151159583699 267834525041250226739375549)
  ·
    refine ⟨100437946890468835027265831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267834525041250226739375549 100437946890468835027265831)
    ·
      refine ⟨150656920335703252540898747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100437946890468835027265831 150656920335703252540898747)
      ·
        refine ⟨225985380503554878811348121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150656920335703252540898747 225985380503554878811348121)
        ·
          refine ⟨169489035377666159108511091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225985380503554878811348121 169489035377666159108511091)
          ·
            refine ⟨254233553066499238662766637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169489035377666159108511091 254233553066499238662766637)
            ·
              refine ⟨95337582399937214498537489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254233553066499238662766637 95337582399937214498537489)
              ·
                refine ⟨71503186799952910873903117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95337582399937214498537489 71503186799952910873903117)
                ·
                  refine ⟨26813695049982341577713669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71503186799952910873903117 26813695049982341577713669)
                  ·
                    refine ⟨5027567821871689045821313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26813695049982341577713669 5027567821871689045821313)
                    ·
                      refine ⟨3770675866403766784365985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027567821871689045821313 3770675866403766784365985)
                      ·
                        rfl

theorem cell23_7343365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 4, 2].length) (baseStart_7343365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343365 prefixEnd_7343365 := by exact prefixLift 7343365
  have htrace : WordTrace (prefixWord ++ tailWord_7343365) baseStart_7343365 baseEnd_7343365 := by
    simpa [prefixWord, tailWord_7343365, baseEnd_7343365] using wordTrace_append hprefix tailTrace_7343365
  have hstable : (prefixWord ++ tailWord_7343365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343365).length < 2 ^ (prefixWord ++ tailWord_7343365).sum := by decide
  have hdescent : baseEnd_7343365 < baseStart_7343365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343388 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 9]
def baseStart_7343388 : Nat := 118140960795 + 7343388 * 2 ^ 59
def prefixEnd_7343388 : Nat := 4983230072969 + 3 ^ 40 * 7343388 * 2
def baseEnd_7343388 : Nat := 418965297384313354930931

theorem tailTrace_7343388 : CollatzResearch.WordTrace tailWord_7343388 prefixEnd_7343388 418965297384313354930931 := by
  unfold tailWord_7343388
  simp only [CollatzResearch.WordTrace]
  refine ⟨133917681960083450833731409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178556909280111267778308545 133917681960083450833731409)
  ·
    refine ⟨100438261470062588125298557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133917681960083450833731409 100438261470062588125298557)
    ·
      refine ⟨37664348051273470546986959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100438261470062588125298557 37664348051273470546986959)
      ·
        refine ⟨56496522076910205820480439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37664348051273470546986959 56496522076910205820480439)
        ·
          refine ⟨84744783115365308730720659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56496522076910205820480439 84744783115365308730720659)
          ·
            refine ⟨127117174673047963096080989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84744783115365308730720659 127117174673047963096080989)
            ·
              refine ⟨47668940502392986161030371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127117174673047963096080989 47668940502392986161030371)
              ·
                refine ⟨71503410753589479241545557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47668940502392986161030371 71503410753589479241545557)
                ·
                  refine ⟨418965297384313354930931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71503410753589479241545557 418965297384313354930931)
                  ·
                    rfl

theorem cell23_7343388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_7343388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343388 prefixEnd_7343388 := by exact prefixLift 7343388
  have htrace : WordTrace (prefixWord ++ tailWord_7343388) baseStart_7343388 baseEnd_7343388 := by
    simpa [prefixWord, tailWord_7343388, baseEnd_7343388] using wordTrace_append hprefix tailTrace_7343388
  have hstable : (prefixWord ++ tailWord_7343388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343388).length < 2 ^ (prefixWord ++ tailWord_7343388).sum := by decide
  have hdescent : baseEnd_7343388 < baseStart_7343388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343422 : List Nat := [4, 2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_7343422 : Nat := 118140960795 + 7343422 * 2 ^ 59
def prefixEnd_7343422 : Nat := 4983230072969 + 3 ^ 40 * 7343422 * 2
def baseEnd_7343422 : Nat := 418967237200119229039247

theorem tailTrace_7343422 : CollatzResearch.WordTrace tailWord_7343422 prefixEnd_7343422 418967237200119229039247 := by
  unfold tailWord_7343422
  simp only [CollatzResearch.WordTrace]
  refine ⟨33479575500255465684275065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178557736001362483649467013 33479575500255465684275065)
  ·
    refine ⟨25109681625191599263206299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33479575500255465684275065 25109681625191599263206299)
    ·
      refine ⟨37664522437787398894809449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25109681625191599263206299 37664522437787398894809449)
      ·
        refine ⟨28248391828340549171107087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37664522437787398894809449 28248391828340549171107087)
        ·
          refine ⟨42372587742510823756660631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28248391828340549171107087 42372587742510823756660631)
          ·
            refine ⟨63558881613766235634990947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42372587742510823756660631 63558881613766235634990947)
            ·
              refine ⟨95338322420649353452486421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63558881613766235634990947 95338322420649353452486421)
              ·
                refine ⟨4468983863467938443085301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95338322420649353452486421 4468983863467938443085301)
                ·
                  refine ⟨418967237200119229039247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4468983863467938443085301 418967237200119229039247)
                  ·
                    rfl

theorem cell23_7343422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_7343422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343422 prefixEnd_7343422 := by exact prefixLift 7343422
  have htrace : WordTrace (prefixWord ++ tailWord_7343422) baseStart_7343422 baseEnd_7343422 := by
    simpa [prefixWord, tailWord_7343422, baseEnd_7343422] using wordTrace_append hprefix tailTrace_7343422
  have hstable : (prefixWord ++ tailWord_7343422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343422).length < 2 ^ (prefixWord ++ tailWord_7343422).sum := by decide
  have hdescent : baseEnd_7343422 < baseStart_7343422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343448 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 2, 8]
def baseStart_7343448 : Nat := 118140960795 + 7343448 * 2 ^ 59
def prefixEnd_7343448 : Nat := 4983230072969 + 3 ^ 40 * 7343448 * 2
def baseEnd_7343448 : Nat := 1256906161766029986542701

theorem tailTrace_7343448 : CollatzResearch.WordTrace tailWord_7343448 prefixEnd_7343448 1256906161766029986542701 := by
  unfold tailWord_7343448
  simp only [CollatzResearch.WordTrace]
  refine ⟨133918776149974765957323499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178558368199966354609764665 133918776149974765957323499)
  ·
    refine ⟨200878164224962148935985249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133918776149974765957323499 200878164224962148935985249)
    ·
      refine ⟨150658623168721611701988937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200878164224962148935985249 150658623168721611701988937)
      ·
        refine ⟨112993967376541208776491703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150658623168721611701988937 112993967376541208776491703)
        ·
          refine ⟨169490951064811813164737555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112993967376541208776491703 169490951064811813164737555)
          ·
            refine ⟨254236426597217719747106333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169490951064811813164737555 254236426597217719747106333)
            ·
              refine ⟨95338659973956644905164875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254236426597217719747106333 95338659973956644905164875)
              ·
                refine ⟨143007989960934967357747313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95338659973956644905164875 143007989960934967357747313)
                ·
                  refine ⟨107255992470701225518310485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143007989960934967357747313 107255992470701225518310485)
                  ·
                    refine ⟨1256906161766029986542701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107255992470701225518310485 1256906161766029986542701)
                    ·
                      rfl

theorem cell23_7343448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_7343448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343448 prefixEnd_7343448 := by exact prefixLift 7343448
  have htrace : WordTrace (prefixWord ++ tailWord_7343448) baseStart_7343448 baseEnd_7343448 := by
    simpa [prefixWord, tailWord_7343448, baseEnd_7343448] using wordTrace_append hprefix tailTrace_7343448
  have hstable : (prefixWord ++ tailWord_7343448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343448).length < 2 ^ (prefixWord ++ tailWord_7343448).sum := by decide
  have hdescent : baseEnd_7343448 < baseStart_7343448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343455 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 4]
def baseStart_7343455 : Nat := 118140960795 + 7343455 * 2 ^ 59
def prefixEnd_7343455 : Nat := 4983230072969 + 3 ^ 40 * 7343455 * 2
def baseEnd_7343455 : Nat := 3770722079662671432240571

theorem tailTrace_7343455 : CollatzResearch.WordTrace tailWord_7343455 prefixEnd_7343455 3770722079662671432240571 := by
  unfold tailWord_7343455
  simp only [CollatzResearch.WordTrace]
  refine ⟨267837807610924172110151819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178558538407282781406767879 267837807610924172110151819)
  ·
    refine ⟨401756711416386258165227729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267837807610924172110151819 401756711416386258165227729)
    ·
      refine ⟨301317533562289693623920797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401756711416386258165227729 301317533562289693623920797)
      ·
        refine ⟨112994075085858635108970299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301317533562289693623920797 112994075085858635108970299)
        ·
          refine ⟨169491112628787952663455449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112994075085858635108970299 169491112628787952663455449)
          ·
            refine ⟨127118334471590964497591587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169491112628787952663455449 127118334471590964497591587)
            ·
              refine ⟨190677501707386446746387381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127118334471590964497591587 190677501707386446746387381)
              ·
                refine ⟨17876015785067479382473817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190677501707386446746387381 17876015785067479382473817)
                ·
                  refine ⟨13407011838800609536855363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17876015785067479382473817 13407011838800609536855363)
                  ·
                    refine ⟨20110517758200914305283045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13407011838800609536855363 20110517758200914305283045)
                    ·
                      refine ⟨3770722079662671432240571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20110517758200914305283045 3770722079662671432240571)
                      ·
                        rfl

theorem cell23_7343455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_7343455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343455 prefixEnd_7343455 := by exact prefixLift 7343455
  have htrace : WordTrace (prefixWord ++ tailWord_7343455) baseStart_7343455 baseEnd_7343455 := by
    simpa [prefixWord, tailWord_7343455, baseEnd_7343455] using wordTrace_append hprefix tailTrace_7343455
  have hstable : (prefixWord ++ tailWord_7343455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343455).length < 2 ^ (prefixWord ++ tailWord_7343455).sum := by decide
  have hdescent : baseEnd_7343455 < baseStart_7343455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343506 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7343506 : Nat := 118140960795 + 7343506 * 2 ^ 59
def prefixEnd_7343506 : Nat := 4983230072969 + 3 ^ 40 * 7343506 * 2
def baseEnd_7343506 : Nat := 3770748267176050732702837

theorem tailTrace_7343506 : CollatzResearch.WordTrace tailWord_7343506 prefixEnd_7343506 3770748267176050732702837 := by
  unfold tailWord_7343506
  simp only [CollatzResearch.WordTrace]
  refine ⟨66959916933434851955064593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178559778489159605213505581 66959916933434851955064593)
  ·
    refine ⟨50219937700076138966298445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66959916933434851955064593 50219937700076138966298445)
    ·
      refine ⟨18832476637528552112361917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50219937700076138966298445 18832476637528552112361917)
      ·
        refine ⟨7062178739073207042135719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18832476637528552112361917 7062178739073207042135719)
        ·
          refine ⟨10593268108609810563203579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7062178739073207042135719 10593268108609810563203579)
          ·
            refine ⟨15889902162914715844805369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10593268108609810563203579 15889902162914715844805369)
            ·
              refine ⟨11917426622186036883604027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15889902162914715844805369 11917426622186036883604027)
              ·
                refine ⟨17876139933279055325406041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11917426622186036883604027 17876139933279055325406041)
                ·
                  refine ⟨13407104949959291494054531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17876139933279055325406041 13407104949959291494054531)
                  ·
                    refine ⟨20110657424938937241081797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13407104949959291494054531 20110657424938937241081797)
                    ·
                      refine ⟨3770748267176050732702837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20110657424938937241081797 3770748267176050732702837)
                      ·
                        rfl

theorem cell23_7343506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7343506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343506 prefixEnd_7343506 := by exact prefixLift 7343506
  have htrace : WordTrace (prefixWord ++ tailWord_7343506) baseStart_7343506 baseEnd_7343506 := by
    simpa [prefixWord, tailWord_7343506, baseEnd_7343506] using wordTrace_append hprefix tailTrace_7343506
  have hstable : (prefixWord ++ tailWord_7343506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343506).length < 2 ^ (prefixWord ++ tailWord_7343506).sum := by decide
  have hdescent : baseEnd_7343506 < baseStart_7343506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343533 : List Nat := [1, 5, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_7343533 : Nat := 118140960795 + 7343533 * 2 ^ 59
def prefixEnd_7343533 : Nat := 4983230072969 + 3 ^ 40 * 7343533 * 2
def baseEnd_7343533 : Nat := 1256920710384574042355071

theorem tailTrace_7343533 : CollatzResearch.WordTrace tailWord_7343533 prefixEnd_7343533 1256920710384574042355071 := by
  unfold tailWord_7343533
  simp only [CollatzResearch.WordTrace]
  refine ⟨267840652504641591431491253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178560435003094394287660835 267840652504641591431491253)
  ·
    refine ⟨25110061172310149196702305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267840652504641591431491253 25110061172310149196702305)
    ·
      refine ⟨18832545879232611897526729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25110061172310149196702305 18832545879232611897526729)
      ·
        refine ⟨14124409409424458923145047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18832545879232611897526729 14124409409424458923145047)
        ·
          refine ⟨21186614114136688384717571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14124409409424458923145047 21186614114136688384717571)
          ·
            refine ⟨31779921171205032577076357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21186614114136688384717571 31779921171205032577076357)
            ·
              refine ⟨5958735219600943608201817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31779921171205032577076357 5958735219600943608201817)
              ·
                refine ⟨4469051414700707706151363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5958735219600943608201817 4469051414700707706151363)
                ·
                  refine ⟨6703577122051061559227045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4469051414700707706151363 6703577122051061559227045)
                  ·
                    refine ⟨1256920710384574042355071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6703577122051061559227045 1256920710384574042355071)
                    ·
                      rfl

theorem cell23_7343533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_7343533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343533 prefixEnd_7343533 := by exact prefixLift 7343533
  have htrace : WordTrace (prefixWord ++ tailWord_7343533) baseStart_7343533 baseEnd_7343533 := by
    simpa [prefixWord, tailWord_7343533, baseEnd_7343533] using wordTrace_append hprefix tailTrace_7343533
  have hstable : (prefixWord ++ tailWord_7343533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343533).length < 2 ^ (prefixWord ++ tailWord_7343533).sum := by decide
  have hdescent : baseEnd_7343533 < baseStart_7343533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343555 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 1, 6]
def baseStart_7343555 : Nat := 118140960795 + 7343555 * 2 ^ 59
def prefixEnd_7343555 : Nat := 4983230072969 + 3 ^ 40 * 7343555 * 2
def baseEnd_7343555 : Nat := 1256924475909373680330037

theorem tailTrace_7343555 : CollatzResearch.WordTrace tailWord_7343555 prefixEnd_7343555 1256924475909373680330037 := by
  unfold tailWord_7343555
  simp only [CollatzResearch.WordTrace]
  refine ⟨267841454910561889188792119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178560969940374592792528079 267841454910561889188792119)
  ·
    refine ⟨401762182365842833783188179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267841454910561889188792119 401762182365842833783188179)
    ·
      refine ⟨602643273548764250674782269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401762182365842833783188179 602643273548764250674782269)
      ·
        refine ⟨225991227580786594003043351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 602643273548764250674782269 225991227580786594003043351)
        ·
          refine ⟨338986841371179891004565027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225991227580786594003043351 338986841371179891004565027)
          ·
            refine ⟨508480262056769836506847541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338986841371179891004565027 508480262056769836506847541)
            ·
              refine ⟨47670024567822172172516957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 508480262056769836506847541 47670024567822172172516957)
              ·
                refine ⟨17876259212933314564693859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47670024567822172172516957 17876259212933314564693859)
                ·
                  refine ⟨26814388819399971847040789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17876259212933314564693859 26814388819399971847040789)
                  ·
                    refine ⟨1256924475909373680330037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26814388819399971847040789 1256924475909373680330037)
                    ·
                      rfl

theorem cell23_7343555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 6].length) (baseStart_7343555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343555 prefixEnd_7343555 := by exact prefixLift 7343555
  have htrace : WordTrace (prefixWord ++ tailWord_7343555) baseStart_7343555 baseEnd_7343555 := by
    simpa [prefixWord, tailWord_7343555, baseEnd_7343555] using wordTrace_append hprefix tailTrace_7343555
  have hstable : (prefixWord ++ tailWord_7343555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343555).length < 2 ^ (prefixWord ++ tailWord_7343555).sum := by decide
  have hdescent : baseEnd_7343555 < baseStart_7343555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343556 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_7343556 : Nat := 118140960795 + 7343556 * 2 ^ 59
def prefixEnd_7343556 : Nat := 4983230072969 + 3 ^ 40 * 7343556 * 2
def baseEnd_7343556 : Nat := 3770773941208775537077607

theorem tailTrace_7343556 : CollatzResearch.WordTrace tailWord_7343556 prefixEnd_7343556 3770773941208775537077607 := by
  unfold tailWord_7343556
  simp only [CollatzResearch.WordTrace]
  refine ⟨133920745691779133179789261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178560994255705510906385681 133920745691779133179789261)
  ·
    refine ⟨50220279634417174942420973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133920745691779133179789261 50220279634417174942420973)
    ·
      refine ⟨18832604862906440603407865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50220279634417174942420973 18832604862906440603407865)
      ·
        refine ⟨14124453647179830452555899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18832604862906440603407865 14124453647179830452555899)
        ·
          refine ⟨21186680470769745678833849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14124453647179830452555899 21186680470769745678833849)
          ·
            refine ⟨15890010353077309259125387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21186680470769745678833849 15890010353077309259125387)
            ·
              refine ⟨23835015529615963888688081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15890010353077309259125387 23835015529615963888688081)
              ·
                refine ⟨17876261647211972916516061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23835015529615963888688081 17876261647211972916516061)
                ·
                  refine ⟨6703598117704489843693523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17876261647211972916516061 6703598117704489843693523)
                  ·
                    refine ⟨10055397176556734765540285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6703598117704489843693523 10055397176556734765540285)
                    ·
                      refine ⟨3770773941208775537077607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10055397176556734765540285 3770773941208775537077607)
                      ·
                        rfl

theorem cell23_7343556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_7343556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343556 prefixEnd_7343556 := by exact prefixLift 7343556
  have htrace : WordTrace (prefixWord ++ tailWord_7343556) baseStart_7343556 baseEnd_7343556 := by
    simpa [prefixWord, tailWord_7343556, baseEnd_7343556] using wordTrace_append hprefix tailTrace_7343556
  have hstable : (prefixWord ++ tailWord_7343556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343556).length < 2 ^ (prefixWord ++ tailWord_7343556).sum := by decide
  have hdescent : baseEnd_7343556 < baseStart_7343556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343562 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_7343562 : Nat := 118140960795 + 7343562 * 2 ^ 59
def prefixEnd_7343562 : Nat := 4983230072969 + 3 ^ 40 * 7343562 * 2
def baseEnd_7343562 : Nat := 3770777022092702513602579

theorem tailTrace_7343562 : CollatzResearch.WordTrace tailWord_7343562 prefixEnd_7343562 3770777022092702513602579 := by
  unfold tailWord_7343562
  simp only [CollatzResearch.WordTrace]
  refine ⟨66960427555384132346074235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178561140147691019589531293 66960427555384132346074235)
  ·
    refine ⟨100440641333076198519111353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66960427555384132346074235 100440641333076198519111353)
    ·
      refine ⟨75330480999807148889333515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100440641333076198519111353 75330480999807148889333515)
      ·
        refine ⟨112995721499710723334000273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75330480999807148889333515 112995721499710723334000273)
        ·
          refine ⟨84746791124783042500500205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112995721499710723334000273 84746791124783042500500205)
          ·
            refine ⟨31780046671793640937687577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84746791124783042500500205 31780046671793640937687577)
            ·
              refine ⟨23835035003845230703265683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31780046671793640937687577 23835035003845230703265683)
              ·
                refine ⟨35752552505767846054898525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23835035003845230703265683 35752552505767846054898525)
                ·
                  refine ⟨13407207189662942270586947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35752552505767846054898525 13407207189662942270586947)
                  ·
                    refine ⟨20110810784494413405880421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13407207189662942270586947 20110810784494413405880421)
                    ·
                      refine ⟨3770777022092702513602579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20110810784494413405880421 3770777022092702513602579)
                      ·
                        rfl

theorem cell23_7343562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_7343562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343562 prefixEnd_7343562 := by exact prefixLift 7343562
  have htrace : WordTrace (prefixWord ++ tailWord_7343562) baseStart_7343562 baseEnd_7343562 := by
    simpa [prefixWord, tailWord_7343562, baseEnd_7343562] using wordTrace_append hprefix tailTrace_7343562
  have hstable : (prefixWord ++ tailWord_7343562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343562).length < 2 ^ (prefixWord ++ tailWord_7343562).sum := by decide
  have hdescent : baseEnd_7343562 < baseStart_7343562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343585 : List Nat := [1, 2, 3, 1, 2, 4, 10]
def baseStart_7343585 : Nat := 118140960795 + 7343585 * 2 ^ 59
def prefixEnd_7343585 : Nat := 4983230072969 + 3 ^ 40 * 7343585 * 2
def baseEnd_7343585 : Nat := 46552948545034023748333

theorem tailTrace_7343585 : CollatzResearch.WordTrace tailWord_7343585 prefixEnd_7343585 46552948545034023748333 := by
  unfold tailWord_7343585
  simp only [CollatzResearch.WordTrace]
  refine ⟨267842549100453204312384209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178561699400302136208256139 267842549100453204312384209)
  ·
    refine ⟨200881911825339903234288157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267842549100453204312384209 200881911825339903234288157)
    ·
      refine ⟨75330716934502463712858059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200881911825339903234288157 75330716934502463712858059)
      ·
        refine ⟨112996075401753695569287089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75330716934502463712858059 112996075401753695569287089)
        ·
          refine ⟨84747056551315271676965317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112996075401753695569287089 84747056551315271676965317)
          ·
            refine ⟨15890073103371613439430997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84747056551315271676965317 15890073103371613439430997)
            ·
              refine ⟨46552948545034023748333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15890073103371613439430997 46552948545034023748333)
              ·
                rfl

theorem cell23_7343585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 10].length) (baseStart_7343585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343585 prefixEnd_7343585 := by exact prefixLift 7343585
  have htrace : WordTrace (prefixWord ++ tailWord_7343585) baseStart_7343585 baseEnd_7343585 := by
    simpa [prefixWord, tailWord_7343585, baseEnd_7343585] using wordTrace_append hprefix tailTrace_7343585
  have hstable : (prefixWord ++ tailWord_7343585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343585).length < 2 ^ (prefixWord ++ tailWord_7343585).sum := by decide
  have hdescent : baseEnd_7343585 < baseStart_7343585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343589 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 4, 4]
def baseStart_7343589 : Nat := 118140960795 + 7343589 * 2 ^ 59
def prefixEnd_7343589 : Nat := 4983230072969 + 3 ^ 40 * 7343589 * 2
def baseEnd_7343589 : Nat := 1256930295356791302654985

theorem tailTrace_7343589 : CollatzResearch.WordTrace tailWord_7343589 prefixEnd_7343589 1256930295356791302654985 := by
  unfold tailWord_7343589
  simp only [CollatzResearch.WordTrace]
  refine ⟨267842694992438712995529821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178561796661625808663686547 267842694992438712995529821)
  ·
    refine ⟨100441010622164517373323683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267842694992438712995529821 100441010622164517373323683)
    ·
      refine ⟨150661515933246776059985525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100441010622164517373323683 150661515933246776059985525)
      ·
        refine ⟨14124517118741885255623643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150661515933246776059985525 14124517118741885255623643)
        ·
          refine ⟨21186775678112827883435465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14124517118741885255623643 21186775678112827883435465)
          ·
            refine ⟨15890081758584620912576599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21186775678112827883435465 15890081758584620912576599)
            ·
              refine ⟨23835122637876931368864899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15890081758584620912576599 23835122637876931368864899)
              ·
                refine ⟨35752683956815397053297349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23835122637876931368864899 35752683956815397053297349)
                ·
                  refine ⟨6703628241902886947493253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35752683956815397053297349 6703628241902886947493253)
                  ·
                    refine ⟨1256930295356791302654985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6703628241902886947493253 1256930295356791302654985)
                    ·
                      rfl

theorem cell23_7343589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_7343589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343589 prefixEnd_7343589 := by exact prefixLift 7343589
  have htrace : WordTrace (prefixWord ++ tailWord_7343589) baseStart_7343589 baseEnd_7343589 := by
    simpa [prefixWord, tailWord_7343589, baseEnd_7343589] using wordTrace_append hprefix tailTrace_7343589
  have hstable : (prefixWord ++ tailWord_7343589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343589).length < 2 ^ (prefixWord ++ tailWord_7343589).sum := by decide
  have hdescent : baseEnd_7343589 < baseStart_7343589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343625 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_7343625 : Nat := 118140960795 + 7343625 * 2 ^ 59
def prefixEnd_7343625 : Nat := 4983230072969 + 3 ^ 40 * 7343625 * 2
def baseEnd_7343625 : Nat := 3770809371373935767114789

theorem tailTrace_7343625 : CollatzResearch.WordTrace tailWord_7343625 prefixEnd_7343625 3770809371373935767114789 := by
  unfold tailWord_7343625
  simp only [CollatzResearch.WordTrace]
  refine ⟨267844008020308291143840329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178562672013538860762560219 267844008020308291143840329)
  ·
    refine ⟨200883006015231218357880247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267844008020308291143840329 200883006015231218357880247)
    ·
      refine ⟨301324509022846827536820371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200883006015231218357880247 301324509022846827536820371)
      ·
        refine ⟨451986763534270241305230557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301324509022846827536820371 451986763534270241305230557)
        ·
          refine ⟨169495036325351340489461459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451986763534270241305230557 169495036325351340489461459)
          ·
            refine ⟨254242554488027010734192189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169495036325351340489461459 254242554488027010734192189)
            ·
              refine ⟨95340957933010129025322071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254242554488027010734192189 95340957933010129025322071)
              ·
                refine ⟨143011436899515193537983107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95340957933010129025322071 143011436899515193537983107)
                ·
                  refine ⟨214517155349272790306974661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143011436899515193537983107 214517155349272790306974661)
                  ·
                    refine ⟨40221966627988648182557749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214517155349272790306974661 40221966627988648182557749)
                    ·
                      refine ⟨3770809371373935767114789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40221966627988648182557749 3770809371373935767114789)
                      ·
                        rfl

theorem cell23_7343625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_7343625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343625 prefixEnd_7343625 := by exact prefixLift 7343625
  have htrace : WordTrace (prefixWord ++ tailWord_7343625) baseStart_7343625 baseEnd_7343625 := by
    simpa [prefixWord, tailWord_7343625, baseEnd_7343625] using wordTrace_append hprefix tailTrace_7343625
  have hstable : (prefixWord ++ tailWord_7343625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343625).length < 2 ^ (prefixWord ++ tailWord_7343625).sum := by decide
  have hdescent : baseEnd_7343625 < baseStart_7343625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343636 : List Nat := [2, 4, 3, 1, 3, 1, 9]
def baseStart_7343636 : Nat := 118140960795 + 7343636 * 2 ^ 59
def prefixEnd_7343636 : Nat := 4983230072969 + 3 ^ 40 * 7343636 * 2
def baseEnd_7343636 : Nat := 46553271847668336099719

theorem tailTrace_7343636 : CollatzResearch.WordTrace tailWord_7343636 prefixEnd_7343636 46553271847668336099719 := by
  unfold tailWord_7343636
  simp only [CollatzResearch.WordTrace]
  refine ⟨133922204611634220011245381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178562939482178960014993841 133922204611634220011245381)
  ·
    refine ⟨25110413364681416252108509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133922204611634220011245381 25110413364681416252108509)
    ·
      refine ⟨9416405011755531094540691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25110413364681416252108509 9416405011755531094540691)
      ·
        refine ⟨14124607517633296641811037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9416405011755531094540691 14124607517633296641811037)
        ·
          refine ⟨5296727819112486240679139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14124607517633296641811037 5296727819112486240679139)
          ·
            refine ⟨7945091728668729361018709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296727819112486240679139 7945091728668729361018709)
            ·
              refine ⟨46553271847668336099719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7945091728668729361018709 46553271847668336099719)
              ·
                rfl

theorem cell23_7343636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 9].length) (baseStart_7343636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343636 prefixEnd_7343636 := by exact prefixLift 7343636
  have htrace : WordTrace (prefixWord ++ tailWord_7343636) baseStart_7343636 baseEnd_7343636 := by
    simpa [prefixWord, tailWord_7343636, baseEnd_7343636] using wordTrace_append hprefix tailTrace_7343636
  have hstable : (prefixWord ++ tailWord_7343636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343636).length < 2 ^ (prefixWord ++ tailWord_7343636).sum := by decide
  have hdescent : baseEnd_7343636 < baseStart_7343636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343672 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_7343672 : Nat := 118140960795 + 7343672 * 2 ^ 59
def prefixEnd_7343672 : Nat := 4983230072969 + 3 ^ 40 * 7343672 * 2
def baseEnd_7343672 : Nat := 3770833504964697083227073

theorem tailTrace_7343672 : CollatzResearch.WordTrace tailWord_7343672 prefixEnd_7343672 3770833504964697083227073 := by
  unfold tailWord_7343672
  simp only [CollatzResearch.WordTrace]
  refine ⟨133922861125569009085400635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178563814834092012113867513 133922861125569009085400635)
  ·
    refine ⟨200884291688353513628100953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133922861125569009085400635 200884291688353513628100953)
    ·
      refine ⟨150663218766265135221075715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200884291688353513628100953 150663218766265135221075715)
      ·
        refine ⟨225994828149397702831613573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150663218766265135221075715 225994828149397702831613573)
        ·
          refine ⟨42374030278012069280927545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225994828149397702831613573 42374030278012069280927545)
          ·
            refine ⟨31780522708509051960695659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42374030278012069280927545 31780522708509051960695659)
            ·
              refine ⟨47670784062763577941043489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31780522708509051960695659 47670784062763577941043489)
              ·
                refine ⟨35753088047072683455782617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47670784062763577941043489 35753088047072683455782617)
                ·
                  refine ⟨26814816035304512591836963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35753088047072683455782617 26814816035304512591836963)
                  ·
                    refine ⟨40222224052956768887755445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26814816035304512591836963 40222224052956768887755445)
                    ·
                      refine ⟨3770833504964697083227073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40222224052956768887755445 3770833504964697083227073)
                      ·
                        rfl

theorem cell23_7343672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_7343672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343672 prefixEnd_7343672 := by exact prefixLift 7343672
  have htrace : WordTrace (prefixWord ++ tailWord_7343672) baseStart_7343672 baseEnd_7343672 := by
    simpa [prefixWord, tailWord_7343672, baseEnd_7343672] using wordTrace_append hprefix tailTrace_7343672
  have hstable : (prefixWord ++ tailWord_7343672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343672).length < 2 ^ (prefixWord ++ tailWord_7343672).sum := by decide
  have hdescent : baseEnd_7343672 < baseStart_7343672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343673 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 1, 3, 2]
def baseStart_7343673 : Nat := 118140960795 + 7343673 * 2 ^ 59
def prefixEnd_7343673 : Nat := 4983230072969 + 3 ^ 40 * 7343673 * 2
def baseEnd_7343673 : Nat := 3770834018445351579314569

theorem tailTrace_7343673 : CollatzResearch.WordTrace tailWord_7343673 prefixEnd_7343673 3770834018445351579314569 := by
  unfold tailWord_7343673
  simp only [CollatzResearch.WordTrace]
  refine ⟨267845758724134395341587673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178563839149422930227725115 267845758724134395341587673)
  ·
    refine ⟨200884319043100796506190755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267845758724134395341587673 200884319043100796506190755)
    ·
      refine ⟨301326478564651194759286133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200884319043100796506190755 301326478564651194759286133)
      ·
        refine ⟨28249357365436049508683075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301326478564651194759286133 28249357365436049508683075)
        ·
          refine ⟨42374036048154074263024613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28249357365436049508683075 42374036048154074263024613)
          ·
            refine ⟨7945131759028888924317115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42374036048154074263024613 7945131759028888924317115)
            ·
              refine ⟨11917697638543333386475673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7945131759028888924317115 11917697638543333386475673)
              ·
                refine ⟨8938273228907500039856755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11917697638543333386475673 8938273228907500039856755)
                ·
                  refine ⟨13407409843361250059785133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8938273228907500039856755 13407409843361250059785133)
                  ·
                    refine ⟨5027778691260468772419425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13407409843361250059785133 5027778691260468772419425)
                    ·
                      refine ⟨3770834018445351579314569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027778691260468772419425 3770834018445351579314569)
                      ·
                        rfl

theorem cell23_7343673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_7343673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343673 prefixEnd_7343673 := by exact prefixLift 7343673
  have htrace : WordTrace (prefixWord ++ tailWord_7343673) baseStart_7343673 baseEnd_7343673 := by
    simpa [prefixWord, tailWord_7343673, baseEnd_7343673] using wordTrace_append hprefix tailTrace_7343673
  have hstable : (prefixWord ++ tailWord_7343673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343673).length < 2 ^ (prefixWord ++ tailWord_7343673).sum := by decide
  have hdescent : baseEnd_7343673 < baseStart_7343673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343703 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 2, 2, 2]
def baseStart_7343703 : Nat := 118140960795 + 7343703 * 2 ^ 59
def prefixEnd_7343703 : Nat := 4983230072969 + 3 ^ 40 * 7343703 * 2
def baseEnd_7343703 : Nat := 3770849422864986461939431

theorem tailTrace_7343703 : CollatzResearch.WordTrace tailWord_7343703 prefixEnd_7343703 3770849422864986461939431 := by
  unfold tailWord_7343703
  simp only [CollatzResearch.WordTrace]
  refine ⟨267846852914025710465179763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178564568609350473643453175 267846852914025710465179763)
  ·
    refine ⟨401770279371038565697769645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267846852914025710465179763 401770279371038565697769645)
    ·
      refine ⟨150663854764139462136663617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401770279371038565697769645 150663854764139462136663617)
      ·
        refine ⟨112997891073104596602497713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150663854764139462136663617 112997891073104596602497713)
        ·
          refine ⟨84748418304828447451873285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112997891073104596602497713 84748418304828447451873285)
          ·
            refine ⟨15890328432155333897226241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84748418304828447451873285 15890328432155333897226241)
            ·
              refine ⟨11917746324116500422919681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15890328432155333897226241 11917746324116500422919681)
              ·
                refine ⟨8938309743087375317189761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11917746324116500422919681 8938309743087375317189761)
                ·
                  refine ⟨6703732307315531487892321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8938309743087375317189761 6703732307315531487892321)
                  ·
                    refine ⟨5027799230486648615919241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6703732307315531487892321 5027799230486648615919241)
                    ·
                      refine ⟨3770849422864986461939431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027799230486648615919241 3770849422864986461939431)
                      ·
                        rfl

theorem cell23_7343703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_7343703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343703 prefixEnd_7343703 := by exact prefixLift 7343703
  have htrace : WordTrace (prefixWord ++ tailWord_7343703) baseStart_7343703 baseEnd_7343703 := by
    simpa [prefixWord, tailWord_7343703, baseEnd_7343703] using wordTrace_append hprefix tailTrace_7343703
  have hstable : (prefixWord ++ tailWord_7343703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343703).length < 2 ^ (prefixWord ++ tailWord_7343703).sum := by decide
  have hdescent : baseEnd_7343703 < baseStart_7343703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343776 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 2, 4, 2]
def baseStart_7343776 : Nat := 118140960795 + 7343776 * 2 ^ 59
def prefixEnd_7343776 : Nat := 4983230072969 + 3 ^ 40 * 7343776 * 2
def baseEnd_7343776 : Nat := 3770886906952764676326595

theorem tailTrace_7343776 : CollatzResearch.WordTrace tailWord_7343776 prefixEnd_7343776 3770886906952764676326595 := by
  unfold tailWord_7343776
  simp only [CollatzResearch.WordTrace]
  refine ⟨133924757721380621966293591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178566343628507495955058121 133924757721380621966293591)
  ·
    refine ⟨200887136582070932949440387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133924757721380621966293591 200887136582070932949440387)
    ·
      refine ⟨301330704873106399424160581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200887136582070932949440387 301330704873106399424160581)
      ·
        refine ⟨56499507163707449892030109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301330704873106399424160581 56499507163707449892030109)
        ·
          refine ⟨21187315186390293709511291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56499507163707449892030109 21187315186390293709511291)
          ·
            refine ⟨31780972779585440564266937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21187315186390293709511291 31780972779585440564266937)
            ·
              refine ⟨23835729584689080423200203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31780972779585440564266937 23835729584689080423200203)
              ·
                refine ⟨35753594377033620634800305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23835729584689080423200203 35753594377033620634800305)
                ·
                  refine ⟨26815195782775215476100229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35753594377033620634800305 26815195782775215476100229)
                  ·
                    refine ⟨5027849209270352901768793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26815195782775215476100229 5027849209270352901768793)
                    ·
                      refine ⟨3770886906952764676326595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027849209270352901768793 3770886906952764676326595)
                      ·
                        rfl

theorem cell23_7343776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_7343776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343776 prefixEnd_7343776 := by exact prefixLift 7343776
  have htrace : WordTrace (prefixWord ++ tailWord_7343776) baseStart_7343776 baseEnd_7343776 := by
    simpa [prefixWord, tailWord_7343776, baseEnd_7343776] using wordTrace_append hprefix tailTrace_7343776
  have hstable : (prefixWord ++ tailWord_7343776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343776).length < 2 ^ (prefixWord ++ tailWord_7343776).sum := by decide
  have hdescent : baseEnd_7343776 < baseStart_7343776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343789 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_7343789 : Nat := 118140960795 + 7343789 * 2 ^ 59
def prefixEnd_7343789 : Nat := 4983230072969 + 3 ^ 40 * 7343789 * 2
def baseEnd_7343789 : Nat := 3770893582201273125464035

theorem tailTrace_7343789 : CollatzResearch.WordTrace tailWord_7343789 prefixEnd_7343789 3770893582201273125464035 := by
  unfold tailWord_7343789
  simp only [CollatzResearch.WordTrace]
  refine ⟨267849989591714147152810421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178566659727809431435206947 267849989591714147152810421)
  ·
    refine ⟨25110936524223201295575977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267849989591714147152810421 25110936524223201295575977)
    ·
      refine ⟨18833202393167400971681983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25110936524223201295575977 18833202393167400971681983)
      ·
        refine ⟨28249803589751101457522975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18833202393167400971681983 28249803589751101457522975)
        ·
          refine ⟨42374705384626652186284463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28249803589751101457522975 42374705384626652186284463)
          ·
            refine ⟨63562058076939978279426695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42374705384626652186284463 63562058076939978279426695)
            ·
              refine ⟨95343087115409967419140043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63562058076939978279426695 95343087115409967419140043)
              ·
                refine ⟨143014630673114951128710065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95343087115409967419140043 143014630673114951128710065)
                ·
                  refine ⟨107260973004836213346532549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143014630673114951128710065 107260973004836213346532549)
                  ·
                    refine ⟨20111432438406790002474853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107260973004836213346532549 20111432438406790002474853)
                    ·
                      refine ⟨3770893582201273125464035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20111432438406790002474853 3770893582201273125464035)
                      ·
                        rfl

theorem cell23_7343789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_7343789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343789 prefixEnd_7343789 := by exact prefixLift 7343789
  have htrace : WordTrace (prefixWord ++ tailWord_7343789) baseStart_7343789 baseEnd_7343789 := by
    simpa [prefixWord, tailWord_7343789, baseEnd_7343789] using wordTrace_append hprefix tailTrace_7343789
  have hstable : (prefixWord ++ tailWord_7343789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343789).length < 2 ^ (prefixWord ++ tailWord_7343789).sum := by decide
  have hdescent : baseEnd_7343789 < baseStart_7343789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343820 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 3, 4]
def baseStart_7343820 : Nat := 118140960795 + 7343820 * 2 ^ 59
def prefixEnd_7343820 : Nat := 4983230072969 + 3 ^ 40 * 7343820 * 2
def baseEnd_7343820 : Nat := 1256969833367187501392131

theorem tailTrace_7343820 : CollatzResearch.WordTrace tailWord_7343820 prefixEnd_7343820 1256969833367187501392131 := by
  unfold tailWord_7343820
  simp only [CollatzResearch.WordTrace]
  refine ⟨133925560127300919723594457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178567413503067892964792609 133925560127300919723594457)
  ·
    refine ⟨100444170095475689792695843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133925560127300919723594457 100444170095475689792695843)
    ·
      refine ⟨150666255143213534689043765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100444170095475689792695843 150666255143213534689043765)
      ·
        refine ⟨14124961419676268877097853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150666255143213534689043765 14124961419676268877097853)
        ·
          refine ⟨5296860532378600828911695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14124961419676268877097853 5296860532378600828911695)
          ·
            refine ⟨7945290798567901243367543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296860532378600828911695 7945290798567901243367543)
            ·
              refine ⟨11917936197851851865051315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7945290798567901243367543 11917936197851851865051315)
              ·
                refine ⟨17876904296777777797576973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11917936197851851865051315 17876904296777777797576973)
                ·
                  refine ⟨6703839111291666674091365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17876904296777777797576973 6703839111291666674091365)
                  ·
                    refine ⟨1256969833367187501392131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6703839111291666674091365 1256969833367187501392131)
                    ·
                      rfl

theorem cell23_7343820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_7343820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343820 prefixEnd_7343820 := by exact prefixLift 7343820
  have htrace : WordTrace (prefixWord ++ tailWord_7343820) baseStart_7343820 baseEnd_7343820 := by
    simpa [prefixWord, tailWord_7343820, baseEnd_7343820] using wordTrace_append hprefix tailTrace_7343820
  have hstable : (prefixWord ++ tailWord_7343820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343820).length < 2 ^ (prefixWord ++ tailWord_7343820).sum := by decide
  have hdescent : baseEnd_7343820 < baseStart_7343820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343853 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_7343853 : Nat := 118140960795 + 7343853 * 2 ^ 59
def prefixEnd_7343853 : Nat := 4983230072969 + 3 ^ 40 * 7343853 * 2
def baseEnd_7343853 : Nat := 3770926444963160875063741

theorem tailTrace_7343853 : CollatzResearch.WordTrace tailWord_7343853 prefixEnd_7343853 3770926444963160875063741 := by
  unfold tailWord_7343853
  simp only [CollatzResearch.WordTrace]
  refine ⟨267852323863482286083140213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178568215908988190722093475 267852323863482286083140213)
  ·
    refine ⟨25111155362201464320294395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267852323863482286083140213 25111155362201464320294395)
    ·
      refine ⟨37666733043302196480441593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25111155362201464320294395 37666733043302196480441593)
      ·
        refine ⟨28250049782476647360331195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37666733043302196480441593 28250049782476647360331195)
        ·
          refine ⟨42375074673714971040496793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28250049782476647360331195 42375074673714971040496793)
          ·
            refine ⟨31781306005286228280372595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42375074673714971040496793 31781306005286228280372595)
            ·
              refine ⟨47671959007929342420558893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31781306005286228280372595 47671959007929342420558893)
              ·
                refine ⟨17876984627973503407709585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47671959007929342420558893 17876984627973503407709585)
                ·
                  refine ⟨13407738470980127555782189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17876984627973503407709585 13407738470980127555782189)
                  ·
                    refine ⟨5027901926617547833418321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13407738470980127555782189 5027901926617547833418321)
                    ·
                      refine ⟨3770926444963160875063741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5027901926617547833418321 3770926444963160875063741)
                      ·
                        rfl

theorem cell23_7343853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_7343853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343853 prefixEnd_7343853 := by exact prefixLift 7343853
  have htrace : WordTrace (prefixWord ++ tailWord_7343853) baseStart_7343853 baseEnd_7343853 := by
    simpa [prefixWord, tailWord_7343853, baseEnd_7343853] using wordTrace_append hprefix tailTrace_7343853
  have hstable : (prefixWord ++ tailWord_7343853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343853).length < 2 ^ (prefixWord ++ tailWord_7343853).sum := by decide
  have hdescent : baseEnd_7343853 < baseStart_7343853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343859 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 6, 4]
def baseStart_7343859 : Nat := 118140960795 + 7343859 * 2 ^ 59
def prefixEnd_7343859 : Nat := 4983230072969 + 3 ^ 40 * 7343859 * 2
def baseEnd_7343859 : Nat := 1256976508615695950529571

theorem tailTrace_7343859 : CollatzResearch.WordTrace tailWord_7343859 prefixEnd_7343859 1256976508615695950529571 := by
  unfold tailWord_7343859
  simp only [CollatzResearch.WordTrace]
  refine ⟨267852542701460549107858631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178568361800973699405239087 267852542701460549107858631)
  ·
    refine ⟨401778814052190823661787947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267852542701460549107858631 401778814052190823661787947)
    ·
      refine ⟨602668221078286235492681921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401778814052190823661787947 602668221078286235492681921)
      ·
        refine ⟨452001165808714676619511441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602668221078286235492681921 452001165808714676619511441)
        ·
          refine ⟨339000874356536007464633581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452001165808714676619511441 339000874356536007464633581)
          ·
            refine ⟨127125327883701002799237593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339000874356536007464633581 127125327883701002799237593)
            ·
              refine ⟨95343995912775752099428195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127125327883701002799237593 95343995912775752099428195)
              ·
                refine ⟨143015993869163628149142293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95343995912775752099428195 143015993869163628149142293)
                ·
                  refine ⟨6703874712617045069491045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143015993869163628149142293 6703874712617045069491045)
                  ·
                    refine ⟨1256976508615695950529571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6703874712617045069491045 1256976508615695950529571)
                    ·
                      rfl

theorem cell23_7343859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 4].length) (baseStart_7343859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343859 prefixEnd_7343859 := by exact prefixLift 7343859
  have htrace : WordTrace (prefixWord ++ tailWord_7343859) baseStart_7343859 baseEnd_7343859 := by
    simpa [prefixWord, tailWord_7343859, baseEnd_7343859] using wordTrace_append hprefix tailTrace_7343859
  have hstable : (prefixWord ++ tailWord_7343859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343859).length < 2 ^ (prefixWord ++ tailWord_7343859).sum := by decide
  have hdescent : baseEnd_7343859 < baseStart_7343859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343869 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_7343869 : Nat := 118140960795 + 7343869 * 2 ^ 59
def prefixEnd_7343869 : Nat := 4983230072969 + 3 ^ 40 * 7343869 * 2
def baseEnd_7343869 : Nat := 3770934660653632812463667

theorem tailTrace_7343869 : CollatzResearch.WordTrace tailWord_7343869 prefixEnd_7343869 3770934660653632812463667 := by
  unfold tailWord_7343869
  simp only [CollatzResearch.WordTrace]
  refine ⟨267852907431424320815722661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178568604954282880543815107 267852907431424320815722661)
  ·
    refine ⟨50222420143392060152947999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267852907431424320815722661 50222420143392060152947999)
    ·
      refine ⟨75333630215088090229421999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50222420143392060152947999 75333630215088090229421999)
      ·
        refine ⟨113000445322632135344132999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75333630215088090229421999 113000445322632135344132999)
        ·
          refine ⟨169500667983948203016199499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113000445322632135344132999 169500667983948203016199499)
          ·
            refine ⟨254251001975922304524299249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169500667983948203016199499 254251001975922304524299249)
            ·
              refine ⟨190688251481941728393224437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254251001975922304524299249 190688251481941728393224437)
              ·
                refine ⟨17877023576432037036864791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190688251481941728393224437 17877023576432037036864791)
                ·
                  refine ⟨26815535364648055555297187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17877023576432037036864791 26815535364648055555297187)
                  ·
                    refine ⟨40223303046972083332945781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26815535364648055555297187 40223303046972083332945781)
                    ·
                      refine ⟨3770934660653632812463667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40223303046972083332945781 3770934660653632812463667)
                      ·
                        rfl

theorem cell23_7343869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_7343869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343869 prefixEnd_7343869 := by exact prefixLift 7343869
  have htrace : WordTrace (prefixWord ++ tailWord_7343869) baseStart_7343869 baseEnd_7343869 := by
    simpa [prefixWord, tailWord_7343869, baseEnd_7343869] using wordTrace_append hprefix tailTrace_7343869
  have hstable : (prefixWord ++ tailWord_7343869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343869).length < 2 ^ (prefixWord ++ tailWord_7343869).sum := by decide
  have hdescent : baseEnd_7343869 < baseStart_7343869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343886 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_7343886 : Nat := 118140960795 + 7343886 * 2 ^ 59
def prefixEnd_7343886 : Nat := 4983230072969 + 3 ^ 40 * 7343886 * 2
def baseEnd_7343886 : Nat := 3770943389824759245951089

theorem tailTrace_7343886 : CollatzResearch.WordTrace tailWord_7343886 prefixEnd_7343886 3770943389824759245951089 := by
  unfold tailWord_7343886
  simp only [CollatzResearch.WordTrace]
  refine ⟨33481690934045341589886439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178569018314908488479394341 33481690934045341589886439)
  ·
    refine ⟨50222536401068012384829659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33481690934045341589886439 50222536401068012384829659)
    ·
      refine ⟨75333804601602018577244489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50222536401068012384829659 75333804601602018577244489)
      ·
        refine ⟨56500353451201513932933367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75333804601602018577244489 56500353451201513932933367)
        ·
          refine ⟨84750530176802270899400051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56500353451201513932933367 84750530176802270899400051)
          ·
            refine ⟨127125795265203406349100077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84750530176802270899400051 127125795265203406349100077)
            ·
              refine ⟨47672173224451277380912529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127125795265203406349100077 47672173224451277380912529)
              ·
                refine ⟨35754129918338458035684397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47672173224451277380912529 35754129918338458035684397)
                ·
                  refine ⟨13407798719376921763381649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35754129918338458035684397 13407798719376921763381649)
                  ·
                    refine ⟨10055849039532691322536237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13407798719376921763381649 10055849039532691322536237)
                    ·
                      refine ⟨3770943389824759245951089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10055849039532691322536237 3770943389824759245951089)
                      ·
                        rfl

theorem cell23_7343886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_7343886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343886 prefixEnd_7343886 := by exact prefixLift 7343886
  have htrace : WordTrace (prefixWord ++ tailWord_7343886) baseStart_7343886 baseEnd_7343886 := by
    simpa [prefixWord, tailWord_7343886, baseEnd_7343886] using wordTrace_append hprefix tailTrace_7343886
  have hstable : (prefixWord ++ tailWord_7343886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343886).length < 2 ^ (prefixWord ++ tailWord_7343886).sum := by decide
  have hdescent : baseEnd_7343886 < baseStart_7343886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343899 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 3]
def baseStart_7343899 : Nat := 118140960795 + 7343899 * 2 ^ 59
def prefixEnd_7343899 : Nat := 4983230072969 + 3 ^ 40 * 7343899 * 2
def baseEnd_7343899 : Nat := 3770950065073267695088529

theorem tailTrace_7343899 : CollatzResearch.WordTrace tailWord_7343899 prefixEnd_7343899 3770950065073267695088529 := by
  unfold tailWord_7343899
  simp only [CollatzResearch.WordTrace]
  refine ⟨267854001621315635939314751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178569334414210423959543167 267854001621315635939314751)
  ·
    refine ⟨401781002431973453908972127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267854001621315635939314751 401781002431973453908972127)
    ·
      refine ⟨602671503647960180863458191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401781002431973453908972127 602671503647960180863458191)
      ·
        refine ⟨904007255471940271295187287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602671503647960180863458191 904007255471940271295187287)
        ·
          refine ⟨1356010883207910406942780931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904007255471940271295187287 1356010883207910406942780931)
          ·
            refine ⟨2034016324811865610414171397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356010883207910406942780931 2034016324811865610414171397)
            ·
              refine ⟨381378060902224801952657137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2034016324811865610414171397 381378060902224801952657137)
              ·
                refine ⟨286033545676668601464492853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381378060902224801952657137 286033545676668601464492853)
                ·
                  refine ⟨26815644907187681387296205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286033545676668601464492853 26815644907187681387296205)
                  ·
                    refine ⟨10055866840195380520236077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26815644907187681387296205 10055866840195380520236077)
                    ·
                      refine ⟨3770950065073267695088529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10055866840195380520236077 3770950065073267695088529)
                      ·
                        rfl

theorem cell23_7343899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 3].length) (baseStart_7343899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343899 prefixEnd_7343899 := by exact prefixLift 7343899
  have htrace : WordTrace (prefixWord ++ tailWord_7343899) baseStart_7343899 baseEnd_7343899 := by
    simpa [prefixWord, tailWord_7343899, baseEnd_7343899] using wordTrace_append hprefix tailTrace_7343899
  have hstable : (prefixWord ++ tailWord_7343899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343899).length < 2 ^ (prefixWord ++ tailWord_7343899).sum := by decide
  have hdescent : baseEnd_7343899 < baseStart_7343899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343906 : List Nat := [3, 3, 1, 1, 2, 1, 5, 7]
def baseStart_7343906 : Nat := 118140960795 + 7343906 * 2 ^ 59
def prefixEnd_7343906 : Nat := 4983230072969 + 3 ^ 40 * 7343906 * 2
def baseEnd_7343906 : Nat := 139664950349549969174111

theorem tailTrace_7343906 : CollatzResearch.WordTrace tailWord_7343906 prefixEnd_7343906 139664950349549969174111 := by
  unfold tailWord_7343906
  simp only [CollatzResearch.WordTrace]
  refine ⟨66963564233072569033704893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178569504621526850756546381 66963564233072569033704893)
  ·
    refine ⟨25111336587402213387639335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66963564233072569033704893 25111336587402213387639335)
    ·
      refine ⟨37667004881103320081459003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25111336587402213387639335 37667004881103320081459003)
      ·
        refine ⟨56500507321654980122188505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37667004881103320081459003 56500507321654980122188505)
        ·
          refine ⟨42375380491241235091641379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56500507321654980122188505 42375380491241235091641379)
          ·
            refine ⟨63563070736861852637462069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42375380491241235091641379 63563070736861852637462069)
            ·
              refine ⟨5959037881580798684762069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63563070736861852637462069 5959037881580798684762069)
              ·
                refine ⟨139664950349549969174111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5959037881580798684762069 139664950349549969174111)
                ·
                  rfl

theorem cell23_7343906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 7].length) (baseStart_7343906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343906 prefixEnd_7343906 := by exact prefixLift 7343906
  have htrace : WordTrace (prefixWord ++ tailWord_7343906) baseStart_7343906 baseEnd_7343906 := by
    simpa [prefixWord, tailWord_7343906, baseEnd_7343906] using wordTrace_append hprefix tailTrace_7343906
  have hstable : (prefixWord ++ tailWord_7343906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343906).length < 2 ^ (prefixWord ++ tailWord_7343906).sum := by decide
  have hdescent : baseEnd_7343906 < baseStart_7343906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343916 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 3]
def baseStart_7343916 : Nat := 118140960795 + 7343916 * 2 ^ 59
def prefixEnd_7343916 : Nat := 4983230072969 + 3 ^ 40 * 7343916 * 2
def baseEnd_7343916 : Nat := 3770958794244394128575951

theorem tailTrace_7343916 : CollatzResearch.WordTrace tailWord_7343916 prefixEnd_7343916 3770958794244394128575951 := by
  unfold tailWord_7343916
  simp only [CollatzResearch.WordTrace]
  refine ⟨133927310831127023921341801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178569747774836031895122401 133927310831127023921341801)
  ·
    refine ⟨100445483123345267941006351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133927310831127023921341801 100445483123345267941006351)
    ·
      refine ⟨150668224685017901911509527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100445483123345267941006351 150668224685017901911509527)
      ·
        refine ⟨226002337027526852867264291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150668224685017901911509527 226002337027526852867264291)
        ·
          refine ⟨339003505541290279300896437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226002337027526852867264291 339003505541290279300896437)
          ·
            refine ⟨31781578644495963684459041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 339003505541290279300896437 31781578644495963684459041)
            ·
              refine ⟨23836183983371972763344281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31781578644495963684459041 23836183983371972763344281)
              ·
                refine ⟨17877137987528979572508211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23836183983371972763344281 17877137987528979572508211)
                ·
                  refine ⟨26815706981293469358762317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17877137987528979572508211 26815706981293469358762317)
                  ·
                    refine ⟨10055890117985051009535869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26815706981293469358762317 10055890117985051009535869)
                    ·
                      refine ⟨3770958794244394128575951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10055890117985051009535869 3770958794244394128575951)
                      ·
                        rfl

theorem cell23_7343916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_7343916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343916 prefixEnd_7343916 := by exact prefixLift 7343916
  have htrace : WordTrace (prefixWord ++ tailWord_7343916) baseStart_7343916 baseEnd_7343916 := by
    simpa [prefixWord, tailWord_7343916, baseEnd_7343916] using wordTrace_append hprefix tailTrace_7343916
  have hstable : (prefixWord ++ tailWord_7343916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343916).length < 2 ^ (prefixWord ++ tailWord_7343916).sum := by decide
  have hdescent : baseEnd_7343916 < baseStart_7343916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7343976 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_7343976 : Nat := 118140960795 + 7343976 * 2 ^ 59
def prefixEnd_7343976 : Nat := 4983230072969 + 3 ^ 40 * 7343976 * 2
def baseEnd_7343976 : Nat := 3770989603083663893825675

theorem tailTrace_7343976 : CollatzResearch.WordTrace tailWord_7343976 prefixEnd_7343976 3770989603083663893825675 := by
  unfold tailWord_7343976
  simp only [CollatzResearch.WordTrace]
  refine ⟨133928405021018339044933891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178571206694691118726578521 133928405021018339044933891)
  ·
    refine ⟨200892607531527508567400837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133928405021018339044933891 200892607531527508567400837)
    ·
      refine ⟨37667363912161407856387657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200892607531527508567400837 37667363912161407856387657)
      ·
        refine ⟨28250522934121055892290743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37667363912161407856387657 28250522934121055892290743)
        ·
          refine ⟨42375784401181583838436115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28250522934121055892290743 42375784401181583838436115)
          ·
            refine ⟨63563676601772375757654173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42375784401181583838436115 63563676601772375757654173)
            ·
              refine ⟨23836378725664640909120315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63563676601772375757654173 23836378725664640909120315)
              ·
                refine ⟨35754568088496961363680473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23836378725664640909120315 35754568088496961363680473)
                ·
                  refine ⟨26815926066372721022760355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35754568088496961363680473 26815926066372721022760355)
                  ·
                    refine ⟨40223889099559081534140533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26815926066372721022760355 40223889099559081534140533)
                    ·
                      refine ⟨3770989603083663893825675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40223889099559081534140533 3770989603083663893825675)
                      ·
                        rfl

theorem cell23_7343976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_7343976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7343976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7343976 prefixEnd_7343976 := by exact prefixLift 7343976
  have htrace : WordTrace (prefixWord ++ tailWord_7343976) baseStart_7343976 baseEnd_7343976 := by
    simpa [prefixWord, tailWord_7343976, baseEnd_7343976] using wordTrace_append hprefix tailTrace_7343976
  have hstable : (prefixWord ++ tailWord_7343976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7343976).length < 2 ^ (prefixWord ++ tailWord_7343976).sum := by decide
  have hdescent : baseEnd_7343976 < baseStart_7343976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7343976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344001 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_7344001 : Nat := 118140960795 + 7344001 * 2 ^ 59
def prefixEnd_7344001 : Nat := 4983230072969 + 3 ^ 40 * 7344001 * 2
def baseEnd_7344001 : Nat := 3771002440100026296013061

theorem tailTrace_7344001 : CollatzResearch.WordTrace tailWord_7344001 prefixEnd_7344001 3771002440100026296013061 := by
  unfold tailWord_7344001
  simp only [CollatzResearch.WordTrace]
  refine ⟨267857721866946107359527857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178571814577964071573018571 267857721866946107359527857)
  ·
    refine ⟨200893291400209580519645893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267857721866946107359527857 200893291400209580519645893)
    ·
      refine ⟨37667492137539296347433605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200893291400209580519645893 37667492137539296347433605)
      ·
        refine ⟨7062654775788618065143801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37667492137539296347433605 7062654775788618065143801)
        ·
          refine ⟨5296991081841463548857851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7062654775788618065143801 5296991081841463548857851)
          ·
            refine ⟨7945486622762195323286777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296991081841463548857851 7945486622762195323286777)
            ·
              refine ⟨5959114967071646492465083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7945486622762195323286777 5959114967071646492465083)
              ·
                refine ⟨8938672450607469738697625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959114967071646492465083 8938672450607469738697625)
                ·
                  refine ⟨6704004337955602304023219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8938672450607469738697625 6704004337955602304023219)
                  ·
                    refine ⟨10056006506933403456034829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6704004337955602304023219 10056006506933403456034829)
                    ·
                      refine ⟨3771002440100026296013061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10056006506933403456034829 3771002440100026296013061)
                      ·
                        rfl

theorem cell23_7344001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_7344001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344001 prefixEnd_7344001 := by exact prefixLift 7344001
  have htrace : WordTrace (prefixWord ++ tailWord_7344001) baseStart_7344001 baseEnd_7344001 := by
    simpa [prefixWord, tailWord_7344001, baseEnd_7344001] using wordTrace_append hprefix tailTrace_7344001
  have hstable : (prefixWord ++ tailWord_7344001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344001).length < 2 ^ (prefixWord ++ tailWord_7344001).sum := by decide
  have hdescent : baseEnd_7344001 < baseStart_7344001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344007 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 2, 2, 2]
def baseStart_7344007 : Nat := 118140960795 + 7344007 * 2 ^ 59
def prefixEnd_7344007 : Nat := 4983230072969 + 3 ^ 40 * 7344007 * 2
def baseEnd_7344007 : Nat := 3771005520983953272538033

theorem tailTrace_7344007 : CollatzResearch.WordTrace tailWord_7344007 prefixEnd_7344007 3771005520983953272538033 := by
  unfold tailWord_7344007
  simp only [CollatzResearch.WordTrace]
  refine ⟨267857940704924370384246275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178571960469949580256164183 267857940704924370384246275)
  ·
    refine ⟨401786911057386555576369413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267857940704924370384246275 401786911057386555576369413)
    ·
      refine ⟨75335045823259979170569265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401786911057386555576369413 75335045823259979170569265)
      ·
        refine ⟨56501284367444984377926949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75335045823259979170569265 56501284367444984377926949)
        ·
          refine ⟨10593990818895934570861303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56501284367444984377926949 10593990818895934570861303)
          ·
            refine ⟨15890986228343901856291955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10593990818895934570861303 15890986228343901856291955)
            ·
              refine ⟨23836479342515852784437933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15890986228343901856291955 23836479342515852784437933)
              ·
                refine ⟨8938679753443444794164225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23836479342515852784437933 8938679753443444794164225)
                ·
                  refine ⟨6704009815082583595623169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8938679753443444794164225 6704009815082583595623169)
                  ·
                    refine ⟨5028007361311937696717377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6704009815082583595623169 5028007361311937696717377)
                    ·
                      refine ⟨3771005520983953272538033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028007361311937696717377 3771005520983953272538033)
                      ·
                        rfl

theorem cell23_7344007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_7344007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344007 prefixEnd_7344007 := by exact prefixLift 7344007
  have htrace : WordTrace (prefixWord ++ tailWord_7344007) baseStart_7344007 baseEnd_7344007 := by
    simpa [prefixWord, tailWord_7344007, baseEnd_7344007] using wordTrace_append hprefix tailTrace_7344007
  have hstable : (prefixWord ++ tailWord_7344007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344007).length < 2 ^ (prefixWord ++ tailWord_7344007).sum := by decide
  have hdescent : baseEnd_7344007 < baseStart_7344007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344036 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_7344036 : Nat := 118140960795 + 7344036 * 2 ^ 59
def prefixEnd_7344036 : Nat := 4983230072969 + 3 ^ 40 * 7344036 * 2
def baseEnd_7344036 : Nat := 3771020411922933659075399

theorem tailTrace_7344036 : CollatzResearch.WordTrace tailWord_7344036 prefixEnd_7344036 3771020411922933659075399 := by
  unfold tailWord_7344036
  simp only [CollatzResearch.WordTrace]
  refine ⟨133929499210909654168525981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178572665614546205558034641 133929499210909654168525981)
  ·
    refine ⟨50223562204091120313197243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133929499210909654168525981 50223562204091120313197243)
    ·
      refine ⟨75335343306136680469795865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50223562204091120313197243 75335343306136680469795865)
      ·
        refine ⟨56501507479602510352346899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75335343306136680469795865 56501507479602510352346899)
        ·
          refine ⟨84752261219403765528520349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56501507479602510352346899 84752261219403765528520349)
          ·
            refine ⟨31782097957276412073195131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84752261219403765528520349 31782097957276412073195131)
            ·
              refine ⟨47673146935914618109792697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31782097957276412073195131 47673146935914618109792697)
              ·
                refine ⟨35754860201935963582344523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47673146935914618109792697 35754860201935963582344523)
                ·
                  refine ⟨53632290302903945373516785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35754860201935963582344523 53632290302903945373516785)
                  ·
                    refine ⟨40224217727177959030137589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53632290302903945373516785 40224217727177959030137589)
                    ·
                      refine ⟨3771020411922933659075399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40224217727177959030137589 3771020411922933659075399)
                      ·
                        rfl

theorem cell23_7344036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_7344036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344036 prefixEnd_7344036 := by exact prefixLift 7344036
  have htrace : WordTrace (prefixWord ++ tailWord_7344036) baseStart_7344036 baseEnd_7344036 := by
    simpa [prefixWord, tailWord_7344036, baseEnd_7344036] using wordTrace_append hprefix tailTrace_7344036
  have hstable : (prefixWord ++ tailWord_7344036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344036).length < 2 ^ (prefixWord ++ tailWord_7344036).sum := by decide
  have hdescent : baseEnd_7344036 < baseStart_7344036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344063 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 2, 4, 2]
def baseStart_7344063 : Nat := 118140960795 + 7344063 * 2 ^ 59
def prefixEnd_7344063 : Nat := 4983230072969 + 3 ^ 40 * 7344063 * 2
def baseEnd_7344063 : Nat := 3771034275900605053437775

theorem tailTrace_7344063 : CollatzResearch.WordTrace tailWord_7344063 prefixEnd_7344063 3771034275900605053437775 := by
  unfold tailWord_7344063
  simp only [CollatzResearch.WordTrace]
  refine ⟨267859983192721491948284843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178573322128480994632189895 267859983192721491948284843)
  ·
    refine ⟨401789974789082237922427265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267859983192721491948284843 401789974789082237922427265)
    ·
      refine ⟨301342481091811678441820449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401789974789082237922427265 301342481091811678441820449)
      ·
        refine ⟨226006860818858758831365337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301342481091811678441820449 226006860818858758831365337)
        ·
          refine ⟨169505145614144069123524003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226006860818858758831365337 169505145614144069123524003)
          ·
            refine ⟨254257718421216103685286005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169505145614144069123524003 254257718421216103685286005)
            ·
              refine ⟨23836661101989009720495563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254257718421216103685286005 23836661101989009720495563)
              ·
                refine ⟨35754991652983514580743345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23836661101989009720495563 35754991652983514580743345)
                ·
                  refine ⟨26816243739737635935557509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35754991652983514580743345 26816243739737635935557509)
                  ·
                    refine ⟨5028045701200806737917033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26816243739737635935557509 5028045701200806737917033)
                    ·
                      refine ⟨3771034275900605053437775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028045701200806737917033 3771034275900605053437775)
                      ·
                        rfl

theorem cell23_7344063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 4, 2].length) (baseStart_7344063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344063 prefixEnd_7344063 := by exact prefixLift 7344063
  have htrace : WordTrace (prefixWord ++ tailWord_7344063) baseStart_7344063 baseEnd_7344063 := by
    simpa [prefixWord, tailWord_7344063, baseEnd_7344063] using wordTrace_append hprefix tailTrace_7344063
  have hstable : (prefixWord ++ tailWord_7344063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344063).length < 2 ^ (prefixWord ++ tailWord_7344063).sum := by decide
  have hdescent : baseEnd_7344063 < baseStart_7344063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344096 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 3]
def baseStart_7344096 : Nat := 118140960795 + 7344096 * 2 ^ 59
def prefixEnd_7344096 : Nat := 4983230072969 + 3 ^ 40 * 7344096 * 2
def baseEnd_7344096 : Nat := 3771051220762203424325123

theorem tailTrace_7344096 : CollatzResearch.WordTrace tailWord_7344096 prefixEnd_7344096 3771051220762203424325123 := by
  unfold tailWord_7344096
  simp only [CollatzResearch.WordTrace]
  refine ⟨133930593400800969292118071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178574124534401292389490761 133930593400800969292118071)
  ·
    refine ⟨200895890101201453938177107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133930593400800969292118071 200895890101201453938177107)
    ·
      refine ⟨301343835151802180907265661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200895890101201453938177107 301343835151802180907265661)
      ·
        refine ⟨113003938181925817840224623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301343835151802180907265661 113003938181925817840224623)
        ·
          refine ⟨169505907272888726760336935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113003938181925817840224623 169505907272888726760336935)
          ·
            refine ⟨254258860909333090140505403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169505907272888726760336935 254258860909333090140505403)
            ·
              refine ⟨381388291363999635210758105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254258860909333090140505403 381388291363999635210758105)
              ·
                refine ⟨286041218522999726408068579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381388291363999635210758105 286041218522999726408068579)
                ·
                  refine ⟨429061827784499589612102869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286041218522999726408068579 429061827784499589612102869)
                  ·
                    refine ⟨10056136588699209131533661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 429061827784499589612102869 10056136588699209131533661)
                    ·
                      refine ⟨3771051220762203424325123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10056136588699209131533661 3771051220762203424325123)
                      ·
                        rfl

theorem cell23_7344096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_7344096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344096 prefixEnd_7344096 := by exact prefixLift 7344096
  have htrace : WordTrace (prefixWord ++ tailWord_7344096) baseStart_7344096 baseEnd_7344096 := by
    simpa [prefixWord, tailWord_7344096, baseEnd_7344096] using wordTrace_append hprefix tailTrace_7344096
  have hstable : (prefixWord ++ tailWord_7344096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344096).length < 2 ^ (prefixWord ++ tailWord_7344096).sum := by decide
  have hdescent : baseEnd_7344096 < baseStart_7344096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344103 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 8]
def baseStart_7344103 : Nat := 118140960795 + 7344103 * 2 ^ 59
def prefixEnd_7344103 : Nat := 4983230072969 + 3 ^ 40 * 7344103 * 2
def baseEnd_7344103 : Nat := 419006090569642766326399

theorem tailTrace_7344103 : CollatzResearch.WordTrace tailWord_7344103 prefixEnd_7344103 419006090569642766326399 := by
  unfold tailWord_7344103
  simp only [CollatzResearch.WordTrace]
  refine ⟨267861442112576578779740963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178574294741717719186493975 267861442112576578779740963)
  ·
    refine ⟨401792163168864868169611445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267861442112576578779740963 401792163168864868169611445)
    ·
      refine ⟨37668015297081081390901073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 401792163168864868169611445 37668015297081081390901073)
      ·
        refine ⟨28251011472810811043175805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37668015297081081390901073 28251011472810811043175805)
        ·
          refine ⟨10594129302304054141190927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28251011472810811043175805 10594129302304054141190927)
          ·
            refine ⟨15891193953456081211786391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10594129302304054141190927 15891193953456081211786391)
            ·
              refine ⟨23836790930184121817679587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15891193953456081211786391 23836790930184121817679587)
              ·
                refine ⟨35755186395276182726519381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23836790930184121817679587 35755186395276182726519381)
                ·
                  refine ⟨419006090569642766326399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35755186395276182726519381 419006090569642766326399)
                  ·
                    rfl

theorem cell23_7344103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 8].length) (baseStart_7344103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344103 prefixEnd_7344103 := by exact prefixLift 7344103
  have htrace : WordTrace (prefixWord ++ tailWord_7344103) baseStart_7344103 baseEnd_7344103 := by
    simpa [prefixWord, tailWord_7344103, baseEnd_7344103] using wordTrace_append hprefix tailTrace_7344103
  have hstable : (prefixWord ++ tailWord_7344103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344103).length < 2 ^ (prefixWord ++ tailWord_7344103).sum := by decide
  have hdescent : baseEnd_7344103 < baseStart_7344103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344106 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_7344106 : Nat := 118140960795 + 7344106 * 2 ^ 59
def prefixEnd_7344106 : Nat := 4983230072969 + 3 ^ 40 * 7344106 * 2
def baseEnd_7344106 : Nat := 3771056355568748385200077

theorem tailTrace_7344106 : CollatzResearch.WordTrace tailWord_7344106 prefixEnd_7344106 3771056355568748385200077 := by
  unfold tailWord_7344106
  simp only [CollatzResearch.WordTrace]
  refine ⟨66965387882891427573025043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178574367687710473528066781 66965387882891427573025043)
  ·
    refine ⟨100448081824337141359537565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66965387882891427573025043 100448081824337141359537565)
    ·
      refine ⟨37668030684126428009826587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100448081824337141359537565 37668030684126428009826587)
      ·
        refine ⟨56502046026189642014739881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37668030684126428009826587 56502046026189642014739881)
        ·
          refine ⟨42376534519642231511054911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56502046026189642014739881 42376534519642231511054911)
          ·
            refine ⟨63564801779463347266582367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42376534519642231511054911 63564801779463347266582367)
            ·
              refine ⟨95347202669195020899873551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63564801779463347266582367 95347202669195020899873551)
              ·
                refine ⟨143020804003792531349810327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95347202669195020899873551 143020804003792531349810327)
                ·
                  refine ⟨214531206005688797024715491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143020804003792531349810327 214531206005688797024715491)
                  ·
                    refine ⟨321796809008533195537073237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 214531206005688797024715491 321796809008533195537073237)
                    ·
                      refine ⟨3771056355568748385200077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 321796809008533195537073237 3771056355568748385200077)
                      ·
                        rfl

theorem cell23_7344106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_7344106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344106 prefixEnd_7344106 := by exact prefixLift 7344106
  have htrace : WordTrace (prefixWord ++ tailWord_7344106) baseStart_7344106 baseEnd_7344106 := by
    simpa [prefixWord, tailWord_7344106, baseEnd_7344106] using wordTrace_append hprefix tailTrace_7344106
  have hstable : (prefixWord ++ tailWord_7344106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344106).length < 2 ^ (prefixWord ++ tailWord_7344106).sum := by decide
  have hdescent : baseEnd_7344106 < baseStart_7344106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344123 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 1, 5, 2]
def baseStart_7344123 : Nat := 118140960795 + 7344123 * 2 ^ 59
def prefixEnd_7344123 : Nat := 4983230072969 + 3 ^ 40 * 7344123 * 2
def baseEnd_7344123 : Nat := 3771065084739874818687499

theorem tailTrace_7344123 : CollatzResearch.WordTrace tailWord_7344123 prefixEnd_7344123 3771065084739874818687499 := by
  unfold tailWord_7344123
  simp only [CollatzResearch.WordTrace]
  refine ⟨267862171572504122195469023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178574781048336081463646015 267862171572504122195469023)
  ·
    refine ⟨401793257358756183293203535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267862171572504122195469023 401793257358756183293203535)
    ·
      refine ⟨602689886038134274939805303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401793257358756183293203535 602689886038134274939805303)
      ·
        refine ⟨904034829057201412409707955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602689886038134274939805303 904034829057201412409707955)
        ·
          refine ⟨1356052243585802118614561933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904034829057201412409707955 1356052243585802118614561933)
          ·
            refine ⟨508519591344675794480460725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1356052243585802118614561933 508519591344675794480460725)
            ·
              refine ⟨47673711688563355732543193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 508519591344675794480460725 47673711688563355732543193)
              ·
                refine ⟨35755283766422516799407395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47673711688563355732543193 35755283766422516799407395)
                ·
                  refine ⟨53632925649633775199111093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35755283766422516799407395 53632925649633775199111093)
                  ·
                    refine ⟨5028086779653166424916665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53632925649633775199111093 5028086779653166424916665)
                    ·
                      refine ⟨3771065084739874818687499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028086779653166424916665 3771065084739874818687499)
                      ·
                        rfl

theorem cell23_7344123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 5, 2].length) (baseStart_7344123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344123 prefixEnd_7344123 := by exact prefixLift 7344123
  have htrace : WordTrace (prefixWord ++ tailWord_7344123) baseStart_7344123 baseEnd_7344123 := by
    simpa [prefixWord, tailWord_7344123, baseEnd_7344123] using wordTrace_append hprefix tailTrace_7344123
  have hstable : (prefixWord ++ tailWord_7344123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344123).length < 2 ^ (prefixWord ++ tailWord_7344123).sum := by decide
  have hdescent : baseEnd_7344123 < baseStart_7344123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344133 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 1, 5]
def baseStart_7344133 : Nat := 118140960795 + 7344133 * 2 ^ 59
def prefixEnd_7344133 : Nat := 4983230072969 + 3 ^ 40 * 7344133 * 2
def baseEnd_7344133 : Nat := 1257023406515473259854151

theorem tailTrace_7344133 : CollatzResearch.WordTrace tailWord_7344133 prefixEnd_7344133 1257023406515473259854151 := by
  unfold tailWord_7344133
  simp only [CollatzResearch.WordTrace]
  refine ⟨267862536302467893903333053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178575024201645262602222035 267862536302467893903333053)
  ·
    refine ⟨100448451113425460213749895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267862536302467893903333053 100448451113425460213749895)
    ·
      refine ⟨150672676670138190320624843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100448451113425460213749895 150672676670138190320624843)
      ·
        refine ⟨226009015005207285480937265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150672676670138190320624843 226009015005207285480937265)
        ·
          refine ⟨169506761253905464110702949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226009015005207285480937265 169506761253905464110702949)
          ·
            refine ⟨31782517735107274520756803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169506761253905464110702949 31782517735107274520756803)
            ·
              refine ⟨47673776602660911781135205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31782517735107274520756803 47673776602660911781135205)
              ·
                refine ⟨8938833112998920958962851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47673776602660911781135205 8938833112998920958962851)
                ·
                  refine ⟨13408249669498381438444277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8938833112998920958962851 13408249669498381438444277)
                  ·
                    refine ⟨1257023406515473259854151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13408249669498381438444277 1257023406515473259854151)
                    ·
                      rfl

theorem cell23_7344133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_7344133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344133 prefixEnd_7344133 := by exact prefixLift 7344133
  have htrace : WordTrace (prefixWord ++ tailWord_7344133) baseStart_7344133 baseEnd_7344133 := by
    simpa [prefixWord, tailWord_7344133, baseEnd_7344133] using wordTrace_append hprefix tailTrace_7344133
  have hstable : (prefixWord ++ tailWord_7344133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344133).length < 2 ^ (prefixWord ++ tailWord_7344133).sum := by decide
  have hdescent : baseEnd_7344133 < baseStart_7344133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344140 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 2, 3, 2]
def baseStart_7344140 : Nat := 118140960795 + 7344140 * 2 ^ 59
def prefixEnd_7344140 : Nat := 4983230072969 + 3 ^ 40 * 7344140 * 2
def baseEnd_7344140 : Nat := 3771073813911001252174921

theorem tailTrace_7344140 : CollatzResearch.WordTrace tailWord_7344140 prefixEnd_7344140 3771073813911001252174921 := by
  unfold tailWord_7344140
  simp only [CollatzResearch.WordTrace]
  refine ⟨133931395806721267049418937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178575194408961689399225249 133931395806721267049418937)
  ·
    refine ⟨100448546855040950287064203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133931395806721267049418937 100448546855040950287064203)
    ·
      refine ⟨150672820282561425430596305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100448546855040950287064203 150672820282561425430596305)
      ·
        refine ⟨113004615211921069072947229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150672820282561425430596305 113004615211921069072947229)
        ·
          refine ⟨42376730704470400902355211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113004615211921069072947229 42376730704470400902355211)
          ·
            refine ⟨63565096056705601353532817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42376730704470400902355211 63565096056705601353532817)
            ·
              refine ⟨47673822042529201015149613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63565096056705601353532817 47673822042529201015149613)
              ·
                refine ⟨17877683265948450380681105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47673822042529201015149613 17877683265948450380681105)
                ·
                  refine ⟨13408262449461337785510829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17877683265948450380681105 13408262449461337785510829)
                  ·
                    refine ⟨5028098418548001669566561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13408262449461337785510829 5028098418548001669566561)
                    ·
                      refine ⟨3771073813911001252174921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028098418548001669566561 3771073813911001252174921)
                      ·
                        rfl

theorem cell23_7344140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_7344140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344140 prefixEnd_7344140 := by exact prefixLift 7344140
  have htrace : WordTrace (prefixWord ++ tailWord_7344140) baseStart_7344140 baseEnd_7344140 := by
    simpa [prefixWord, tailWord_7344140, baseEnd_7344140] using wordTrace_append hprefix tailTrace_7344140
  have hstable : (prefixWord ++ tailWord_7344140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344140).length < 2 ^ (prefixWord ++ tailWord_7344140).sum := by decide
  have hdescent : baseEnd_7344140 < baseStart_7344140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344147 : List Nat := [1, 1, 1, 2, 1, 4, 5, 3, 1, 1, 3]
def baseStart_7344147 : Nat := 118140960795 + 7344147 * 2 ^ 59
def prefixEnd_7344147 : Nat := 4983230072969 + 3 ^ 40 * 7344147 * 2
def baseEnd_7344147 : Nat := 3771077408275582724787389

theorem tailTrace_7344147 : CollatzResearch.WordTrace tailWord_7344147 prefixEnd_7344147 3771077408275582724787389 := by
  unfold tailWord_7344147
  simp only [CollatzResearch.WordTrace]
  refine ⟨267863046924417174294342695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178575364616278116196228463 267863046924417174294342695)
  ·
    refine ⟨401794570386625761441514043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267863046924417174294342695 401794570386625761441514043)
    ·
      refine ⟨602691855579938642162271065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401794570386625761441514043 602691855579938642162271065)
      ·
        refine ⟨452018891684953981621703299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602691855579938642162271065 452018891684953981621703299)
        ·
          refine ⟨678028337527430972432554949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452018891684953981621703299 678028337527430972432554949)
          ·
            refine ⟨127130313286393307331104053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 678028337527430972432554949 127130313286393307331104053)
            ·
              refine ⟨11918466870599372562291005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127130313286393307331104053 11918466870599372562291005)
              ·
                refine ⟨4469425076474764710859127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11918466870599372562291005 4469425076474764710859127)
                ·
                  refine ⟨6704137614712147066288691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4469425076474764710859127 6704137614712147066288691)
                  ·
                    refine ⟨10056206422068220599433037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6704137614712147066288691 10056206422068220599433037)
                    ·
                      refine ⟨3771077408275582724787389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10056206422068220599433037 3771077408275582724787389)
                      ·
                        rfl

theorem cell23_7344147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 1, 1, 3].length) (baseStart_7344147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344147 prefixEnd_7344147 := by exact prefixLift 7344147
  have htrace : WordTrace (prefixWord ++ tailWord_7344147) baseStart_7344147 baseEnd_7344147 := by
    simpa [prefixWord, tailWord_7344147, baseEnd_7344147] using wordTrace_append hprefix tailTrace_7344147
  have hstable : (prefixWord ++ tailWord_7344147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344147).length < 2 ^ (prefixWord ++ tailWord_7344147).sum := by decide
  have hdescent : baseEnd_7344147 < baseStart_7344147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344157 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_7344157 : Nat := 118140960795 + 7344157 * 2 ^ 59
def prefixEnd_7344157 : Nat := 4983230072969 + 3 ^ 40 * 7344157 * 2
def baseEnd_7344157 : Nat := 3771082543082127685662343

theorem tailTrace_7344157 : CollatzResearch.WordTrace tailWord_7344157 prefixEnd_7344157 3771082543082127685662343 := by
  unfold tailWord_7344157
  simp only [CollatzResearch.WordTrace]
  refine ⟨267863411654380946002206725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178575607769587297334804483 267863411654380946002206725)
  ·
    refine ⟨50224389685196427375413761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267863411654380946002206725 50224389685196427375413761)
    ·
      refine ⟨37668292263897320531560321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50224389685196427375413761 37668292263897320531560321)
      ·
        refine ⟨28251219197922990398670241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37668292263897320531560321 28251219197922990398670241)
        ·
          refine ⟨21188414398442242799002681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28251219197922990398670241 21188414398442242799002681)
          ·
            refine ⟨15891310798831682099252011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21188414398442242799002681 15891310798831682099252011)
            ·
              refine ⟨23836966198247523148878017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15891310798831682099252011 23836966198247523148878017)
              ·
                refine ⟨17877724648685642361658513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23836966198247523148878017 17877724648685642361658513)
                ·
                  refine ⟨13408293486514231771243885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17877724648685642361658513 13408293486514231771243885)
                  ·
                    refine ⟨5028110057442836914216457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13408293486514231771243885 5028110057442836914216457)
                    ·
                      refine ⟨3771082543082127685662343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028110057442836914216457 3771082543082127685662343)
                      ·
                        rfl

theorem cell23_7344157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_7344157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344157 prefixEnd_7344157 := by exact prefixLift 7344157
  have htrace : WordTrace (prefixWord ++ tailWord_7344157) baseStart_7344157 baseEnd_7344157 := by
    simpa [prefixWord, tailWord_7344157, baseEnd_7344157] using wordTrace_append hprefix tailTrace_7344157
  have hstable : (prefixWord ++ tailWord_7344157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344157).length < 2 ^ (prefixWord ++ tailWord_7344157).sum := by decide
  have hdescent : baseEnd_7344157 < baseStart_7344157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344163 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 4, 4]
def baseStart_7344163 : Nat := 118140960795 + 7344163 * 2 ^ 59
def prefixEnd_7344163 : Nat := 4983230072969 + 3 ^ 40 * 7344163 * 2
def baseEnd_7344163 : Nat := 1257028541322018220729105

theorem tailTrace_7344163 : CollatzResearch.WordTrace tailWord_7344163 prefixEnd_7344163 1257028541322018220729105 := by
  unfold tailWord_7344163
  simp only [CollatzResearch.WordTrace]
  refine ⟨267863630492359209026925143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178575753661572806017950095 267863630492359209026925143)
  ·
    refine ⟨401795445738538813540387715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267863630492359209026925143 401795445738538813540387715)
    ·
      refine ⟨602693168607808220310581573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401795445738538813540387715 602693168607808220310581573)
      ·
        refine ⟨113004969113964041308234045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 602693168607808220310581573 113004969113964041308234045)
        ·
          refine ⟨42376863417736515490587767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113004969113964041308234045 42376863417736515490587767)
          ·
            refine ⟨63565295126604773235881651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42376863417736515490587767 63565295126604773235881651)
            ·
              refine ⟨95347942689907159853822477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63565295126604773235881651 95347942689907159853822477)
              ·
                refine ⟨35755478508715184945183429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95347942689907159853822477 35755478508715184945183429)
                ·
                  refine ⟨6704152220384097177221893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35755478508715184945183429 6704152220384097177221893)
                  ·
                    refine ⟨1257028541322018220729105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6704152220384097177221893 1257028541322018220729105)
                    ·
                      rfl

theorem cell23_7344163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 4].length) (baseStart_7344163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344163 prefixEnd_7344163 := by exact prefixLift 7344163
  have htrace : WordTrace (prefixWord ++ tailWord_7344163) baseStart_7344163 baseEnd_7344163 := by
    simpa [prefixWord, tailWord_7344163, baseEnd_7344163] using wordTrace_append hprefix tailTrace_7344163
  have hstable : (prefixWord ++ tailWord_7344163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344163).length < 2 ^ (prefixWord ++ tailWord_7344163).sum := by decide
  have hdescent : baseEnd_7344163 < baseStart_7344163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344164 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_7344164 : Nat := 118140960795 + 7344164 * 2 ^ 59
def prefixEnd_7344164 : Nat := 4983230072969 + 3 ^ 40 * 7344164 * 2
def baseEnd_7344164 : Nat := 3771086137446709158274811

theorem tailTrace_7344164 : CollatzResearch.WordTrace tailWord_7344164 prefixEnd_7344164 3771086137446709158274811 := by
  unfold tailWord_7344164
  simp only [CollatzResearch.WordTrace]
  refine ⟨133931833482677793098855773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178575777976903724131807697 133931833482677793098855773)
  ·
    refine ⟨50224437556004172412070915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133931833482677793098855773 50224437556004172412070915)
    ·
      refine ⟨75336656334006258618106373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50224437556004172412070915 75336656334006258618106373)
      ·
        refine ⟨14125623062626173490894945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75336656334006258618106373 14125623062626173490894945)
        ·
          refine ⟨10594217296969630118171209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14125623062626173490894945 10594217296969630118171209)
          ·
            refine ⟨7945662972727222588628407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10594217296969630118171209 7945662972727222588628407)
            ·
              refine ⟨11918494459090833882942611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7945662972727222588628407 11918494459090833882942611)
              ·
                refine ⟨17877741688636250824413917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11918494459090833882942611 17877741688636250824413917)
                ·
                  refine ⟨6704153133238594059155219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17877741688636250824413917 6704153133238594059155219)
                  ·
                    refine ⟨10056229699857891088732829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6704153133238594059155219 10056229699857891088732829)
                    ·
                      refine ⟨3771086137446709158274811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10056229699857891088732829 3771086137446709158274811)
                      ·
                        rfl

theorem cell23_7344164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_7344164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344164 prefixEnd_7344164 := by exact prefixLift 7344164
  have htrace : WordTrace (prefixWord ++ tailWord_7344164) baseStart_7344164 baseEnd_7344164 := by
    simpa [prefixWord, tailWord_7344164, baseEnd_7344164] using wordTrace_append hprefix tailTrace_7344164
  have hstable : (prefixWord ++ tailWord_7344164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344164).length < 2 ^ (prefixWord ++ tailWord_7344164).sum := by decide
  have hdescent : baseEnd_7344164 < baseStart_7344164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344176 : List Nat := [2, 1, 1, 1, 2, 5, 1, 10]
def baseStart_7344176 : Nat := 118140960795 + 7344176 * 2 ^ 59
def prefixEnd_7344176 : Nat := 4983230072969 + 3 ^ 40 * 7344176 * 2
def baseEnd_7344176 : Nat := 139670085156094930049065

theorem tailTrace_7344176 : CollatzResearch.WordTrace tailWord_7344176 prefixEnd_7344176 139670085156094930049065 := by
  unfold tailWord_7344176
  simp only [CollatzResearch.WordTrace]
  refine ⟨133932052320656056123574191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178576069760874741498098921 133932052320656056123574191)
  ·
    refine ⟨200898078480984084185361287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133932052320656056123574191 200898078480984084185361287)
    ·
      refine ⟨301347117721476126278041931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200898078480984084185361287 301347117721476126278041931)
      ·
        refine ⟨452020676582214189417062897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301347117721476126278041931 452020676582214189417062897)
        ·
          refine ⟨339015507436660642062797173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452020676582214189417062897 339015507436660642062797173)
          ·
            refine ⟨31782703822186935193387235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 339015507436660642062797173 31782703822186935193387235)
            ·
              refine ⟨47674055733280402790080853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31782703822186935193387235 47674055733280402790080853)
              ·
                refine ⟨139670085156094930049065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47674055733280402790080853 139670085156094930049065)
                ·
                  rfl

theorem cell23_7344176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 10].length) (baseStart_7344176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344176 prefixEnd_7344176 := by exact prefixLift 7344176
  have htrace : WordTrace (prefixWord ++ tailWord_7344176) baseStart_7344176 baseEnd_7344176 := by
    simpa [prefixWord, tailWord_7344176, baseEnd_7344176] using wordTrace_append hprefix tailTrace_7344176
  have hstable : (prefixWord ++ tailWord_7344176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344176).length < 2 ^ (prefixWord ++ tailWord_7344176).sum := by decide
  have hdescent : baseEnd_7344176 < baseStart_7344176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344193 : List Nat := [1, 2, 5, 1, 2, 1, 2, 9]
def baseStart_7344193 : Nat := 118140960795 + 7344193 * 2 ^ 59
def prefixEnd_7344193 : Nat := 4983230072969 + 3 ^ 40 * 7344193 * 2
def baseEnd_7344193 : Nat := 139670408458729242400451

theorem tailTrace_7344193 : CollatzResearch.WordTrace tailWord_7344193 prefixEnd_7344193 139670408458729242400451 := by
  unfold tailWord_7344193
  simp only [CollatzResearch.WordTrace]
  refine ⟨267864724682250524150517233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178576483121500349433678155 267864724682250524150517233)
  ·
    refine ⟨200898543511687893112887925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267864724682250524150517233 200898543511687893112887925)
    ·
      refine ⟨18834238454220739979333243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200898543511687893112887925 18834238454220739979333243)
      ·
        refine ⟨28251357681331109968999865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18834238454220739979333243 28251357681331109968999865)
        ·
          refine ⟨21188518260998332476749899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28251357681331109968999865 21188518260998332476749899)
          ·
            refine ⟨31782777391497498715124849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21188518260998332476749899 31782777391497498715124849)
            ·
              refine ⟨23837083043623124036343637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31782777391497498715124849 23837083043623124036343637)
              ·
                refine ⟨139670408458729242400451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23837083043623124036343637 139670408458729242400451)
                ·
                  rfl

theorem cell23_7344193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 9].length) (baseStart_7344193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344193 prefixEnd_7344193 := by exact prefixLift 7344193
  have htrace : WordTrace (prefixWord ++ tailWord_7344193) baseStart_7344193 baseEnd_7344193 := by
    simpa [prefixWord, tailWord_7344193, baseEnd_7344193] using wordTrace_append hprefix tailTrace_7344193
  have hstable : (prefixWord ++ tailWord_7344193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344193).length < 2 ^ (prefixWord ++ tailWord_7344193).sum := by decide
  have hdescent : baseEnd_7344193 < baseStart_7344193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344203 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 3]
def baseStart_7344203 : Nat := 118140960795 + 7344203 * 2 ^ 59
def prefixEnd_7344203 : Nat := 4983230072969 + 3 ^ 40 * 7344203 * 2
def baseEnd_7344203 : Nat := 3771106163192234505687131

theorem tailTrace_7344203 : CollatzResearch.WordTrace tailWord_7344203 prefixEnd_7344203 3771106163192234505687131 := by
  unfold tailWord_7344203
  simp only [CollatzResearch.WordTrace]
  refine ⟨267865089412214295858381263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178576726274809530572254175 267865089412214295858381263)
  ·
    refine ⟨401797634118321443787571895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267865089412214295858381263 401797634118321443787571895)
    ·
      refine ⟨602696451177482165681357843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401797634118321443787571895 602696451177482165681357843)
      ·
        refine ⟨904044676766223248522036765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602696451177482165681357843 904044676766223248522036765)
        ·
          refine ⟨339016753787333718195763787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 904044676766223248522036765 339016753787333718195763787)
          ·
            refine ⟨508525130681000577293645681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339016753787333718195763787 508525130681000577293645681)
            ·
              refine ⟨381393848010750432970234261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508525130681000577293645681 381393848010750432970234261)
              ·
                refine ⟨17877836625503926545479731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 381393848010750432970234261 17877836625503926545479731)
                ·
                  refine ⟨26816754938255889818219597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17877836625503926545479731 26816754938255889818219597)
                  ·
                    refine ⟨10056283101845958681832349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26816754938255889818219597 10056283101845958681832349)
                    ·
                      refine ⟨3771106163192234505687131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10056283101845958681832349 3771106163192234505687131)
                      ·
                        rfl

theorem cell23_7344203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 3].length) (baseStart_7344203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344203 prefixEnd_7344203 := by exact prefixLift 7344203
  have htrace : WordTrace (prefixWord ++ tailWord_7344203) baseStart_7344203 baseEnd_7344203 := by
    simpa [prefixWord, tailWord_7344203, baseEnd_7344203] using wordTrace_append hprefix tailTrace_7344203
  have hstable : (prefixWord ++ tailWord_7344203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344203).length < 2 ^ (prefixWord ++ tailWord_7344203).sum := by decide
  have hdescent : baseEnd_7344203 < baseStart_7344203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344214 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_7344214 : Nat := 118140960795 + 7344214 * 2 ^ 59
def prefixEnd_7344214 : Nat := 4983230072969 + 3 ^ 40 * 7344214 * 2
def baseEnd_7344214 : Nat := 1257037270493144654216527

theorem tailTrace_7344214 : CollatzResearch.WordTrace tailWord_7344214 prefixEnd_7344214 1257037270493144654216527 := by
  unfold tailWord_7344214
  simp only [CollatzResearch.WordTrace]
  refine ⟨16741593163448402796064481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178576993743449629824687797 16741593163448402796064481)
  ·
    refine ⟨12556194872586302097048361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16741593163448402796064481 12556194872586302097048361)
    ·
      refine ⟨9417146154439726572786271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12556194872586302097048361 9417146154439726572786271)
      ·
        refine ⟨14125719231659589859179407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9417146154439726572786271 14125719231659589859179407)
        ·
          refine ⟨21188578847489384788769111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14125719231659589859179407 21188578847489384788769111)
          ·
            refine ⟨31782868271234077183153667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21188578847489384788769111 31782868271234077183153667)
            ·
              refine ⟨47674302406851115774730501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31782868271234077183153667 47674302406851115774730501)
              ·
                refine ⟨8938931701284584207761969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47674302406851115774730501 8938931701284584207761969)
                ·
                  refine ⟨6704198775963438155821477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8938931701284584207761969 6704198775963438155821477)
                  ·
                    refine ⟨1257037270493144654216527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6704198775963438155821477 1257037270493144654216527)
                    ·
                      rfl

theorem cell23_7344214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_7344214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344214 prefixEnd_7344214 := by exact prefixLift 7344214
  have htrace : WordTrace (prefixWord ++ tailWord_7344214) baseStart_7344214 baseEnd_7344214 := by
    simpa [prefixWord, tailWord_7344214, baseEnd_7344214] using wordTrace_append hprefix tailTrace_7344214
  have hstable : (prefixWord ++ tailWord_7344214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344214).length < 2 ^ (prefixWord ++ tailWord_7344214).sum := by decide
  have hdescent : baseEnd_7344214 < baseStart_7344214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344237 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_7344237 : Nat := 118140960795 + 7344237 * 2 ^ 59
def prefixEnd_7344237 : Nat := 4983230072969 + 3 ^ 40 * 7344237 * 2
def baseEnd_7344237 : Nat := 3771123621534487372661975

theorem tailTrace_7344237 : CollatzResearch.WordTrace tailWord_7344237 prefixEnd_7344237 3771123621534487372661975 := by
  unfold tailWord_7344237
  simp only [CollatzResearch.WordTrace]
  refine ⟨267866329494091119665118965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178577552996060746443412643 267866329494091119665118965)
  ·
    refine ⟨25112468390071042468604903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267866329494091119665118965 25112468390071042468604903)
    ·
      refine ⟨37668702585106563702907355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25112468390071042468604903 37668702585106563702907355)
      ·
        refine ⟨56503053877659845554361033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37668702585106563702907355 56503053877659845554361033)
        ·
          refine ⟨42377290408244884165770775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56503053877659845554361033 42377290408244884165770775)
          ·
            refine ⟨63565935612367326248656163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42377290408244884165770775 63565935612367326248656163)
            ·
              refine ⟨95348903418550989372984245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63565935612367326248656163 95348903418550989372984245)
              ·
                refine ⟨8938959695489155253717273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95348903418550989372984245 8938959695489155253717273)
                ·
                  refine ⟨6704219771616866440287955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8938959695489155253717273 6704219771616866440287955)
                  ·
                    refine ⟨10056329657425299660431933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6704219771616866440287955 10056329657425299660431933)
                    ·
                      refine ⟨3771123621534487372661975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10056329657425299660431933 3771123621534487372661975)
                      ·
                        rfl

theorem cell23_7344237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_7344237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344237 prefixEnd_7344237 := by exact prefixLift 7344237
  have htrace : WordTrace (prefixWord ++ tailWord_7344237) baseStart_7344237 baseEnd_7344237 := by
    simpa [prefixWord, tailWord_7344237, baseEnd_7344237] using wordTrace_append hprefix tailTrace_7344237
  have hstable : (prefixWord ++ tailWord_7344237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344237).length < 2 ^ (prefixWord ++ tailWord_7344237).sum := by decide
  have hdescent : baseEnd_7344237 < baseStart_7344237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344263 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_7344263 : Nat := 118140960795 + 7344263 * 2 ^ 59
def prefixEnd_7344263 : Nat := 4983230072969 + 3 ^ 40 * 7344263 * 2
def baseEnd_7344263 : Nat := 3771136972031504270936855

theorem tailTrace_7344263 : CollatzResearch.WordTrace tailWord_7344263 prefixEnd_7344263 3771136972031504270936855 := by
  unfold tailWord_7344263
  simp only [CollatzResearch.WordTrace]
  refine ⟨267867277791996926105565443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178578185194664617403710295 267867277791996926105565443)
  ·
    refine ⟨401800916687995389158348165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267867277791996926105565443 401800916687995389158348165)
    ·
      refine ⟨75337671878999135467190281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401800916687995389158348165 75337671878999135467190281)
      ·
        refine ⟨56503253909249351600392711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75337671878999135467190281 56503253909249351600392711)
        ·
          refine ⟨84754880863874027400589067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56503253909249351600392711 84754880863874027400589067)
          ·
            refine ⟨127132321295811041100883601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84754880863874027400589067 127132321295811041100883601)
            ·
              refine ⟨95349240971858280825662701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127132321295811041100883601 95349240971858280825662701)
              ·
                refine ⟨35755965364446855309623513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95349240971858280825662701 35755965364446855309623513)
                ·
                  refine ⟨26816974023335141482217635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35755965364446855309623513 26816974023335141482217635)
                  ·
                    refine ⟨40225461035002712223326453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26816974023335141482217635 40225461035002712223326453)
                    ·
                      refine ⟨3771136972031504270936855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40225461035002712223326453 3771136972031504270936855)
                      ·
                        rfl

theorem cell23_7344263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_7344263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344263 prefixEnd_7344263 := by exact prefixLift 7344263
  have htrace : WordTrace (prefixWord ++ tailWord_7344263) baseStart_7344263 baseEnd_7344263 := by
    simpa [prefixWord, tailWord_7344263, baseEnd_7344263] using wordTrace_append hprefix tailTrace_7344263
  have hstable : (prefixWord ++ tailWord_7344263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344263).length < 2 ^ (prefixWord ++ tailWord_7344263).sum := by decide
  have hdescent : baseEnd_7344263 < baseStart_7344263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344264 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 1, 3, 2]
def baseStart_7344264 : Nat := 118140960795 + 7344264 * 2 ^ 59
def prefixEnd_7344264 : Nat := 4983230072969 + 3 ^ 40 * 7344264 * 2
def baseEnd_7344264 : Nat := 3771137485512158767024351

theorem tailTrace_7344264 : CollatzResearch.WordTrace tailWord_7344264 prefixEnd_7344264 3771137485512158767024351 := by
  unfold tailWord_7344264
  simp only [CollatzResearch.WordTrace]
  refine ⟨133933657132496651638175923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178578209509995535517567897 133933657132496651638175923)
  ·
    refine ⟨200900485698744977457263885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133933657132496651638175923 200900485698744977457263885)
    ·
      refine ⟨75337682137029366546473957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200900485698744977457263885 75337682137029366546473957)
      ·
        refine ⟨14125815400693006227463867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75337682137029366546473957 14125815400693006227463867)
        ·
          refine ⟨21188723101039509341195801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14125815400693006227463867 21188723101039509341195801)
          ·
            refine ⟨15891542325779632005896851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21188723101039509341195801 15891542325779632005896851)
            ·
              refine ⟨23837313488669448008845277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15891542325779632005896851 23837313488669448008845277)
              ·
                refine ⟨8938992558251043003316979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23837313488669448008845277 8938992558251043003316979)
                ·
                  refine ⟨13408488837376564504975469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8938992558251043003316979 13408488837376564504975469)
                  ·
                    refine ⟨5028183314016211689365801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13408488837376564504975469 5028183314016211689365801)
                    ·
                      refine ⟨3771137485512158767024351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028183314016211689365801 3771137485512158767024351)
                      ·
                        rfl

theorem cell23_7344264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_7344264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344264 prefixEnd_7344264 := by exact prefixLift 7344264
  have htrace : WordTrace (prefixWord ++ tailWord_7344264) baseStart_7344264 baseEnd_7344264 := by
    simpa [prefixWord, tailWord_7344264, baseEnd_7344264] using wordTrace_append hprefix tailTrace_7344264
  have hstable : (prefixWord ++ tailWord_7344264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344264).length < 2 ^ (prefixWord ++ tailWord_7344264).sum := by decide
  have hdescent : baseEnd_7344264 < baseStart_7344264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344277 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 4, 2, 2]
def baseStart_7344277 : Nat := 118140960795 + 7344277 * 2 ^ 59
def prefixEnd_7344277 : Nat := 4983230072969 + 3 ^ 40 * 7344277 * 2
def baseEnd_7344277 : Nat := 3771144160760667216161791

theorem tailTrace_7344277 : CollatzResearch.WordTrace tailWord_7344277 prefixEnd_7344277 3771144160760667216161791 := by
  unfold tailWord_7344277
  simp only [CollatzResearch.WordTrace]
  refine ⟨267867788413946206496575085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178578525609297470997716723 267867788413946206496575085)
  ·
    refine ⟨100450420655229827436215657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267867788413946206496575085 100450420655229827436215657)
    ·
      refine ⟨75337815491422370577161743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100450420655229827436215657 75337815491422370577161743)
      ·
        refine ⟨113006723237133555865742615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75337815491422370577161743 113006723237133555865742615)
        ·
          refine ⟨169510084855700333798613923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113006723237133555865742615 169510084855700333798613923)
          ·
            refine ⟨254265127283550500697920885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169510084855700333798613923 254265127283550500697920885)
            ·
              refine ⟨23837355682832859440430083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254265127283550500697920885 23837355682832859440430083)
              ·
                refine ⟨35756033524249289160645125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23837355682832859440430083 35756033524249289160645125)
                ·
                  refine ⟨6704256285796741717620961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35756033524249289160645125 6704256285796741717620961)
                  ·
                    refine ⟨5028192214347556288215721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6704256285796741717620961 5028192214347556288215721)
                    ·
                      refine ⟨3771144160760667216161791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028192214347556288215721 3771144160760667216161791)
                      ·
                        rfl

theorem cell23_7344277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_7344277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344277 prefixEnd_7344277 := by exact prefixLift 7344277
  have htrace : WordTrace (prefixWord ++ tailWord_7344277) baseStart_7344277 baseEnd_7344277 := by
    simpa [prefixWord, tailWord_7344277, baseEnd_7344277] using wordTrace_append hprefix tailTrace_7344277
  have hstable : (prefixWord ++ tailWord_7344277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344277).length < 2 ^ (prefixWord ++ tailWord_7344277).sum := by decide
  have hdescent : baseEnd_7344277 < baseStart_7344277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344313 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 1, 7]
def baseStart_7344313 : Nat := 118140960795 + 7344313 * 2 ^ 59
def prefixEnd_7344313 : Nat := 4983230072969 + 3 ^ 40 * 7344313 * 2
def baseEnd_7344313 : Nat := 1257054215354743025103875

theorem tailTrace_7344313 : CollatzResearch.WordTrace tailWord_7344313 prefixEnd_7344313 1257054215354743025103875 := by
  unfold tailWord_7344313
  simp only [CollatzResearch.WordTrace]
  refine ⟨267869101441815784644885593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178579400961210523096590395 267869101441815784644885593)
  ·
    refine ⟨200901826081361838483664195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267869101441815784644885593 200901826081361838483664195)
    ·
      refine ⟨301352739122042757725496293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200901826081361838483664195 301352739122042757725496293)
      ·
        refine ⟨56503638585383017073530555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301352739122042757725496293 56503638585383017073530555)
        ·
          refine ⟨84755457878074525610295833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56503638585383017073530555 84755457878074525610295833)
          ·
            refine ⟨63566593408555894207721875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84755457878074525610295833 63566593408555894207721875)
            ·
              refine ⟨95349890112833841311582813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63566593408555894207721875 95349890112833841311582813)
              ·
                refine ⟨35756208792312690491843555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95349890112833841311582813 35756208792312690491843555)
                ·
                  refine ⟨53634313188469035737765333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35756208792312690491843555 53634313188469035737765333)
                  ·
                    refine ⟨1257054215354743025103875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53634313188469035737765333 1257054215354743025103875)
                    ·
                      rfl

theorem cell23_7344313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_7344313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344313 prefixEnd_7344313 := by exact prefixLift 7344313
  have htrace : WordTrace (prefixWord ++ tailWord_7344313) baseStart_7344313 baseEnd_7344313 := by
    simpa [prefixWord, tailWord_7344313, baseEnd_7344313] using wordTrace_append hprefix tailTrace_7344313
  have hstable : (prefixWord ++ tailWord_7344313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344313).length < 2 ^ (prefixWord ++ tailWord_7344313).sum := by decide
  have hdescent : baseEnd_7344313 < baseStart_7344313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344330 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_7344330 : Nat := 118140960795 + 7344330 * 2 ^ 59
def prefixEnd_7344330 : Nat := 4983230072969 + 3 ^ 40 * 7344330 * 2
def baseEnd_7344330 : Nat := 1257057125078451836266349

theorem tailTrace_7344330 : CollatzResearch.WordTrace tailWord_7344330 prefixEnd_7344330 1257057125078451836266349 := by
  unfold tailWord_7344330
  simp only [CollatzResearch.WordTrace]
  refine ⟨66967430370688549137063611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178579814321836131032169629 66967430370688549137063611)
  ·
    refine ⟨100451145556032823705595417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66967430370688549137063611 100451145556032823705595417)
    ·
      refine ⟨75338359167024617779196563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100451145556032823705595417 75338359167024617779196563)
      ·
        refine ⟨113007538750536926668794845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75338359167024617779196563 113007538750536926668794845)
        ·
          refine ⟨42377827031451347500798067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113007538750536926668794845 42377827031451347500798067)
          ·
            refine ⟨63566740547177021251197101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42377827031451347500798067 63566740547177021251197101)
            ·
              refine ⟨23837527705191382969198913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63566740547177021251197101 23837527705191382969198913)
              ·
                refine ⟨17878145778893537226899185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23837527705191382969198913 17878145778893537226899185)
                ·
                  refine ⟨13408609334170152920174389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17878145778893537226899185 13408609334170152920174389)
                  ·
                    refine ⟨1257057125078451836266349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13408609334170152920174389 1257057125078451836266349)
                    ·
                      rfl

theorem cell23_7344330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_7344330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344330 prefixEnd_7344330 := by exact prefixLift 7344330
  have htrace : WordTrace (prefixWord ++ tailWord_7344330) baseStart_7344330 baseEnd_7344330 := by
    simpa [prefixWord, tailWord_7344330, baseEnd_7344330] using wordTrace_append hprefix tailTrace_7344330
  have hstable : (prefixWord ++ tailWord_7344330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344330).length < 2 ^ (prefixWord ++ tailWord_7344330).sum := by decide
  have hdescent : baseEnd_7344330 < baseStart_7344330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344334 : List Nat := [4, 1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_7344334 : Nat := 118140960795 + 7344334 * 2 ^ 59
def prefixEnd_7344334 : Nat := 4983230072969 + 3 ^ 40 * 7344334 * 2
def baseEnd_7344334 : Nat := 419019269906441499238781

theorem tailTrace_7344334 : CollatzResearch.WordTrace tailWord_7344334 prefixEnd_7344334 419019269906441499238781 := by
  unfold tailWord_7344334
  simp only [CollatzResearch.WordTrace]
  refine ⟨33483733421842463153925007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178579911583159803487600037 33483733421842463153925007)
  ·
    refine ⟨50225600132763694730887511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33483733421842463153925007 50225600132763694730887511)
    ·
      refine ⟨75338400199145542096331267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50225600132763694730887511 75338400199145542096331267)
      ·
        refine ⟨113007600298718313144496901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75338400199145542096331267 113007600298718313144496901)
        ·
          refine ⟨21188925056009683714593169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113007600298718313144496901 21188925056009683714593169)
          ·
            refine ⟨15891693792007262785944877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21188925056009683714593169 15891693792007262785944877)
            ·
              refine ⟨5959385172002723544729329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15891693792007262785944877 5959385172002723544729329)
              ·
                refine ⟨4469538879002042658546997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5959385172002723544729329 4469538879002042658546997)
                ·
                  refine ⟨419019269906441499238781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4469538879002042658546997 419019269906441499238781)
                  ·
                    rfl

theorem cell23_7344334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_7344334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344334 prefixEnd_7344334 := by exact prefixLift 7344334
  have htrace : WordTrace (prefixWord ++ tailWord_7344334) baseStart_7344334 baseEnd_7344334 := by
    simpa [prefixWord, tailWord_7344334, baseEnd_7344334] using wordTrace_append hprefix tailTrace_7344334
  have hstable : (prefixWord ++ tailWord_7344334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344334).length < 2 ^ (prefixWord ++ tailWord_7344334).sum := by decide
  have hdescent : baseEnd_7344334 < baseStart_7344334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344367 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 4]
def baseStart_7344367 : Nat := 118140960795 + 7344367 * 2 ^ 59
def prefixEnd_7344367 : Nat := 4983230072969 + 3 ^ 40 * 7344367 * 2
def baseEnd_7344367 : Nat := 3771190374019571864036377

theorem tailTrace_7344367 : CollatzResearch.WordTrace tailWord_7344367 prefixEnd_7344367 3771190374019571864036377 := by
  unfold tailWord_7344367
  simp only [CollatzResearch.WordTrace]
  refine ⟨267871070983620151867351355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178580713989080101244900903 267871070983620151867351355)
  ·
    refine ⟨401806606475430227801027033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267871070983620151867351355 401806606475430227801027033)
    ·
      refine ⟨301354954856572670850770275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401806606475430227801027033 301354954856572670850770275)
      ·
        refine ⟨452032432284859006276155413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301354954856572670850770275 452032432284859006276155413)
        ·
          refine ⟨21189020263352765919194785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 452032432284859006276155413 21189020263352765919194785)
          ·
            refine ⟨15891765197514574439396089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21189020263352765919194785 15891765197514574439396089)
            ·
              refine ⟨11918823898135930829547067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15891765197514574439396089 11918823898135930829547067)
              ·
                refine ⟨17878235847203896244320601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11918823898135930829547067 17878235847203896244320601)
                ·
                  refine ⟨13408676885402922183240451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17878235847203896244320601 13408676885402922183240451)
                  ·
                    refine ⟨20113015328104383274860677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13408676885402922183240451 20113015328104383274860677)
                    ·
                      refine ⟨3771190374019571864036377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20113015328104383274860677 3771190374019571864036377)
                      ·
                        rfl

theorem cell23_7344367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 4].length) (baseStart_7344367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344367 prefixEnd_7344367 := by exact prefixLift 7344367
  have htrace : WordTrace (prefixWord ++ tailWord_7344367) baseStart_7344367 baseEnd_7344367 := by
    simpa [prefixWord, tailWord_7344367, baseEnd_7344367] using wordTrace_append hprefix tailTrace_7344367
  have hstable : (prefixWord ++ tailWord_7344367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344367).length < 2 ^ (prefixWord ++ tailWord_7344367).sum := by decide
  have hdescent : baseEnd_7344367 < baseStart_7344367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344417 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_7344417 : Nat := 118140960795 + 7344417 * 2 ^ 59
def prefixEnd_7344417 : Nat := 4983230072969 + 3 ^ 40 * 7344417 * 2
def baseEnd_7344417 : Nat := 3771216048052296668411147

theorem tailTrace_7344417 : CollatzResearch.WordTrace tailWord_7344417 prefixEnd_7344417 3771216048052296668411147 := by
  unfold tailWord_7344417
  simp only [CollatzResearch.WordTrace]
  refine ⟨267872894633439010406671505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178581929755626006937781003 267872894633439010406671505)
  ·
    refine ⟨200904670975079257805003629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267872894633439010406671505 200904670975079257805003629)
    ·
      refine ⟨75339251615654721676876361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200904670975079257805003629 75339251615654721676876361)
      ·
        refine ⟨56504438711741041257657271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75339251615654721676876361 56504438711741041257657271)
        ·
          refine ⟨84756658067611561886485907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56504438711741041257657271 84756658067611561886485907)
          ·
            refine ⟨127134987101417342829728861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84756658067611561886485907 127134987101417342829728861)
            ·
              refine ⟨47675620163031503561148323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127134987101417342829728861 47675620163031503561148323)
              ·
                refine ⟨71513430244547255341722485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47675620163031503561148323 71513430244547255341722485)
                ·
                  refine ⟨6704384085426305188286483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71513430244547255341722485 6704384085426305188286483)
                  ·
                    refine ⟨10056576128139457782429725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6704384085426305188286483 10056576128139457782429725)
                    ·
                      refine ⟨3771216048052296668411147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10056576128139457782429725 3771216048052296668411147)
                      ·
                        rfl

theorem cell23_7344417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_7344417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344417 prefixEnd_7344417 := by exact prefixLift 7344417
  have htrace : WordTrace (prefixWord ++ tailWord_7344417) baseStart_7344417 baseEnd_7344417 := by
    simpa [prefixWord, tailWord_7344417, baseEnd_7344417] using wordTrace_append hprefix tailTrace_7344417
  have hstable : (prefixWord ++ tailWord_7344417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344417).length < 2 ^ (prefixWord ++ tailWord_7344417).sum := by decide
  have hdescent : baseEnd_7344417 < baseStart_7344417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344421 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 2, 2, 3]
def baseStart_7344421 : Nat := 118140960795 + 7344421 * 2 ^ 59
def prefixEnd_7344421 : Nat := 4983230072969 + 3 ^ 40 * 7344421 * 2
def baseEnd_7344421 : Nat := 3771218101974914652761129

theorem tailTrace_7344421 : CollatzResearch.WordTrace tailWord_7344421 prefixEnd_7344421 3771218101974914652761129 := by
  unfold tailWord_7344421
  simp only [CollatzResearch.WordTrace]
  refine ⟨267873040525424519089817117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178582027016949679393211411 267873040525424519089817117)
  ·
    refine ⟨100452390197034194658681419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267873040525424519089817117 100452390197034194658681419)
    ·
      refine ⟨150678585295551291988022129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100452390197034194658681419 150678585295551291988022129)
      ·
        refine ⟨113008938971663468991016597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150678585295551291988022129 113008938971663468991016597)
        ·
          refine ⟨5297294014296725108953903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113008938971663468991016597 5297294014296725108953903)
          ·
            refine ⟨7945941021445087663430855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297294014296725108953903 7945941021445087663430855)
            ·
              refine ⟨11918911532167631495146283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7945941021445087663430855 11918911532167631495146283)
              ·
                refine ⟨17878367298251447242719425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11918911532167631495146283 17878367298251447242719425)
                ·
                  refine ⟨13408775473688585432039569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17878367298251447242719425 13408775473688585432039569)
                  ·
                    refine ⟨10056581605266439074029677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13408775473688585432039569 10056581605266439074029677)
                    ·
                      refine ⟨3771218101974914652761129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10056581605266439074029677 3771218101974914652761129)
                      ·
                        rfl

theorem cell23_7344421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_7344421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344421 prefixEnd_7344421 := by exact prefixLift 7344421
  have htrace : WordTrace (prefixWord ++ tailWord_7344421) baseStart_7344421 baseEnd_7344421 := by
    simpa [prefixWord, tailWord_7344421, baseEnd_7344421] using wordTrace_append hprefix tailTrace_7344421
  have hstable : (prefixWord ++ tailWord_7344421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344421).length < 2 ^ (prefixWord ++ tailWord_7344421).sum := by decide
  have hdescent : baseEnd_7344421 < baseStart_7344421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344437 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 1, 5]
def baseStart_7344437 : Nat := 118140960795 + 7344437 * 2 ^ 59
def prefixEnd_7344437 : Nat := 4983230072969 + 3 ^ 40 * 7344437 * 2
def baseEnd_7344437 : Nat := 1257075439221795530053685

theorem tailTrace_7344437 : CollatzResearch.WordTrace tailWord_7344437 prefixEnd_7344437 1257075439221795530053685 := by
  unfold tailWord_7344437
  simp only [CollatzResearch.WordTrace]
  refine ⟨267873624093366553822399565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178582416062244369214933043 267873624093366553822399565)
  ·
    refine ⟨100452609035012457683399837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267873624093366553822399565 100452609035012457683399837)
    ·
      refine ⟨37669728388129671631274939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100452609035012457683399837 37669728388129671631274939)
      ·
        refine ⟨56504592582194507446912409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37669728388129671631274939 56504592582194507446912409)
        ·
          refine ⟨42378444436645880585184307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56504592582194507446912409 42378444436645880585184307)
          ·
            refine ⟨63567666654968820877776461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42378444436645880585184307 63567666654968820877776461)
            ·
              refine ⟨23837874995613307829166173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63567666654968820877776461 23837874995613307829166173)
              ·
                refine ⟨8939203123354990435937315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23837874995613307829166173 8939203123354990435937315)
                ·
                  refine ⟨13408804685032485653905973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8939203123354990435937315 13408804685032485653905973)
                  ·
                    refine ⟨1257075439221795530053685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13408804685032485653905973 1257075439221795530053685)
                    ·
                      rfl

theorem cell23_7344437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_7344437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344437 prefixEnd_7344437 := by exact prefixLift 7344437
  have htrace : WordTrace (prefixWord ++ tailWord_7344437) baseStart_7344437 baseEnd_7344437 := by
    simpa [prefixWord, tailWord_7344437, baseEnd_7344437] using wordTrace_append hprefix tailTrace_7344437
  have hstable : (prefixWord ++ tailWord_7344437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344437).length < 2 ^ (prefixWord ++ tailWord_7344437).sum := by decide
  have hdescent : baseEnd_7344437 < baseStart_7344437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344502 : List Nat := [5, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7344502 : Nat := 118140960795 + 7344502 * 2 ^ 59
def prefixEnd_7344502 : Nat := 4983230072969 + 3 ^ 40 * 7344502 * 2
def baseEnd_7344502 : Nat := 3771259693907928835848257

theorem tailTrace_7344502 : CollatzResearch.WordTrace tailWord_7344502 prefixEnd_7344502 3771259693907928835848257 := by
  unfold tailWord_7344502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16742249677383191870219735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178583996558754046615677173 16742249677383191870219735)
  ·
    refine ⟨25113374516074787805329603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16742249677383191870219735 25113374516074787805329603)
    ·
      refine ⟨37670061774112181707994405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25113374516074787805329603 37670061774112181707994405)
      ·
        refine ⟨7063136582646034070248951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37670061774112181707994405 7063136582646034070248951)
        ·
          refine ⟨10594704873969051105373427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7063136582646034070248951 10594704873969051105373427)
          ·
            refine ⟨15892057310953576658060141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10594704873969051105373427 15892057310953576658060141)
            ·
              refine ⟨5959521491607591246772553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15892057310953576658060141 5959521491607591246772553)
              ·
                refine ⟨4469641118705693435079415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5959521491607591246772553 4469641118705693435079415)
                ·
                  refine ⟨6704461678058540152619123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4469641118705693435079415 6704461678058540152619123)
                  ·
                    refine ⟨10056692517087810228928685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6704461678058540152619123 10056692517087810228928685)
                    ·
                      refine ⟨3771259693907928835848257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10056692517087810228928685 3771259693907928835848257)
                      ·
                        rfl

theorem cell23_7344502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7344502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344502 prefixEnd_7344502 := by exact prefixLift 7344502
  have htrace : WordTrace (prefixWord ++ tailWord_7344502) baseStart_7344502 baseEnd_7344502 := by
    simpa [prefixWord, tailWord_7344502, baseEnd_7344502] using wordTrace_append hprefix tailTrace_7344502
  have hstable : (prefixWord ++ tailWord_7344502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344502).length < 2 ^ (prefixWord ++ tailWord_7344502).sum := by decide
  have hdescent : baseEnd_7344502 < baseStart_7344502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344517 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 2, 7, 2]
def baseStart_7344517 : Nat := 118140960795 + 7344517 * 2 ^ 59
def prefixEnd_7344517 : Nat := 4983230072969 + 3 ^ 40 * 7344517 * 2
def baseEnd_7344517 : Nat := 3771267396117746277160687

theorem tailTrace_7344517 : CollatzResearch.WordTrace tailWord_7344517 prefixEnd_7344517 3771267396117746277160687 := by
  unfold tailWord_7344517
  simp only [CollatzResearch.WordTrace]
  refine ⟨267876541933076727485311805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178584361288717818323541203 267876541933076727485311805)
  ·
    refine ⟨100453703224903772806991927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267876541933076727485311805 100453703224903772806991927)
    ·
      refine ⟨150680554837355659210487891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100453703224903772806991927 150680554837355659210487891)
      ·
        refine ⟨226020832256033488815731837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150680554837355659210487891 226020832256033488815731837)
        ·
          refine ⟨84757812096012558305899439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226020832256033488815731837 84757812096012558305899439)
          ·
            refine ⟨127136718144018837458849159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84757812096012558305899439 127136718144018837458849159)
            ·
              refine ⟨190705077216028256188273739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127136718144018837458849159 190705077216028256188273739)
              ·
                refine ⟨286057615824042384282410609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190705077216028256188273739 286057615824042384282410609)
                ·
                  refine ⟨214543211868031788211807957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286057615824042384282410609 214543211868031788211807957)
                  ·
                    refine ⟨5028356528156995036214249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 214543211868031788211807957 5028356528156995036214249)
                    ·
                      refine ⟨3771267396117746277160687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028356528156995036214249 3771267396117746277160687)
                      ·
                        rfl

theorem cell23_7344517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 7, 2].length) (baseStart_7344517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344517 prefixEnd_7344517 := by exact prefixLift 7344517
  have htrace : WordTrace (prefixWord ++ tailWord_7344517) baseStart_7344517 baseEnd_7344517 := by
    simpa [prefixWord, tailWord_7344517, baseEnd_7344517] using wordTrace_append hprefix tailTrace_7344517
  have hstable : (prefixWord ++ tailWord_7344517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344517).length < 2 ^ (prefixWord ++ tailWord_7344517).sum := by decide
  have hdescent : baseEnd_7344517 < baseStart_7344517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344567 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 3]
def baseStart_7344567 : Nat := 118140960795 + 7344567 * 2 ^ 59
def prefixEnd_7344567 : Nat := 4983230072969 + 3 ^ 40 * 7344567 * 2
def baseEnd_7344567 : Nat := 3771293070150471081535457

theorem tailTrace_7344567 : CollatzResearch.WordTrace tailWord_7344567 prefixEnd_7344567 3771293070150471081535457 := by
  unfold tailWord_7344567
  simp only [CollatzResearch.WordTrace]
  refine ⟨267878365582895586024631955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178585577055263724016421303 267878365582895586024631955)
  ·
    refine ⟨401817548374343379036947933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267878365582895586024631955 401817548374343379036947933)
    ·
      refine ⟨150681580640378767138855475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401817548374343379036947933 150681580640378767138855475)
      ·
        refine ⟨226022370960568150708283213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150681580640378767138855475 226022370960568150708283213)
        ·
          refine ⟨84758389110213056515606205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226022370960568150708283213 84758389110213056515606205)
          ·
            refine ⟨31784395916329896193352327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84758389110213056515606205 31784395916329896193352327)
            ·
              refine ⟨47676593874494844290028491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31784395916329896193352327 47676593874494844290028491)
              ·
                refine ⟨71514890811742266435042737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47676593874494844290028491 71514890811742266435042737)
                ·
                  refine ⟨53636168108806699826282053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71514890811742266435042737 53636168108806699826282053)
                  ·
                    refine ⟨10056781520401256217427885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53636168108806699826282053 10056781520401256217427885)
                    ·
                      refine ⟨3771293070150471081535457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10056781520401256217427885 3771293070150471081535457)
                      ·
                        rfl

theorem cell23_7344567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_7344567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344567 prefixEnd_7344567 := by exact prefixLift 7344567
  have htrace : WordTrace (prefixWord ++ tailWord_7344567) baseStart_7344567 baseEnd_7344567 := by
    simpa [prefixWord, tailWord_7344567, baseEnd_7344567] using wordTrace_append hprefix tailTrace_7344567
  have hstable : (prefixWord ++ tailWord_7344567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344567).length < 2 ^ (prefixWord ++ tailWord_7344567).sum := by decide
  have hdescent : baseEnd_7344567 < baseStart_7344567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344570 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 11]
def baseStart_7344570 : Nat := 118140960795 + 7344570 * 2 ^ 59
def prefixEnd_7344570 : Nat := 4983230072969 + 3 ^ 40 * 7344570 * 2
def baseEnd_7344570 : Nat := 419032734510270507755327

theorem tailTrace_7344570 : CollatzResearch.WordTrace tailWord_7344570 prefixEnd_7344570 419032734510270507755327 := by
  unfold tailWord_7344570
  simp only [CollatzResearch.WordTrace]
  refine ⟨66969618750471179384247791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178585650001256478357994109 66969618750471179384247791)
  ·
    refine ⟨100454428125706769076371687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66969618750471179384247791 100454428125706769076371687)
    ·
      refine ⟨150681642188560153614557531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100454428125706769076371687 150681642188560153614557531)
      ·
        refine ⟨226022463282840230421836297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150681642188560153614557531 226022463282840230421836297)
        ·
          refine ⟨169516847462130172816377223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226022463282840230421836297 169516847462130172816377223)
          ·
            refine ⟨254275271193195259224565835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169516847462130172816377223 254275271193195259224565835)
            ·
              refine ⟨381412906789792888836848753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254275271193195259224565835 381412906789792888836848753)
              ·
                refine ⟨286059680092344666627636565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381412906789792888836848753 286059680092344666627636565)
                ·
                  refine ⟨419032734510270507755327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 286059680092344666627636565 419032734510270507755327)
                  ·
                    rfl

theorem cell23_7344570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_7344570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344570 prefixEnd_7344570 := by exact prefixLift 7344570
  have htrace : WordTrace (prefixWord ++ tailWord_7344570) baseStart_7344570 baseEnd_7344570 := by
    simpa [prefixWord, tailWord_7344570, baseEnd_7344570] using wordTrace_append hprefix tailTrace_7344570
  have hstable : (prefixWord ++ tailWord_7344570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344570).length < 2 ^ (prefixWord ++ tailWord_7344570).sum := by decide
  have hdescent : baseEnd_7344570 < baseStart_7344570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344598 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_7344598 : Nat := 118140960795 + 7344598 * 2 ^ 59
def prefixEnd_7344598 : Nat := 4983230072969 + 3 ^ 40 * 7344598 * 2
def baseEnd_7344598 : Nat := 3771308988050760460247815

theorem tailTrace_7344598 : CollatzResearch.WordTrace tailWord_7344598 prefixEnd_7344598 3771308988050760460247815 := by
  unfold tailWord_7344598
  simp only [CollatzResearch.WordTrace]
  refine ⟨16742468515361454894938153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178586330830522185546006965 16742468515361454894938153)
  ·
    refine ⟨12556851386521091171203615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16742468515361454894938153 12556851386521091171203615)
    ·
      refine ⟨18835277079781636756805423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12556851386521091171203615 18835277079781636756805423)
      ·
        refine ⟨28252915619672455135208135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18835277079781636756805423 28252915619672455135208135)
        ·
          refine ⟨42379373429508682702812203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28252915619672455135208135 42379373429508682702812203)
          ·
            refine ⟨63569060144263024054218305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42379373429508682702812203 63569060144263024054218305)
            ·
              refine ⟨47676795108197268040663729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63569060144263024054218305 47676795108197268040663729)
              ·
                refine ⟨35757596331147951030497797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47676795108197268040663729 35757596331147951030497797)
                ·
                  refine ⟨6704549312090240818218337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35757596331147951030497797 6704549312090240818218337)
                  ·
                    refine ⟨5028411984067680613663753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6704549312090240818218337 5028411984067680613663753)
                    ·
                      refine ⟨3771308988050760460247815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028411984067680613663753 3771308988050760460247815)
                      ·
                        rfl

theorem cell23_7344598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_7344598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344598 prefixEnd_7344598 := by exact prefixLift 7344598
  have htrace : WordTrace (prefixWord ++ tailWord_7344598) baseStart_7344598 baseEnd_7344598 := by
    simpa [prefixWord, tailWord_7344598, baseEnd_7344598] using wordTrace_append hprefix tailTrace_7344598
  have hstable : (prefixWord ++ tailWord_7344598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344598).length < 2 ^ (prefixWord ++ tailWord_7344598).sum := by decide
  have hdescent : baseEnd_7344598 < baseStart_7344598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344621 : List Nat := [1, 5, 1, 3, 1, 1, 2, 4, 5]
def baseStart_7344621 : Nat := 118140960795 + 7344621 * 2 ^ 59
def prefixEnd_7344621 : Nat := 4983230072969 + 3 ^ 40 * 7344621 * 2
def baseEnd_7344621 : Nat := 419035644233979318917801

theorem tailTrace_7344621 : CollatzResearch.WordTrace tailWord_7344621 prefixEnd_7344621 419035644233979318917801 := by
  unfold tailWord_7344621
  simp only [CollatzResearch.WordTrace]
  refine ⟨267880335124699953247097717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178586890083133302164731811 267880335124699953247097717)
  ·
    refine ⟨25113781417940620616915411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267880335124699953247097717 25113781417940620616915411)
    ·
      refine ⟨37670672126910930925373117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25113781417940620616915411 37670672126910930925373117)
      ·
        refine ⟨14126502047591599097014919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37670672126910930925373117 14126502047591599097014919)
        ·
          refine ⟨21189753071387398645522379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14126502047591599097014919 21189753071387398645522379)
          ·
            refine ⟨31784629607081097968283569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21189753071387398645522379 31784629607081097968283569)
            ·
              refine ⟨23838472205310823476212677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31784629607081097968283569 23838472205310823476212677)
              ·
                refine ⟨4469713538495779401789877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23838472205310823476212677 4469713538495779401789877)
                ·
                  refine ⟨419035644233979318917801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4469713538495779401789877 419035644233979318917801)
                  ·
                    rfl

theorem cell23_7344621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_7344621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344621 prefixEnd_7344621 := by exact prefixLift 7344621
  have htrace : WordTrace (prefixWord ++ tailWord_7344621) baseStart_7344621 baseEnd_7344621 := by
    simpa [prefixWord, tailWord_7344621, baseEnd_7344621] using wordTrace_append hprefix tailTrace_7344621
  have hstable : (prefixWord ++ tailWord_7344621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344621).length < 2 ^ (prefixWord ++ tailWord_7344621).sum := by decide
  have hdescent : baseEnd_7344621 < baseStart_7344621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344637 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_7344637 : Nat := 118140960795 + 7344637 * 2 ^ 59
def prefixEnd_7344637 : Nat := 4983230072969 + 3 ^ 40 * 7344637 * 2
def baseEnd_7344637 : Nat := 3771329013796285807660135

theorem tailTrace_7344637 : CollatzResearch.WordTrace tailWord_7344637 prefixEnd_7344637 3771329013796285807660135 := by
  unfold tailWord_7344637
  simp only [CollatzResearch.WordTrace]
  refine ⟨267880918692641987979680165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178587279128427991986453443 267880918692641987979680165)
  ·
    refine ⟨50227672254870372746190031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267880918692641987979680165 50227672254870372746190031)
    ·
      refine ⟨75341508382305559119285047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50227672254870372746190031 75341508382305559119285047)
      ·
        refine ⟨113012262573458338678927571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75341508382305559119285047 113012262573458338678927571)
        ·
          refine ⟨169518393860187508018391357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113012262573458338678927571 169518393860187508018391357)
          ·
            refine ⟨63569397697570315506896759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169518393860187508018391357 63569397697570315506896759)
            ·
              refine ⟨95354096546355473260345139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63569397697570315506896759 95354096546355473260345139)
              ·
                refine ⟨143031144819533209890517709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95354096546355473260345139 143031144819533209890517709)
                ·
                  refine ⟨53636679307324953708944141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143031144819533209890517709 53636679307324953708944141)
                  ·
                    refine ⟨20113754740246857640854053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53636679307324953708944141 20113754740246857640854053)
                    ·
                      refine ⟨3771329013796285807660135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20113754740246857640854053 3771329013796285807660135)
                      ·
                        rfl

theorem cell23_7344637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_7344637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344637 prefixEnd_7344637 := by exact prefixLift 7344637
  have htrace : WordTrace (prefixWord ++ tailWord_7344637) baseStart_7344637 baseEnd_7344637 := by
    simpa [prefixWord, tailWord_7344637, baseEnd_7344637] using wordTrace_append hprefix tailTrace_7344637
  have hstable : (prefixWord ++ tailWord_7344637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344637).length < 2 ^ (prefixWord ++ tailWord_7344637).sum := by decide
  have hdescent : baseEnd_7344637 < baseStart_7344637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344654 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7344654 : Nat := 118140960795 + 7344654 * 2 ^ 59
def prefixEnd_7344654 : Nat := 4983230072969 + 3 ^ 40 * 7344654 * 2
def baseEnd_7344654 : Nat := 3771337742967412241147557

theorem tailTrace_7344654 : CollatzResearch.WordTrace tailWord_7344654 prefixEnd_7344654 3771337742967412241147557 := by
  unfold tailWord_7344654
  simp only [CollatzResearch.WordTrace]
  refine ⟨33485192341697549985381127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178587692489053599922032677 33485192341697549985381127)
  ·
    refine ⟨50227788512546324978071691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33485192341697549985381127 50227788512546324978071691)
    ·
      refine ⟨75341682768819487467107537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50227788512546324978071691 75341682768819487467107537)
      ·
        refine ⟨56506262076614615600330653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75341682768819487467107537 56506262076614615600330653)
        ·
          refine ⟨21189848278730480850123995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56506262076614615600330653 21189848278730480850123995)
          ·
            refine ⟨31784772418095721275185993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21189848278730480850123995 31784772418095721275185993)
            ·
              refine ⟨23838579313571790956389495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31784772418095721275185993 23838579313571790956389495)
              ·
                refine ⟨35757868970357686434584243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23838579313571790956389495 35757868970357686434584243)
                ·
                  refine ⟨53636803455536529651876365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35757868970357686434584243 53636803455536529651876365)
                  ·
                    refine ⟨20113801295826198619453637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53636803455536529651876365 20113801295826198619453637)
                    ·
                      refine ⟨3771337742967412241147557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20113801295826198619453637 3771337742967412241147557)
                      ·
                        rfl

theorem cell23_7344654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7344654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344654 prefixEnd_7344654 := by exact prefixLift 7344654
  have htrace : WordTrace (prefixWord ++ tailWord_7344654) baseStart_7344654 baseEnd_7344654 := by
    simpa [prefixWord, tailWord_7344654, baseEnd_7344654] using wordTrace_append hprefix tailTrace_7344654
  have hstable : (prefixWord ++ tailWord_7344654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344654).length < 2 ^ (prefixWord ++ tailWord_7344654).sum := by decide
  have hdescent : baseEnd_7344654 < baseStart_7344654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344677 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 8]
def baseStart_7344677 : Nat := 118140960795 + 7344677 * 2 ^ 59
def prefixEnd_7344677 : Nat := 4983230072969 + 3 ^ 40 * 7344677 * 2
def baseEnd_7344677 : Nat := 419038839224718405684439

theorem tailTrace_7344677 : CollatzResearch.WordTrace tailWord_7344677 prefixEnd_7344677 419038839224718405684439 := by
  unfold tailWord_7344677
  simp only [CollatzResearch.WordTrace]
  refine ⟨267882377612497074811136285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178588251741664716540757523 267882377612497074811136285)
  ·
    refine ⟨100455891604686403054176107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267882377612497074811136285 100455891604686403054176107)
    ·
      refine ⟨150683837407029604581264161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100455891604686403054176107 150683837407029604581264161)
      ·
        refine ⟨113012878055272203435948121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150683837407029604581264161 113012878055272203435948121)
        ·
          refine ⟨84759658541454152576961091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113012878055272203435948121 84759658541454152576961091)
          ·
            refine ⟨127139487812181228865441637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84759658541454152576961091 127139487812181228865441637)
            ·
              refine ⟨23838653964783980412270307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127139487812181228865441637 23838653964783980412270307)
              ·
                refine ⟨35757980947175970618405461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23838653964783980412270307 35757980947175970618405461)
                ·
                  refine ⟨419038839224718405684439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35757980947175970618405461 419038839224718405684439)
                  ·
                    rfl

theorem cell23_7344677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_7344677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344677 prefixEnd_7344677 := by exact prefixLift 7344677
  have htrace : WordTrace (prefixWord ++ tailWord_7344677) baseStart_7344677 baseEnd_7344677 := by
    simpa [prefixWord, tailWord_7344677, baseEnd_7344677] using wordTrace_append hprefix tailTrace_7344677
  have hstable : (prefixWord ++ tailWord_7344677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344677).length < 2 ^ (prefixWord ++ tailWord_7344677).sum := by decide
  have hdescent : baseEnd_7344677 < baseStart_7344677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344732 : List Nat := [2, 2, 4, 1, 3, 2, 2, 2, 1, 4]
def baseStart_7344732 : Nat := 118140960795 + 7344732 * 2 ^ 59
def prefixEnd_7344732 : Nat := 4983230072969 + 3 ^ 40 * 7344732 * 2
def baseEnd_7344732 : Nat := 1257125931486154311990733

theorem tailTrace_7344732 : CollatzResearch.WordTrace tailWord_7344732 prefixEnd_7344732 1257125931486154311990733 := by
  unfold tailWord_7344732
  simp only [CollatzResearch.WordTrace]
  refine ⟨133942191813648909602194225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178589589084865212802925633 133942191813648909602194225)
  ·
    refine ⟨100456643860236682201645669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133942191813648909602194225 100456643860236682201645669)
    ·
      refine ⟨18835620723794377912808563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100456643860236682201645669 18835620723794377912808563)
      ·
        refine ⟨28253431085691566869212845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18835620723794377912808563 28253431085691566869212845)
        ·
          refine ⟨10595036657134337575954817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28253431085691566869212845 10595036657134337575954817)
          ·
            refine ⟨7946277492850753181966113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10595036657134337575954817 7946277492850753181966113)
            ·
              refine ⟨5959708119638064886474585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7946277492850753181966113 5959708119638064886474585)
              ·
                refine ⟨4469781089728548664855939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5959708119638064886474585 4469781089728548664855939)
                ·
                  refine ⟨6704671634592822997283909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4469781089728548664855939 6704671634592822997283909)
                  ·
                    refine ⟨1257125931486154311990733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6704671634592822997283909 1257125931486154311990733)
                    ·
                      rfl

theorem cell23_7344732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_7344732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344732 prefixEnd_7344732 := by exact prefixLift 7344732
  have htrace : WordTrace (prefixWord ++ tailWord_7344732) baseStart_7344732 baseEnd_7344732 := by
    simpa [prefixWord, tailWord_7344732, baseEnd_7344732] using wordTrace_append hprefix tailTrace_7344732
  have hstable : (prefixWord ++ tailWord_7344732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344732).length < 2 ^ (prefixWord ++ tailWord_7344732).sum := by decide
  have hdescent : baseEnd_7344732 < baseStart_7344732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344765 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 2, 3, 2]
def baseStart_7344765 : Nat := 118140960795 + 7344765 * 2 ^ 59
def prefixEnd_7344765 : Nat := 4983230072969 + 3 ^ 40 * 7344765 * 2
def baseEnd_7344765 : Nat := 3771394739320061306859547

theorem tailTrace_7344765 : CollatzResearch.WordTrace tailWord_7344765 prefixEnd_7344765 3771394739320061306859547 := by
  unfold tailWord_7344765
  simp only [CollatzResearch.WordTrace]
  refine ⟨267885587236178265840339749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178590391490785510560226499 267885587236178265840339749)
  ·
    refine ⟨50228547606783424845063703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267885587236178265840339749 50228547606783424845063703)
    ·
      refine ⟨75342821410175137267595555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50228547606783424845063703 75342821410175137267595555)
      ·
        refine ⟨113014232115262705901393333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75342821410175137267595555 113014232115262705901393333)
        ·
          refine ⟨10595084260805878678255625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113014232115262705901393333 10595084260805878678255625)
          ·
            refine ⟨7946313195604409008691719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10595084260805878678255625 7946313195604409008691719)
            ·
              refine ⟨11919469793406613513037579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7946313195604409008691719 11919469793406613513037579)
              ·
                refine ⟨17879204690109920269556369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11919469793406613513037579 17879204690109920269556369)
                ·
                  refine ⟨13409403517582440202167277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17879204690109920269556369 13409403517582440202167277)
                  ·
                    refine ⟨5028526319093415075812729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13409403517582440202167277 5028526319093415075812729)
                    ·
                      refine ⟨3771394739320061306859547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028526319093415075812729 3771394739320061306859547)
                      ·
                        rfl

theorem cell23_7344765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_7344765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344765 prefixEnd_7344765 := by exact prefixLift 7344765
  have htrace : WordTrace (prefixWord ++ tailWord_7344765) baseStart_7344765 baseEnd_7344765 := by
    simpa [prefixWord, tailWord_7344765, baseEnd_7344765] using wordTrace_append hprefix tailTrace_7344765
  have hstable : (prefixWord ++ tailWord_7344765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344765).length < 2 ^ (prefixWord ++ tailWord_7344765).sum := by decide
  have hdescent : baseEnd_7344765 < baseStart_7344765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344778 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_7344778 : Nat := 118140960795 + 7344778 * 2 ^ 59
def prefixEnd_7344778 : Nat := 4983230072969 + 3 ^ 40 * 7344778 * 2
def baseEnd_7344778 : Nat := 3771401414568569755996987

theorem tailTrace_7344778 : CollatzResearch.WordTrace tailWord_7344778 prefixEnd_7344778 3771401414568569755996987 := by
  unfold tailWord_7344778
  simp only [CollatzResearch.WordTrace]
  refine ⟨66971515346282792265140747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178590707590087446040375325 66971515346282792265140747)
  ·
    refine ⟨100457273019424188397711121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66971515346282792265140747 100457273019424188397711121)
    ·
      refine ⟨75342954764568141298283341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100457273019424188397711121 75342954764568141298283341)
      ·
        refine ⟨28253608036713052986856253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75342954764568141298283341 28253608036713052986856253)
        ·
          refine ⟨10595103013767394870071095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28253608036713052986856253 10595103013767394870071095)
          ·
            refine ⟨15892654520651092305106643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10595103013767394870071095 15892654520651092305106643)
            ·
              refine ⟨23838981780976638457659965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15892654520651092305106643 23838981780976638457659965)
              ·
                refine ⟨8939618167866239421622487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23838981780976638457659965 8939618167866239421622487)
                ·
                  refine ⟨13409427251799359132433731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8939618167866239421622487 13409427251799359132433731)
                  ·
                    refine ⟨20114140877699038698650597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13409427251799359132433731 20114140877699038698650597)
                    ·
                      refine ⟨3771401414568569755996987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20114140877699038698650597 3771401414568569755996987)
                      ·
                        rfl

theorem cell23_7344778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_7344778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344778 prefixEnd_7344778 := by exact prefixLift 7344778
  have htrace : WordTrace (prefixWord ++ tailWord_7344778) baseStart_7344778 baseEnd_7344778 := by
    simpa [prefixWord, tailWord_7344778, baseEnd_7344778] using wordTrace_append hprefix tailTrace_7344778
  have hstable : (prefixWord ++ tailWord_7344778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344778).length < 2 ^ (prefixWord ++ tailWord_7344778).sum := by decide
  have hdescent : baseEnd_7344778 < baseStart_7344778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344788 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_7344788 : Nat := 118140960795 + 7344788 * 2 ^ 59
def prefixEnd_7344788 : Nat := 4983230072969 + 3 ^ 40 * 7344788 * 2
def baseEnd_7344788 : Nat := 1257135516458371572290647

theorem tailTrace_7344788 : CollatzResearch.WordTrace tailWord_7344788 prefixEnd_7344788 1257135516458371572290647 := by
  unfold tailWord_7344788
  simp only [CollatzResearch.WordTrace]
  refine ⟨133943213057547470384213509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178590950743396627178951345 133943213057547470384213509)
  ·
    refine ⟨25114352448290150697040033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133943213057547470384213509 25114352448290150697040033)
    ·
      refine ⟨18835764336217613022780025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25114352448290150697040033 18835764336217613022780025)
      ·
        refine ⟨14126823252163209767085019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18835764336217613022780025 14126823252163209767085019)
        ·
          refine ⟨21190234878244814650627529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14126823252163209767085019 21190234878244814650627529)
          ·
            refine ⟨15892676158683610987970647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21190234878244814650627529 15892676158683610987970647)
            ·
              refine ⟨23839014238025416481955971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15892676158683610987970647 23839014238025416481955971)
              ·
                refine ⟨35758521357038124722933957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23839014238025416481955971 35758521357038124722933957)
                ·
                  refine ⟨6704722754444648385550117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35758521357038124722933957 6704722754444648385550117)
                  ·
                    refine ⟨1257135516458371572290647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6704722754444648385550117 1257135516458371572290647)
                    ·
                      rfl

theorem cell23_7344788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_7344788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344788 prefixEnd_7344788 := by exact prefixLift 7344788
  have htrace : WordTrace (prefixWord ++ tailWord_7344788) baseStart_7344788 baseEnd_7344788 := by
    simpa [prefixWord, tailWord_7344788, baseEnd_7344788] using wordTrace_append hprefix tailTrace_7344788
  have hstable : (prefixWord ++ tailWord_7344788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344788).length < 2 ^ (prefixWord ++ tailWord_7344788).sum := by decide
  have hdescent : baseEnd_7344788 < baseStart_7344788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344864 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 4]
def baseStart_7344864 : Nat := 118140960795 + 7344864 * 2 ^ 59
def prefixEnd_7344864 : Nat := 4983230072969 + 3 ^ 40 * 7344864 * 2
def baseEnd_7344864 : Nat := 3771445573904856419521591

theorem tailTrace_7344864 : CollatzResearch.WordTrace tailWord_7344864 prefixEnd_7344864 3771445573904856419521591 := by
  unfold tailWord_7344864
  simp only [CollatzResearch.WordTrace]
  refine ⟨133944599031409802874096823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178592798708546403832129097 133944599031409802874096823)
  ·
    refine ⟨200916898547114704311145235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133944599031409802874096823 200916898547114704311145235)
    ·
      refine ⟨301375347820672056466717853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200916898547114704311145235 301375347820672056466717853)
      ·
        refine ⟨113015755432752021175019195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301375347820672056466717853 113015755432752021175019195)
        ·
          refine ⟨169523633149128031762528793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113015755432752021175019195 169523633149128031762528793)
          ·
            refine ⟨127142724861846023821896595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169523633149128031762528793 127142724861846023821896595)
            ·
              refine ⟨190714087292769035732844893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127142724861846023821896595 190714087292769035732844893)
              ·
                refine ⟨71517782734788388399816835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190714087292769035732844893 71517782734788388399816835)
                ·
                  refine ⟨107276674102182582599725253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71517782734788388399816835 107276674102182582599725253)
                  ·
                    refine ⟨20114376394159234237448485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107276674102182582599725253 20114376394159234237448485)
                    ·
                      refine ⟨3771445573904856419521591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20114376394159234237448485 3771445573904856419521591)
                      ·
                        rfl

theorem cell23_7344864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_7344864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344864 prefixEnd_7344864 := by exact prefixLift 7344864
  have htrace : WordTrace (prefixWord ++ tailWord_7344864) baseStart_7344864 baseEnd_7344864 := by
    simpa [prefixWord, tailWord_7344864, baseEnd_7344864] using wordTrace_append hprefix tailTrace_7344864
  have hstable : (prefixWord ++ tailWord_7344864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344864).length < 2 ^ (prefixWord ++ tailWord_7344864).sum := by decide
  have hdescent : baseEnd_7344864 < baseStart_7344864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344872 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_7344872 : Nat := 118140960795 + 7344872 * 2 ^ 59
def prefixEnd_7344872 : Nat := 4983230072969 + 3 ^ 40 * 7344872 * 2
def baseEnd_7344872 : Nat := 3771449681750092388221555

theorem tailTrace_7344872 : CollatzResearch.WordTrace tailWord_7344872 prefixEnd_7344872 3771449681750092388221555 := by
  unfold tailWord_7344872
  simp only [CollatzResearch.WordTrace]
  refine ⟨133944744923395311557242435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178592993231193748742989913 133944744923395311557242435)
  ·
    refine ⟨200917117385092967335863653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133944744923395311557242435 200917117385092967335863653)
    ·
      refine ⟨37671959509704931375474435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200917117385092967335863653 37671959509704931375474435)
      ·
        refine ⟨56507939264557397063211653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37671959509704931375474435 56507939264557397063211653)
        ·
          refine ⟨10595238612104511949352185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56507939264557397063211653 10595238612104511949352185)
          ·
            refine ⟨7946428959078383962014139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10595238612104511949352185 7946428959078383962014139)
            ·
              refine ⟨11919643438617575943021209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7946428959078383962014139 11919643438617575943021209)
              ·
                refine ⟨8939732578963181957265907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11919643438617575943021209 8939732578963181957265907)
                ·
                  refine ⟨13409598868444772935898861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8939732578963181957265907 13409598868444772935898861)
                  ·
                    refine ⟨5028599575666789850962073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13409598868444772935898861 5028599575666789850962073)
                    ·
                      refine ⟨3771449681750092388221555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028599575666789850962073 3771449681750092388221555)
                      ·
                        rfl

theorem cell23_7344872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_7344872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344872 prefixEnd_7344872 := by exact prefixLift 7344872
  have htrace : WordTrace (prefixWord ++ tailWord_7344872) baseStart_7344872 baseEnd_7344872 := by
    simpa [prefixWord, tailWord_7344872, baseEnd_7344872] using wordTrace_append hprefix tailTrace_7344872
  have hstable : (prefixWord ++ tailWord_7344872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344872).length < 2 ^ (prefixWord ++ tailWord_7344872).sum := by decide
  have hdescent : baseEnd_7344872 < baseStart_7344872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344874 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 9]
def baseStart_7344874 : Nat := 118140960795 + 7344874 * 2 ^ 59
def prefixEnd_7344874 : Nat := 4983230072969 + 3 ^ 40 * 7344874 * 2
def baseEnd_7344874 : Nat := 419050078745711264488505

theorem tailTrace_7344874 : CollatzResearch.WordTrace tailWord_7344874 prefixEnd_7344874 419050078745711264488505 := by
  unfold tailWord_7344874
  simp only [CollatzResearch.WordTrace]
  refine ⟨66972390698195844364014419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178593041861855584970705117 66972390698195844364014419)
  ·
    refine ⟨100458586047293766546021629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66972390698195844364014419 100458586047293766546021629)
    ·
      refine ⟨37671969767735162454758111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100458586047293766546021629 37671969767735162454758111)
      ·
        refine ⟨56507954651602743682137167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37671969767735162454758111 56507954651602743682137167)
        ·
          refine ⟨84761931977404115523205751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56507954651602743682137167 84761931977404115523205751)
          ·
            refine ⟨127142897966106173284808627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84761931977404115523205751 127142897966106173284808627)
            ·
              refine ⟨190714346949159259927212941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127142897966106173284808627 190714346949159259927212941)
              ·
                refine ⟨71517880105934722472704853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190714346949159259927212941 71517880105934722472704853)
                ·
                  refine ⟨419050078745711264488505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71517880105934722472704853 419050078745711264488505)
                  ·
                    rfl

theorem cell23_7344874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_7344874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344874 prefixEnd_7344874 := by exact prefixLift 7344874
  have htrace : WordTrace (prefixWord ++ tailWord_7344874) baseStart_7344874 baseEnd_7344874 := by
    simpa [prefixWord, tailWord_7344874, baseEnd_7344874] using wordTrace_append hprefix tailTrace_7344874
  have hstable : (prefixWord ++ tailWord_7344874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344874).length < 2 ^ (prefixWord ++ tailWord_7344874).sum := by decide
  have hdescent : baseEnd_7344874 < baseStart_7344874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344911 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 1, 7, 2]
def baseStart_7344911 : Nat := 118140960795 + 7344911 * 2 ^ 59
def prefixEnd_7344911 : Nat := 4983230072969 + 3 ^ 40 * 7344911 * 2
def baseEnd_7344911 : Nat := 3771469707495617735633875

theorem tailTrace_7344911 : CollatzResearch.WordTrace tailWord_7344911 prefixEnd_7344911 3771469707495617735633875 := by
  unfold tailWord_7344911
  simp only [CollatzResearch.WordTrace]
  refine ⟨267890912293649332775154587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178593941529099555183436391 267890912293649332775154587)
  ·
    refine ⟨401836368440473999162731881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267890912293649332775154587 401836368440473999162731881)
    ·
      refine ⟨301377276330355499372048911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401836368440473999162731881 301377276330355499372048911)
      ·
        refine ⟨452065914495533249058073367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301377276330355499372048911 452065914495533249058073367)
        ·
          refine ⟨678098871743299873587110051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452065914495533249058073367 678098871743299873587110051)
          ·
            refine ⟨1017148307614949810380665077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678098871743299873587110051 1017148307614949810380665077)
            ·
              refine ⟨95357653838901544723187351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1017148307614949810380665077 95357653838901544723187351)
              ·
                refine ⟨143036480758352317084781027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95357653838901544723187351 143036480758352317084781027)
                ·
                  refine ⟨214554721137528475627171541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143036480758352317084781027 214554721137528475627171541)
                  ·
                    refine ⟨5028626276660823647511833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 214554721137528475627171541 5028626276660823647511833)
                    ·
                      refine ⟨3771469707495617735633875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028626276660823647511833 3771469707495617735633875)
                      ·
                        rfl

theorem cell23_7344911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 7, 2].length) (baseStart_7344911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344911 prefixEnd_7344911 := by exact prefixLift 7344911
  have htrace : WordTrace (prefixWord ++ tailWord_7344911) baseStart_7344911 baseEnd_7344911 := by
    simpa [prefixWord, tailWord_7344911, baseEnd_7344911] using wordTrace_append hprefix tailTrace_7344911
  have hstable : (prefixWord ++ tailWord_7344911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344911).length < 2 ^ (prefixWord ++ tailWord_7344911).sum := by decide
  have hdescent : baseEnd_7344911 < baseStart_7344911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344951 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 5, 4]
def baseStart_7344951 : Nat := 118140960795 + 7344951 * 2 ^ 59
def prefixEnd_7344951 : Nat := 4983230072969 + 3 ^ 40 * 7344951 * 2
def baseEnd_7344951 : Nat := 1257163415573932526377897

theorem tailTrace_7344951 : CollatzResearch.WordTrace tailWord_7344951 prefixEnd_7344951 1257163415573932526377897 := by
  unfold tailWord_7344951
  simp only [CollatzResearch.WordTrace]
  refine ⟨267892371213504419606610707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178594914142336279737740471 267892371213504419606610707)
  ·
    refine ⟨401838556820256629409916061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267892371213504419606610707 401838556820256629409916061)
    ·
      refine ⟨150689458807596236028718523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401838556820256629409916061 150689458807596236028718523)
      ·
        refine ⟨226034188211394354043077785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150689458807596236028718523 226034188211394354043077785)
        ·
          refine ⟨169525641158545765532308339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226034188211394354043077785 169525641158545765532308339)
          ·
            refine ⟨254288461737818648298462509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169525641158545765532308339 254288461737818648298462509)
            ·
              refine ⟨95358173151681993111923441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254288461737818648298462509 95358173151681993111923441)
              ·
                refine ⟨71518629863761494833942581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95358173151681993111923441 71518629863761494833942581)
                ·
                  refine ⟨6704871549727640140682117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71518629863761494833942581 6704871549727640140682117)
                  ·
                    refine ⟨1257163415573932526377897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6704871549727640140682117 1257163415573932526377897)
                    ·
                      rfl

theorem cell23_7344951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_7344951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344951 prefixEnd_7344951 := by exact prefixLift 7344951
  have htrace : WordTrace (prefixWord ++ tailWord_7344951) baseStart_7344951 baseEnd_7344951 := by
    simpa [prefixWord, tailWord_7344951, baseEnd_7344951] using wordTrace_append hprefix tailTrace_7344951
  have hstable : (prefixWord ++ tailWord_7344951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344951).length < 2 ^ (prefixWord ++ tailWord_7344951).sum := by decide
  have hdescent : baseEnd_7344951 < baseStart_7344951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344968 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 3, 4]
def baseStart_7344968 : Nat := 118140960795 + 7344968 * 2 ^ 59
def prefixEnd_7344968 : Nat := 4983230072969 + 3 ^ 40 * 7344968 * 2
def baseEnd_7344968 : Nat := 1257166325297641337540371

theorem tailTrace_7344968 : CollatzResearch.WordTrace tailWord_7344968 prefixEnd_7344968 1257166325297641337540371 := by
  unfold tailWord_7344968
  simp only [CollatzResearch.WordTrace]
  refine ⟨133946495627221415754989779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178595327502961887673319705 133946495627221415754989779)
  ·
    refine ⟨200919743440832123632484669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133946495627221415754989779 200919743440832123632484669)
    ·
      refine ⟨75344903790312046362181751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200919743440832123632484669 75344903790312046362181751)
      ·
        refine ⟨113017355685468069543272627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75344903790312046362181751 113017355685468069543272627)
        ·
          refine ⟨169526033528202104314908941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113017355685468069543272627 169526033528202104314908941)
          ·
            refine ⟨63572262573075789118090853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169526033528202104314908941 63572262573075789118090853)
            ·
              refine ⟨11919799232451710459642035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63572262573075789118090853 11919799232451710459642035)
              ·
                refine ⟨17879698848677565689463053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11919799232451710459642035 17879698848677565689463053)
                ·
                  refine ⟨6704887068254087133548645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17879698848677565689463053 6704887068254087133548645)
                  ·
                    refine ⟨1257166325297641337540371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6704887068254087133548645 1257166325297641337540371)
                    ·
                      rfl

theorem cell23_7344968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_7344968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344968 prefixEnd_7344968 := by exact prefixLift 7344968
  have htrace : WordTrace (prefixWord ++ tailWord_7344968) baseStart_7344968 baseEnd_7344968 := by
    simpa [prefixWord, tailWord_7344968, baseEnd_7344968] using wordTrace_append hprefix tailTrace_7344968
  have hstable : (prefixWord ++ tailWord_7344968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344968).length < 2 ^ (prefixWord ++ tailWord_7344968).sum := by decide
  have hdescent : baseEnd_7344968 < baseStart_7344968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7344991 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 3]
def baseStart_7344991 : Nat := 118140960795 + 7344991 * 2 ^ 59
def prefixEnd_7344991 : Nat := 4983230072969 + 3 ^ 40 * 7344991 * 2
def baseEnd_7344991 : Nat := 3771510785947977422633507

theorem tailTrace_7344991 : CollatzResearch.WordTrace tailWord_7344991 prefixEnd_7344991 3771510785947977422633507 := by
  unfold tailWord_7344991
  simp only [CollatzResearch.WordTrace]
  refine ⟨267893830133359506438066827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178595886755573004292044551 267893830133359506438066827)
  ·
    refine ⟨401840745200039259657100241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267893830133359506438066827 401840745200039259657100241)
    ·
      refine ⟨301380558900029444742825181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401840745200039259657100241 301380558900029444742825181)
      ·
        refine ⟨113017709587511041778559443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301380558900029444742825181 113017709587511041778559443)
        ·
          refine ⟨169526564381266562667839165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113017709587511041778559443 169526564381266562667839165)
          ·
            refine ⟨63572461642974961000439687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169526564381266562667839165 63572461642974961000439687)
            ·
              refine ⟨95358692464462441500659531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63572461642974961000439687 95358692464462441500659531)
              ·
                refine ⟨143038038696693662250989297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95358692464462441500659531 143038038696693662250989297)
                ·
                  refine ⟨107278529022520246688241973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143038038696693662250989297 107278529022520246688241973)
                  ·
                    refine ⟨10057362095861273127022685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107278529022520246688241973 10057362095861273127022685)
                    ·
                      refine ⟨3771510785947977422633507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10057362095861273127022685 3771510785947977422633507)
                      ·
                        rfl

theorem cell23_7344991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_7344991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7344991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7344991 prefixEnd_7344991 := by exact prefixLift 7344991
  have htrace : WordTrace (prefixWord ++ tailWord_7344991) baseStart_7344991 baseEnd_7344991 := by
    simpa [prefixWord, tailWord_7344991, baseEnd_7344991] using wordTrace_append hprefix tailTrace_7344991
  have hstable : (prefixWord ++ tailWord_7344991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7344991).length < 2 ^ (prefixWord ++ tailWord_7344991).sum := by decide
  have hdescent : baseEnd_7344991 < baseStart_7344991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7344991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345008 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 5, 1, 3]
def baseStart_7345008 : Nat := 118140960795 + 7345008 * 2 ^ 59
def prefixEnd_7345008 : Nat := 4983230072969 + 3 ^ 40 * 7345008 * 2
def baseEnd_7345008 : Nat := 3771519515119103856120929

theorem tailTrace_7345008 : CollatzResearch.WordTrace tailWord_7345008 prefixEnd_7345008 3771519515119103856120929 := by
  unfold tailWord_7345008
  simp only [CollatzResearch.WordTrace]
  refine ⟨133947225087148959170717839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178596300116198612227623785 133947225087148959170717839)
  ·
    refine ⟨200920837630723438756076759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133947225087148959170717839 200920837630723438756076759)
    ·
      refine ⟨301381256446085158134115139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200920837630723438756076759 301381256446085158134115139)
      ·
        refine ⟨452071884669127737201172709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301381256446085158134115139 452071884669127737201172709)
        ·
          refine ⟨84763478375461450725219883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 452071884669127737201172709 84763478375461450725219883)
          ·
            refine ⟨127145217563192176087829825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84763478375461450725219883 127145217563192176087829825)
            ·
              refine ⟨95358913172394132065872369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127145217563192176087829825 95358913172394132065872369)
              ·
                refine ⟨71519184879295599049404277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95358913172394132065872369 71519184879295599049404277)
                ·
                  refine ⟨6704923582433962410881651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71519184879295599049404277 6704923582433962410881651)
                  ·
                    refine ⟨10057385373650943616322477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6704923582433962410881651 10057385373650943616322477)
                    ·
                      refine ⟨3771519515119103856120929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10057385373650943616322477 3771519515119103856120929)
                      ·
                        rfl

theorem cell23_7345008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5, 1, 3].length) (baseStart_7345008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345008 prefixEnd_7345008 := by exact prefixLift 7345008
  have htrace : WordTrace (prefixWord ++ tailWord_7345008) baseStart_7345008 baseEnd_7345008 := by
    simpa [prefixWord, tailWord_7345008, baseEnd_7345008] using wordTrace_append hprefix tailTrace_7345008
  have hstable : (prefixWord ++ tailWord_7345008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345008).length < 2 ^ (prefixWord ++ tailWord_7345008).sum := by decide
  have hdescent : baseEnd_7345008 < baseStart_7345008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345041 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 1, 6]
def baseStart_7345041 : Nat := 118140960795 + 7345041 * 2 ^ 59
def prefixEnd_7345041 : Nat := 4983230072969 + 3 ^ 40 * 7345041 * 2
def baseEnd_7345041 : Nat := 1257178819993567409002759

theorem tailTrace_7345041 : CollatzResearch.WordTrace tailWord_7345041 prefixEnd_7345041 1257178819993567409002759 := by
  unfold tailWord_7345041
  simp only [CollatzResearch.WordTrace]
  refine ⟨267895653783178364977386977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178597102522118909984924651 267895653783178364977386977)
  ·
    refine ⟨200921740337383773733040233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267895653783178364977386977 200921740337383773733040233)
    ·
      refine ⟨150691305253037830299780175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200921740337383773733040233 150691305253037830299780175)
      ·
        refine ⟨226036957879556745449670263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150691305253037830299780175 226036957879556745449670263)
        ·
          refine ⟨339055436819335118174505395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226036957879556745449670263 339055436819335118174505395)
          ·
            refine ⟨508583155229002677261758093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339055436819335118174505395 508583155229002677261758093)
            ·
              refine ⟨190718683210876003973159285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508583155229002677261758093 190718683210876003973159285)
              ·
                refine ⟨17879876551019625372483683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190718683210876003973159285 17879876551019625372483683)
                ·
                  refine ⟨26819814826529438058725525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17879876551019625372483683 26819814826529438058725525)
                  ·
                    refine ⟨1257178819993567409002759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26819814826529438058725525 1257178819993567409002759)
                    ·
                      rfl

theorem cell23_7345041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_7345041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345041 prefixEnd_7345041 := by exact prefixLift 7345041
  have htrace : WordTrace (prefixWord ++ tailWord_7345041) baseStart_7345041 baseEnd_7345041 := by
    simpa [prefixWord, tailWord_7345041, baseEnd_7345041] using wordTrace_append hprefix tailTrace_7345041
  have hstable : (prefixWord ++ tailWord_7345041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345041).length < 2 ^ (prefixWord ++ tailWord_7345041).sum := by decide
  have hdescent : baseEnd_7345041 < baseStart_7345041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345045 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 1, 5]
def baseStart_7345045 : Nat := 118140960795 + 7345045 * 2 ^ 59
def prefixEnd_7345045 : Nat := 4983230072969 + 3 ^ 40 * 7345045 * 2
def baseEnd_7345045 : Nat := 1257179504634440070452753

theorem tailTrace_7345045 : CollatzResearch.WordTrace tailWord_7345045 prefixEnd_7345045 1257179504634440070452753 := by
  unfold tailWord_7345045
  simp only [CollatzResearch.WordTrace]
  refine ⟨267895799675163873660532589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178597199783442582440355059 267895799675163873660532589)
  ·
    refine ⟨100460924878186452622699721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267895799675163873660532589 100460924878186452622699721)
    ·
      refine ⟨75345693658639839467024791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100460924878186452622699721 75345693658639839467024791)
      ·
        refine ⟨113018540487959759200537187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75345693658639839467024791 113018540487959759200537187)
        ·
          refine ⟨169527810731939638800805781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113018540487959759200537187 169527810731939638800805781)
          ·
            refine ⟨7946616128059670568787771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169527810731939638800805781 7946616128059670568787771)
            ·
              refine ⟨11919924192089505853181657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7946616128059670568787771 11919924192089505853181657)
              ·
                refine ⟨8939943144067129389886243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11919924192089505853181657 8939943144067129389886243)
                ·
                  refine ⟨13409914716100694084829365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8939943144067129389886243 13409914716100694084829365)
                  ·
                    refine ⟨1257179504634440070452753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13409914716100694084829365 1257179504634440070452753)
                    ·
                      rfl

theorem cell23_7345045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_7345045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345045 prefixEnd_7345045 := by exact prefixLift 7345045
  have htrace : WordTrace (prefixWord ++ tailWord_7345045) baseStart_7345045 baseEnd_7345045 := by
    simpa [prefixWord, tailWord_7345045, baseEnd_7345045] using wordTrace_append hprefix tailTrace_7345045
  have hstable : (prefixWord ++ tailWord_7345045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345045).length < 2 ^ (prefixWord ++ tailWord_7345045).sum := by decide
  have hdescent : baseEnd_7345045 < baseStart_7345045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345058 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_7345058 : Nat := 118140960795 + 7345058 * 2 ^ 59
def prefixEnd_7345058 : Nat := 4983230072969 + 3 ^ 40 * 7345058 * 2
def baseEnd_7345058 : Nat := 1257181729717276220165233

theorem tailTrace_7345058 : CollatzResearch.WordTrace tailWord_7345058 prefixEnd_7345058 1257181729717276220165233 := by
  unfold tailWord_7345058
  simp only [CollatzResearch.WordTrace]
  refine ⟨66974068456029194220188957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178597515882744517920503885 66974068456029194220188957)
  ·
    refine ⟨25115275671010947832570859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66974068456029194220188957 25115275671010947832570859)
    ·
      refine ⟨37672913506516421748856289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25115275671010947832570859 37672913506516421748856289)
      ·
        refine ⟨28254685129887316311642217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37672913506516421748856289 28254685129887316311642217)
        ·
          refine ⟨21191013847415487233731663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28254685129887316311642217 21191013847415487233731663)
          ·
            refine ⟨31786520771123230850597495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21191013847415487233731663 31786520771123230850597495)
            ·
              refine ⟨47679781156684846275896243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31786520771123230850597495 47679781156684846275896243)
              ·
                refine ⟨71519671735027269413844365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47679781156684846275896243 71519671735027269413844365)
                ·
                  refine ⟨26819876900635226030191637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71519671735027269413844365 26819876900635226030191637)
                  ·
                    refine ⟨1257181729717276220165233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26819876900635226030191637 1257181729717276220165233)
                    ·
                      rfl

theorem cell23_7345058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_7345058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345058 prefixEnd_7345058 := by exact prefixLift 7345058
  have htrace : WordTrace (prefixWord ++ tailWord_7345058) baseStart_7345058 baseEnd_7345058 := by
    simpa [prefixWord, tailWord_7345058, baseEnd_7345058] using wordTrace_append hprefix tailTrace_7345058
  have hstable : (prefixWord ++ tailWord_7345058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345058).length < 2 ^ (prefixWord ++ tailWord_7345058).sum := by decide
  have hdescent : baseEnd_7345058 < baseStart_7345058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345065 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 1, 1, 4]
def baseStart_7345065 : Nat := 118140960795 + 7345065 * 2 ^ 59
def prefixEnd_7345065 : Nat := 4983230072969 + 3 ^ 40 * 7345065 * 2
def baseEnd_7345065 : Nat := 3771548783516410133108167

theorem tailTrace_7345065 : CollatzResearch.WordTrace tailWord_7345065 prefixEnd_7345065 3771548783516410133108167 := by
  unfold tailWord_7345065
  simp only [CollatzResearch.WordTrace]
  refine ⟨267896529135091417076260649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178597686090060944717507099 267896529135091417076260649)
  ·
    refine ⟨200922396851318562807195487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267896529135091417076260649 200922396851318562807195487)
    ·
      refine ⟨301383595276977844210793231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200922396851318562807195487 301383595276977844210793231)
      ·
        refine ⟨452075392915466766316189847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301383595276977844210793231 452075392915466766316189847)
        ·
          refine ⟨678113089373200149474284771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452075392915466766316189847 678113089373200149474284771)
          ·
            refine ⟨1017169634059800224211427157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678113089373200149474284771 1017169634059800224211427157)
            ·
              refine ⟨5959978324569141938738831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1017169634059800224211427157 5959978324569141938738831)
              ·
                refine ⟨8939967486853712908108247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959978324569141938738831 8939967486853712908108247)
                ·
                  refine ⟨13409951230280569362162371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8939967486853712908108247 13409951230280569362162371)
                  ·
                    refine ⟨20114926845420854043243557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13409951230280569362162371 20114926845420854043243557)
                    ·
                      refine ⟨3771548783516410133108167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20114926845420854043243557 3771548783516410133108167)
                      ·
                        rfl

theorem cell23_7345065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 1, 4].length) (baseStart_7345065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345065 prefixEnd_7345065 := by exact prefixLift 7345065
  have htrace : WordTrace (prefixWord ++ tailWord_7345065) baseStart_7345065 baseEnd_7345065 := by
    simpa [prefixWord, tailWord_7345065, baseEnd_7345065] using wordTrace_append hprefix tailTrace_7345065
  have hstable : (prefixWord ++ tailWord_7345065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345065).length < 2 ^ (prefixWord ++ tailWord_7345065).sum := by decide
  have hdescent : baseEnd_7345065 < baseStart_7345065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345076 : List Nat := [2, 5, 2, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_7345076 : Nat := 118140960795 + 7345076 * 2 ^ 59
def prefixEnd_7345076 : Nat := 4983230072969 + 3 ^ 40 * 7345076 * 2
def baseEnd_7345076 : Nat := 3771554431803609590070617

theorem tailTrace_7345076 : CollatzResearch.WordTrace tailWord_7345076 prefixEnd_7345076 3771554431803609590070617 := by
  unfold tailWord_7345076
  simp only [CollatzResearch.WordTrace]
  refine ⟨133948465169025782977455541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178597953558701043969940721 133948465169025782977455541)
  ·
    refine ⟨12557668609596167154136457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133948465169025782977455541 12557668609596167154136457)
    ·
      refine ⟨9418251457197125365602343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12557668609596167154136457 9418251457197125365602343)
      ·
        refine ⟨14127377185795688048403515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9418251457197125365602343 14127377185795688048403515)
        ·
          refine ⟨21191065778693532072605273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14127377185795688048403515 21191065778693532072605273)
          ·
            refine ⟨15893299334020149054453955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21191065778693532072605273 15893299334020149054453955)
            ·
              refine ⟨23839949001030223581680933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15893299334020149054453955 23839949001030223581680933)
              ·
                refine ⟨4469990437693166921565175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23839949001030223581680933 4469990437693166921565175)
                ·
                  refine ⟨6704985656539750382347763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4469990437693166921565175 6704985656539750382347763)
                  ·
                    refine ⟨10057478484809625573521645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6704985656539750382347763 10057478484809625573521645)
                    ·
                      refine ⟨3771554431803609590070617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10057478484809625573521645 3771554431803609590070617)
                      ·
                        rfl

theorem cell23_7345076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_7345076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345076 prefixEnd_7345076 := by exact prefixLift 7345076
  have htrace : WordTrace (prefixWord ++ tailWord_7345076) baseStart_7345076 baseEnd_7345076 := by
    simpa [prefixWord, tailWord_7345076, baseEnd_7345076] using wordTrace_append hprefix tailTrace_7345076
  have hstable : (prefixWord ++ tailWord_7345076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345076).length < 2 ^ (prefixWord ++ tailWord_7345076).sum := by decide
  have hdescent : baseEnd_7345076 < baseStart_7345076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345088 : List Nat := [2, 1, 1, 2, 3, 5, 1, 8]
def baseStart_7345088 : Nat := 118140960795 + 7345088 * 2 ^ 59
def prefixEnd_7345088 : Nat := 4983230072969 + 3 ^ 40 * 7345088 * 2
def baseEnd_7345088 : Nat := 139687429391535686782243

theorem tailTrace_7345088 : CollatzResearch.WordTrace tailWord_7345088 prefixEnd_7345088 139687429391535686782243 := by
  unfold tailWord_7345088
  simp only [CollatzResearch.WordTrace]
  refine ⟨133948684007004046002173959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178598245342672061336231945 133948684007004046002173959)
  ·
    refine ⟨200923026010506069003260939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133948684007004046002173959 200923026010506069003260939)
    ·
      refine ⟨301384539015759103504891409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200923026010506069003260939 301384539015759103504891409)
      ·
        refine ⟨226038404261819327628668557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301384539015759103504891409 226038404261819327628668557)
        ·
          refine ⟨84764401598182247860750709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226038404261819327628668557 84764401598182247860750709)
          ·
            refine ⟨7946662649829585736945379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84764401598182247860750709 7946662649829585736945379)
            ·
              refine ⟨11919993974744378605418069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7946662649829585736945379 11919993974744378605418069)
              ·
                refine ⟨139687429391535686782243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11919993974744378605418069 139687429391535686782243)
                ·
                  rfl

theorem cell23_7345088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 8].length) (baseStart_7345088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345088 prefixEnd_7345088 := by exact prefixLift 7345088
  have htrace : WordTrace (prefixWord ++ tailWord_7345088) baseStart_7345088 baseEnd_7345088 := by
    simpa [prefixWord, tailWord_7345088, baseEnd_7345088] using wordTrace_append hprefix tailTrace_7345088
  have hstable : (prefixWord ++ tailWord_7345088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345088).length < 2 ^ (prefixWord ++ tailWord_7345088).sum := by decide
  have hdescent : baseEnd_7345088 < baseStart_7345088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345092 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_7345092 : Nat := 118140960795 + 7345092 * 2 ^ 59
def prefixEnd_7345092 : Nat := 4983230072969 + 3 ^ 40 * 7345092 * 2
def baseEnd_7345092 : Nat := 1257187549164693842490181

theorem tailTrace_7345092 : CollatzResearch.WordTrace tailWord_7345092 prefixEnd_7345092 1257187549164693842490181 := by
  unfold tailWord_7345092
  simp only [CollatzResearch.WordTrace]
  refine ⟨133948756952996800343746765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178598342603995733791662353 133948756952996800343746765)
  ·
    refine ⟨50230783857373800128905037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133948756952996800343746765 50230783857373800128905037)
    ·
      refine ⟨18836543946515175048339389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50230783857373800128905037 18836543946515175048339389)
      ·
        refine ⟨7063703979943190643127271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18836543946515175048339389 7063703979943190643127271)
        ·
          refine ⟨10595555969914785964690907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7063703979943190643127271 10595555969914785964690907)
          ·
            refine ⟨15893333954872178947036361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10595555969914785964690907 15893333954872178947036361)
            ·
              refine ⟨11920000466154134210277271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15893333954872178947036361 11920000466154134210277271)
              ·
                refine ⟨17880000699231201315415907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11920000466154134210277271 17880000699231201315415907)
                ·
                  refine ⟨26820001048846801973123861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17880000699231201315415907 26820001048846801973123861)
                  ·
                    refine ⟨1257187549164693842490181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26820001048846801973123861 1257187549164693842490181)
                    ·
                      rfl

theorem cell23_7345092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_7345092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345092 prefixEnd_7345092 := by exact prefixLift 7345092
  have htrace : WordTrace (prefixWord ++ tailWord_7345092) baseStart_7345092 baseEnd_7345092 := by
    simpa [prefixWord, tailWord_7345092, baseEnd_7345092] using wordTrace_append hprefix tailTrace_7345092
  have hstable : (prefixWord ++ tailWord_7345092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345092).length < 2 ^ (prefixWord ++ tailWord_7345092).sum := by decide
  have hdescent : baseEnd_7345092 < baseStart_7345092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345119 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 1, 2, 3]
def baseStart_7345119 : Nat := 118140960795 + 7345119 * 2 ^ 59
def prefixEnd_7345119 : Nat := 4983230072969 + 3 ^ 40 * 7345119 * 2
def baseEnd_7345119 : Nat := 3771576511471752921832919

theorem tailTrace_7345119 : CollatzResearch.WordTrace tailWord_7345119 prefixEnd_7345119 3771576511471752921832919 := by
  unfold tailWord_7345119
  simp only [CollatzResearch.WordTrace]
  refine ⟨267898498676895784298726411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178598999117930522865817607 267898498676895784298726411)
  ·
    refine ⟨401847748015343676448089617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267898498676895784298726411 401847748015343676448089617)
    ·
      refine ⟨301385811011507757336067213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401847748015343676448089617 301385811011507757336067213)
      ·
        refine ⟨113019679129315409001025205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301385811011507757336067213 113019679129315409001025205)
        ·
          refine ⟨10595594918373319593846113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113019679129315409001025205 10595594918373319593846113)
          ·
            refine ⟨7946696188779989695384585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10595594918373319593846113 7946696188779989695384585)
            ·
              refine ⟨5960022141584992271538439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7946696188779989695384585 5960022141584992271538439)
              ·
                refine ⟨8940033212377488407307659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960022141584992271538439 8940033212377488407307659)
                ·
                  refine ⟨13410049818566232610961489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8940033212377488407307659 13410049818566232610961489)
                  ·
                    refine ⟨10057537363924674458221117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13410049818566232610961489 10057537363924674458221117)
                    ·
                      refine ⟨3771576511471752921832919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10057537363924674458221117 3771576511471752921832919)
                      ·
                        rfl

theorem cell23_7345119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_7345119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345119 prefixEnd_7345119 := by exact prefixLift 7345119
  have htrace : WordTrace (prefixWord ++ tailWord_7345119) baseStart_7345119 baseEnd_7345119 := by
    simpa [prefixWord, tailWord_7345119, baseEnd_7345119] using wordTrace_append hprefix tailTrace_7345119
  have hstable : (prefixWord ++ tailWord_7345119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345119).length < 2 ^ (prefixWord ++ tailWord_7345119).sum := by decide
  have hdescent : baseEnd_7345119 < baseStart_7345119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345148 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_7345148 : Nat := 118140960795 + 7345148 * 2 ^ 59
def prefixEnd_7345148 : Nat := 4983230072969 + 3 ^ 40 * 7345148 * 2
def baseEnd_7345148 : Nat := 1257197134136911102790095

theorem tailTrace_7345148 : CollatzResearch.WordTrace tailWord_7345148 prefixEnd_7345148 1257197134136911102790095 := by
  unfold tailWord_7345148
  simp only [CollatzResearch.WordTrace]
  refine ⟨133949778196895361125766049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178599704262527148167688065 133949778196895361125766049)
  ·
    refine ⟨100462333647671520844324537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133949778196895361125766049 100462333647671520844324537)
    ·
      refine ⟨75346750235753640633243403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100462333647671520844324537 75346750235753640633243403)
      ·
        refine ⟨113020125353630460949865105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75346750235753640633243403 113020125353630460949865105)
        ·
          refine ⟨84765094015222845712398829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113020125353630460949865105 84765094015222845712398829)
          ·
            refine ⟨31786910255708567142149561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84765094015222845712398829 31786910255708567142149561)
            ·
              refine ⟨23840182691781425356612171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31786910255708567142149561 23840182691781425356612171)
              ·
                refine ⟨35760274037672138034918257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23840182691781425356612171 35760274037672138034918257)
                ·
                  refine ⟨26820205528254103526188693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35760274037672138034918257 26820205528254103526188693)
                  ·
                    refine ⟨1257197134136911102790095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26820205528254103526188693 1257197134136911102790095)
                    ·
                      rfl

theorem cell23_7345148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_7345148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345148 prefixEnd_7345148 := by exact prefixLift 7345148
  have htrace : WordTrace (prefixWord ++ tailWord_7345148) baseStart_7345148 baseEnd_7345148 := by
    simpa [prefixWord, tailWord_7345148, baseEnd_7345148] using wordTrace_append hprefix tailTrace_7345148
  have hstable : (prefixWord ++ tailWord_7345148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345148).length < 2 ^ (prefixWord ++ tailWord_7345148).sum := by decide
  have hdescent : baseEnd_7345148 < baseStart_7345148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345175 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_7345175 : Nat := 118140960795 + 7345175 * 2 ^ 59
def prefixEnd_7345175 : Nat := 4983230072969 + 3 ^ 40 * 7345175 * 2
def baseEnd_7345175 : Nat := 3771605266388404702732661

theorem tailTrace_7345175 : CollatzResearch.WordTrace tailWord_7345175 prefixEnd_7345175 3771605266388404702732661 := by
  unfold tailWord_7345175
  simp only [CollatzResearch.WordTrace]
  refine ⟨267900541164692905862764979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178600360776461937241843319 267900541164692905862764979)
  ·
    refine ⟨401850811747039358794147469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267900541164692905862764979 401850811747039358794147469)
    ·
      refine ⟨150694054405139759547805301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401850811747039358794147469 150694054405139759547805301)
      ·
        refine ⟨14127567600481852457606747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150694054405139759547805301 14127567600481852457606747)
        ·
          refine ⟨21191351400722778686410121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14127567600481852457606747 21191351400722778686410121)
          ·
            refine ⟨15893513550542084014807591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21191351400722778686410121 15893513550542084014807591)
            ·
              refine ⟨23840270325813126022211387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15893513550542084014807591 23840270325813126022211387)
              ·
                refine ⟨35760405488719689033317081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23840270325813126022211387 35760405488719689033317081)
                ·
                  refine ⟨26820304116539766774987811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35760405488719689033317081 26820304116539766774987811)
                  ·
                    refine ⟨40230456174809650162481717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26820304116539766774987811 40230456174809650162481717)
                    ·
                      refine ⟨3771605266388404702732661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40230456174809650162481717 3771605266388404702732661)
                      ·
                        rfl

theorem cell23_7345175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_7345175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345175 prefixEnd_7345175 := by exact prefixLift 7345175
  have htrace : WordTrace (prefixWord ++ tailWord_7345175) baseStart_7345175 baseEnd_7345175 := by
    simpa [prefixWord, tailWord_7345175, baseEnd_7345175] using wordTrace_append hprefix tailTrace_7345175
  have hstable : (prefixWord ++ tailWord_7345175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345175).length < 2 ^ (prefixWord ++ tailWord_7345175).sum := by decide
  have hdescent : baseEnd_7345175 < baseStart_7345175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345206 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_7345206 : Nat := 118140960795 + 7345206 * 2 ^ 59
def prefixEnd_7345206 : Nat := 4983230072969 + 3 ^ 40 * 7345206 * 2
def baseEnd_7345206 : Nat := 3771621184288694081445019

theorem tailTrace_7345206 : CollatzResearch.WordTrace tailWord_7345206 prefixEnd_7345206 3771621184288694081445019 := by
  unfold tailWord_7345206
  simp only [CollatzResearch.WordTrace]
  refine ⟨16743854489223787384821467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178601114551720398771428981 16743854489223787384821467)
  ·
    refine ⟨25115781733835681077232201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16743854489223787384821467 25115781733835681077232201)
    ·
      refine ⟨18836836300376760807924151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25115781733835681077232201 18836836300376760807924151)
      ·
        refine ⟨28255254450565141211886227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18836836300376760807924151 28255254450565141211886227)
        ·
          refine ⟨42382881675847711817829341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28255254450565141211886227 42382881675847711817829341)
          ·
            refine ⟨15893580628442891931686003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42382881675847711817829341 15893580628442891931686003)
            ·
              refine ⟨23840370942664337897529005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15893580628442891931686003 23840370942664337897529005)
              ·
                refine ⟨8940139103499126711573377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23840370942664337897529005 8940139103499126711573377)
                ·
                  refine ⟨6705104327624345033680033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8940139103499126711573377 6705104327624345033680033)
                  ·
                    refine ⟨5028828245718258775260025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6705104327624345033680033 5028828245718258775260025)
                    ·
                      refine ⟨3771621184288694081445019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028828245718258775260025 3771621184288694081445019)
                      ·
                        rfl

theorem cell23_7345206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_7345206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345206 prefixEnd_7345206 := by exact prefixLift 7345206
  have htrace : WordTrace (prefixWord ++ tailWord_7345206) baseStart_7345206 baseEnd_7345206 := by
    simpa [prefixWord, tailWord_7345206, baseEnd_7345206] using wordTrace_append hprefix tailTrace_7345206
  have hstable : (prefixWord ++ tailWord_7345206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345206).length < 2 ^ (prefixWord ++ tailWord_7345206).sum := by decide
  have hdescent : baseEnd_7345206 < baseStart_7345206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345246 : List Nat := [4, 4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_7345246 : Nat := 118140960795 + 7345246 * 2 ^ 59
def prefixEnd_7345246 : Nat := 4983230072969 + 3 ^ 40 * 7345246 * 2
def baseEnd_7345246 : Nat := 419071302612763769438315

theorem tailTrace_7345246 : CollatzResearch.WordTrace tailWord_7345246 prefixEnd_7345246 419071302612763769438315 := by
  unfold tailWord_7345246
  simp only [CollatzResearch.WordTrace]
  refine ⟨33487891343429460623574949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178602087164957123325733061 33487891343429460623574949)
  ·
    refine ⟨6278979626893023866920303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33487891343429460623574949 6278979626893023866920303)
    ·
      refine ⟨9418469440339535800380455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6278979626893023866920303 9418469440339535800380455)
      ·
        refine ⟨14127704160509303700570683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9418469440339535800380455 14127704160509303700570683)
        ·
          refine ⟨21191556240763955550856025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14127704160509303700570683 21191556240763955550856025)
          ·
            refine ⟨15893667180572966663142019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21191556240763955550856025 15893667180572966663142019)
            ·
              refine ⟨23840500770859449994713029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15893667180572966663142019 23840500770859449994713029)
              ·
                refine ⟨4470093894536146874008693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23840500770859449994713029 4470093894536146874008693)
                ·
                  refine ⟨419071302612763769438315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4470093894536146874008693 419071302612763769438315)
                  ·
                    rfl

theorem cell23_7345246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_7345246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345246 prefixEnd_7345246 := by exact prefixLift 7345246
  have htrace : WordTrace (prefixWord ++ tailWord_7345246) baseStart_7345246 baseEnd_7345246 := by
    simpa [prefixWord, tailWord_7345246, baseEnd_7345246] using wordTrace_append hprefix tailTrace_7345246
  have hstable : (prefixWord ++ tailWord_7345246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345246).length < 2 ^ (prefixWord ++ tailWord_7345246).sum := by decide
  have hdescent : baseEnd_7345246 < baseStart_7345246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345248 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_7345248 : Nat := 118140960795 + 7345248 * 2 ^ 59
def prefixEnd_7345248 : Nat := 4983230072969 + 3 ^ 40 * 7345248 * 2
def baseEnd_7345248 : Nat := 3771642750476182917119825

theorem tailTrace_7345248 : CollatzResearch.WordTrace tailWord_7345248 prefixEnd_7345248 3771642750476182917119825 := by
  unfold tailWord_7345248
  simp only [CollatzResearch.WordTrace]
  refine ⟨133951601846714219665086199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178602135795618959553448265 133951601846714219665086199)
  ·
    refine ⟨200927402770071329497629299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133951601846714219665086199 200927402770071329497629299)
    ·
      refine ⟨301391104155106994246443949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200927402770071329497629299 301391104155106994246443949)
      ·
        refine ⟨113021664058165122842416481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301391104155106994246443949 113021664058165122842416481)
        ·
          refine ⟨84766248043623842131812361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113021664058165122842416481 84766248043623842131812361)
          ·
            refine ⟨63574686032717881598859271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84766248043623842131812361 63574686032717881598859271)
            ·
              refine ⟨95362029049076822398288907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63574686032717881598859271 95362029049076822398288907)
              ·
                refine ⟨143043043573615233597433361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95362029049076822398288907 143043043573615233597433361)
                ·
                  refine ⟨107282282680211425198075021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143043043573615233597433361 107282282680211425198075021)
                  ·
                    refine ⟨40230856005079284449278133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107282282680211425198075021 40230856005079284449278133)
                    ·
                      refine ⟨3771642750476182917119825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40230856005079284449278133 3771642750476182917119825)
                      ·
                        rfl

theorem cell23_7345248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_7345248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345248 prefixEnd_7345248 := by exact prefixLift 7345248
  have htrace : WordTrace (prefixWord ++ tailWord_7345248) baseStart_7345248 baseEnd_7345248 := by
    simpa [prefixWord, tailWord_7345248, baseEnd_7345248] using wordTrace_append hprefix tailTrace_7345248
  have hstable : (prefixWord ++ tailWord_7345248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345248).length < 2 ^ (prefixWord ++ tailWord_7345248).sum := by decide
  have hdescent : baseEnd_7345248 < baseStart_7345248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345262 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_7345262 : Nat := 118140960795 + 7345262 * 2 ^ 59
def prefixEnd_7345262 : Nat := 4983230072969 + 3 ^ 40 * 7345262 * 2
def baseEnd_7345262 : Nat := 3771649939205345862344761

theorem tailTrace_7345262 : CollatzResearch.WordTrace tailWord_7345262 prefixEnd_7345262 3771649939205345862344761 := by
  unfold tailWord_7345262
  simp only [CollatzResearch.WordTrace]
  refine ⟨33487964289422214965147755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178602476210251813147454693 33487964289422214965147755)
  ·
    refine ⟨50231946434133322447721633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33487964289422214965147755 50231946434133322447721633)
    ·
      refine ⟨37673959825599991835791225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50231946434133322447721633 37673959825599991835791225)
      ·
        refine ⟨28255469869199993876843419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37673959825599991835791225 28255469869199993876843419)
        ·
          refine ⟨42383204803799990815265129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28255469869199993876843419 42383204803799990815265129)
          ·
            refine ⟨31787403602849993111448847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42383204803799990815265129 31787403602849993111448847)
            ·
              refine ⟨47681105404274989667173271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31787403602849993111448847 47681105404274989667173271)
              ·
                refine ⟨71521658106412484500759907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47681105404274989667173271 71521658106412484500759907)
                ·
                  refine ⟨107282487159618726751139861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71521658106412484500759907 107282487159618726751139861)
                  ·
                    refine ⟨5028866585607127816459681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107282487159618726751139861 5028866585607127816459681)
                    ·
                      refine ⟨3771649939205345862344761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028866585607127816459681 3771649939205345862344761)
                      ·
                        rfl

theorem cell23_7345262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_7345262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345262 prefixEnd_7345262 := by exact prefixLift 7345262
  have htrace : WordTrace (prefixWord ++ tailWord_7345262) baseStart_7345262 baseEnd_7345262 := by
    simpa [prefixWord, tailWord_7345262, baseEnd_7345262] using wordTrace_append hprefix tailTrace_7345262
  have hstable : (prefixWord ++ tailWord_7345262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345262).length < 2 ^ (prefixWord ++ tailWord_7345262).sum := by decide
  have hdescent : baseEnd_7345262 < baseStart_7345262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345289 : List Nat := [1, 2, 1, 1, 4, 4, 2, 3, 1, 4]
def baseStart_7345289 : Nat := 118140960795 + 7345289 * 2 ^ 59
def prefixEnd_7345289 : Nat := 4983230072969 + 3 ^ 40 * 7345289 * 2
def baseEnd_7345289 : Nat := 1257221267727672418902379

theorem tailTrace_7345289 : CollatzResearch.WordTrace tailWord_7345289 prefixEnd_7345289 1257221267727672418902379 := by
  unfold tailWord_7345289
  simp only [CollatzResearch.WordTrace]
  refine ⟨267904699086279903332414921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178603132724186602221609947 267904699086279903332414921)
  ·
    refine ⟨200928524314709927499311191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267904699086279903332414921 200928524314709927499311191)
    ·
      refine ⟨301392786472064891248966787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200928524314709927499311191 301392786472064891248966787)
      ·
        refine ⟨452089179708097336873450181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301392786472064891248966787 452089179708097336873450181)
        ·
          refine ⟨84766721195268250663771909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 452089179708097336873450181 84766721195268250663771909)
          ·
            refine ⟨15893760224112796999457233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84766721195268250663771909 15893760224112796999457233)
            ·
              refine ⟨11920320168084597749592925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15893760224112796999457233 11920320168084597749592925)
              ·
                refine ⟨4470120063031724156097347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11920320168084597749592925 4470120063031724156097347)
                ·
                  refine ⟨6705180094547586234146021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470120063031724156097347 6705180094547586234146021)
                  ·
                    refine ⟨1257221267727672418902379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6705180094547586234146021 1257221267727672418902379)
                    ·
                      rfl

theorem cell23_7345289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 1, 4].length) (baseStart_7345289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345289 prefixEnd_7345289 := by exact prefixLift 7345289
  have htrace : WordTrace (prefixWord ++ tailWord_7345289) baseStart_7345289 baseEnd_7345289 := by
    simpa [prefixWord, tailWord_7345289, baseEnd_7345289] using wordTrace_append hprefix tailTrace_7345289
  have hstable : (prefixWord ++ tailWord_7345289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345289).length < 2 ^ (prefixWord ++ tailWord_7345289).sum := by decide
  have hdescent : baseEnd_7345289 < baseStart_7345289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345319 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 6]
def baseStart_7345319 : Nat := 118140960795 + 7345319 * 2 ^ 59
def prefixEnd_7345319 : Nat := 4983230072969 + 3 ^ 40 * 7345319 * 2
def baseEnd_7345319 : Nat := 419075467511405793259111

theorem tailTrace_7345319 : CollatzResearch.WordTrace tailWord_7345319 prefixEnd_7345319 419075467511405793259111 := by
  unfold tailWord_7345319
  simp only [CollatzResearch.WordTrace]
  refine ⟨267905793276171218456007011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178603862184114145637338007 267905793276171218456007011)
  ·
    refine ⟨401858689914256827684010517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267905793276171218456007011 401858689914256827684010517)
    ·
      refine ⟨18837126089730788797687993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 401858689914256827684010517 18837126089730788797687993)
      ·
        refine ⟨14127844567298091598265995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18837126089730788797687993 14127844567298091598265995)
        ·
          refine ⟨21191766850947137397398993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14127844567298091598265995 21191766850947137397398993)
          ·
            refine ⟨15893825138210353048049245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21191766850947137397398993 15893825138210353048049245)
            ·
              refine ⟨5960184426828882393018467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15893825138210353048049245 5960184426828882393018467)
              ·
                refine ⟨8940276640243323589527701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960184426828882393018467 8940276640243323589527701)
                ·
                  refine ⟨419075467511405793259111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8940276640243323589527701 419075467511405793259111)
                  ·
                    rfl

theorem cell23_7345319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 6].length) (baseStart_7345319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345319 prefixEnd_7345319 := by exact prefixLift 7345319
  have htrace : WordTrace (prefixWord ++ tailWord_7345319) baseStart_7345319 baseEnd_7345319 := by
    simpa [prefixWord, tailWord_7345319, baseEnd_7345319] using wordTrace_append hprefix tailTrace_7345319
  have hstable : (prefixWord ++ tailWord_7345319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345319).length < 2 ^ (prefixWord ++ tailWord_7345319).sum := by decide
  have hdescent : baseEnd_7345319 < baseStart_7345319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345329 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 3, 1, 3]
def baseStart_7345329 : Nat := 118140960795 + 7345329 * 2 ^ 59
def prefixEnd_7345329 : Nat := 4983230072969 + 3 ^ 40 * 7345329 * 2
def baseEnd_7345329 : Nat := 3771684342409197100206953

theorem tailTrace_7345329 : CollatzResearch.WordTrace tailWord_7345329 prefixEnd_7345329 3771684342409197100206953 := by
  unfold tailWord_7345329
  simp only [CollatzResearch.WordTrace]
  refine ⟨267906158006134990163871041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178604105337423326775914027 267906158006134990163871041)
  ·
    refine ⟨200929618504601242622903281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267906158006134990163871041 200929618504601242622903281)
    ·
      refine ⟨150697213878450931967177461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200929618504601242622903281 150697213878450931967177461)
      ·
        refine ⟨14127863801104774871922887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150697213878450931967177461 14127863801104774871922887)
        ·
          refine ⟨21191795701657162307884331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14127863801104774871922887 21191795701657162307884331)
          ·
            refine ⟨31787693552485743461826497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21191795701657162307884331 31787693552485743461826497)
            ·
              refine ⟨23840770164364307596369873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31787693552485743461826497 23840770164364307596369873)
              ·
                refine ⟨17880577623273230697277405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23840770164364307596369873 17880577623273230697277405)
                ·
                  refine ⟨6705216608727461511479027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17880577623273230697277405 6705216608727461511479027)
                  ·
                    refine ⟨10057824913091192267218541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6705216608727461511479027 10057824913091192267218541)
                    ·
                      refine ⟨3771684342409197100206953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10057824913091192267218541 3771684342409197100206953)
                      ·
                        rfl

theorem cell23_7345329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_7345329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345329 prefixEnd_7345329 := by exact prefixLift 7345329
  have htrace : WordTrace (prefixWord ++ tailWord_7345329) baseStart_7345329 baseEnd_7345329 := by
    simpa [prefixWord, tailWord_7345329, baseEnd_7345329] using wordTrace_append hprefix tailTrace_7345329
  have hstable : (prefixWord ++ tailWord_7345329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345329).length < 2 ^ (prefixWord ++ tailWord_7345329).sum := by decide
  have hdescent : baseEnd_7345329 < baseStart_7345329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345352 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_7345352 : Nat := 118140960795 + 7345352 * 2 ^ 59
def prefixEnd_7345352 : Nat := 4983230072969 + 3 ^ 40 * 7345352 * 2
def baseEnd_7345352 : Nat := 3771696152464250510219347

theorem tailTrace_7345352 : CollatzResearch.WordTrace tailWord_7345352 prefixEnd_7345352 3771696152464250510219347 := by
  unfold tailWord_7345352
  simp only [CollatzResearch.WordTrace]
  refine ⟨133953498442525832545979155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178604664590034443394638873 133953498442525832545979155)
  ·
    refine ⟨200930247663788748818968733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133953498442525832545979155 200930247663788748818968733)
    ·
      refine ⟨75348842873920780807113275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200930247663788748818968733 75348842873920780807113275)
      ·
        refine ⟨113023264310881171210669913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75348842873920780807113275 113023264310881171210669913)
        ·
          refine ⟨84767448233160878408002435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113023264310881171210669913 84767448233160878408002435)
          ·
            refine ⟨127151172349741317612003653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84767448233160878408002435 127151172349741317612003653)
            ·
              refine ⟨23840844815576497052250685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127151172349741317612003653 23840844815576497052250685)
              ·
                refine ⟨8940316805841186394594007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23840844815576497052250685 8940316805841186394594007)
                ·
                  refine ⟨13410475208761779591891011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8940316805841186394594007 13410475208761779591891011)
                  ·
                    refine ⟨20115712813142669387836517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13410475208761779591891011 20115712813142669387836517)
                    ·
                      refine ⟨3771696152464250510219347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20115712813142669387836517 3771696152464250510219347)
                      ·
                        rfl

theorem cell23_7345352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_7345352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345352 prefixEnd_7345352 := by exact prefixLift 7345352
  have htrace : WordTrace (prefixWord ++ tailWord_7345352) baseStart_7345352 baseEnd_7345352 := by
    simpa [prefixWord, tailWord_7345352, baseEnd_7345352] using wordTrace_append hprefix tailTrace_7345352
  have hstable : (prefixWord ++ tailWord_7345352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345352).length < 2 ^ (prefixWord ++ tailWord_7345352).sum := by decide
  have hdescent : baseEnd_7345352 < baseStart_7345352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345362 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_7345362 : Nat := 118140960795 + 7345362 * 2 ^ 59
def prefixEnd_7345362 : Nat := 4983230072969 + 3 ^ 40 * 7345362 * 2
def baseEnd_7345362 : Nat := 1257233762423598490364767

theorem tailTrace_7345362 : CollatzResearch.WordTrace tailWord_7345362 prefixEnd_7345362 1257233762423598490364767 := by
  unfold tailWord_7345362
  simp only [CollatzResearch.WordTrace]
  refine ⟨66976840403753859199955585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178604907743343624533214893 66976840403753859199955585)
  ·
    refine ⟨50232630302815394399966689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66976840403753859199955585 50232630302815394399966689)
    ·
      refine ⟨37674472727111545799975017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50232630302815394399966689 37674472727111545799975017)
      ·
        refine ⟨28255854545333659349981263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37674472727111545799975017 28255854545333659349981263)
        ·
          refine ⟨42383781818000489024971895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28255854545333659349981263 42383781818000489024971895)
          ·
            refine ⟨63575672727000733537457843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42383781818000489024971895 63575672727000733537457843)
            ·
              refine ⟨95363509090501100306186765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63575672727000733537457843 95363509090501100306186765)
              ·
                refine ⟨35761315908937912614820037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95363509090501100306186765 35761315908937912614820037)
                ·
                  refine ⟨6705246732925858615278757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35761315908937912614820037 6705246732925858615278757)
                  ·
                    refine ⟨1257233762423598490364767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6705246732925858615278757 1257233762423598490364767)
                    ·
                      rfl

theorem cell23_7345362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_7345362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345362 prefixEnd_7345362 := by exact prefixLift 7345362
  have htrace : WordTrace (prefixWord ++ tailWord_7345362) baseStart_7345362 baseEnd_7345362 := by
    simpa [prefixWord, tailWord_7345362, baseEnd_7345362] using wordTrace_append hprefix tailTrace_7345362
  have hstable : (prefixWord ++ tailWord_7345362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345362).length < 2 ^ (prefixWord ++ tailWord_7345362).sum := by decide
  have hdescent : baseEnd_7345362 < baseStart_7345362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345389 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_7345389 : Nat := 118140960795 + 7345389 * 2 ^ 59
def prefixEnd_7345389 : Nat := 4983230072969 + 3 ^ 40 * 7345389 * 2
def baseEnd_7345389 : Nat := 3771715151248466865456677

theorem tailTrace_7345389 : CollatzResearch.WordTrace tailWord_7345389 prefixEnd_7345389 3771715151248466865456677 := by
  unfold tailWord_7345389
  simp only [CollatzResearch.WordTrace]
  refine ⟨267908346385917620411055221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178605564257278413607370147 267908346385917620411055221)
  ·
    refine ⟨25116407473679776913536427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267908346385917620411055221 25116407473679776913536427)
    ·
      refine ⟨37674611210519665370304641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25116407473679776913536427 37674611210519665370304641)
      ·
        refine ⟨28255958407889749027728481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37674611210519665370304641 28255958407889749027728481)
        ·
          refine ⟨21191968805917311770796361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28255958407889749027728481 21191968805917311770796361)
          ·
            refine ⟨15893976604437983828097271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21191968805917311770796361 15893976604437983828097271)
            ·
              refine ⟨23840964906656975742145907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15893976604437983828097271 23840964906656975742145907)
              ·
                refine ⟨35761447359985463613218861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23840964906656975742145907 35761447359985463613218861)
                ·
                  refine ⟨13410542759994548854957073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35761447359985463613218861 13410542759994548854957073)
                  ·
                    refine ⟨10057907069995911641217805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13410542759994548854957073 10057907069995911641217805)
                    ·
                      refine ⟨3771715151248466865456677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10057907069995911641217805 3771715151248466865456677)
                      ·
                        rfl

theorem cell23_7345389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_7345389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345389 prefixEnd_7345389 := by exact prefixLift 7345389
  have htrace : WordTrace (prefixWord ++ tailWord_7345389) baseStart_7345389 baseEnd_7345389 := by
    simpa [prefixWord, tailWord_7345389, baseEnd_7345389] using wordTrace_append hprefix tailTrace_7345389
  have hstable : (prefixWord ++ tailWord_7345389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345389).length < 2 ^ (prefixWord ++ tailWord_7345389).sum := by decide
  have hdescent : baseEnd_7345389 < baseStart_7345389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345402 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3]
def baseStart_7345402 : Nat := 118140960795 + 7345402 * 2 ^ 59
def prefixEnd_7345402 : Nat := 4983230072969 + 3 ^ 40 * 7345402 * 2
def baseEnd_7345402 : Nat := 3771721826496975314594117

theorem tailTrace_7345402 : CollatzResearch.WordTrace tailWord_7345402 prefixEnd_7345402 3771721826496975314594117 := by
  unfold tailWord_7345402
  simp only [CollatzResearch.WordTrace]
  refine ⟨66977205133717630907819615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178605880356580349087518973 66977205133717630907819615)
  ·
    refine ⟨100465807700576446361729423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66977205133717630907819615 100465807700576446361729423)
    ·
      refine ⟨150698711550864669542594135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100465807700576446361729423 150698711550864669542594135)
      ·
        refine ⟨226048067326297004313891203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150698711550864669542594135 226048067326297004313891203)
        ·
          refine ⟨339072100989445506470836805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226048067326297004313891203 339072100989445506470836805)
          ·
            refine ⟨63576018935521032463281901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339072100989445506470836805 63576018935521032463281901)
            ·
              refine ⟨23841007100820387173730713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63576018935521032463281901 23841007100820387173730713)
              ·
                refine ⟨17880755325615290380298035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23841007100820387173730713 17880755325615290380298035)
                ·
                  refine ⟨26821132988422935570447053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17880755325615290380298035 26821132988422935570447053)
                  ·
                    refine ⟨10057924870658600838917645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26821132988422935570447053 10057924870658600838917645)
                    ·
                      refine ⟨3771721826496975314594117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10057924870658600838917645 3771721826496975314594117)
                      ·
                        rfl

theorem cell23_7345402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_7345402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345402 prefixEnd_7345402 := by exact prefixLift 7345402
  have htrace : WordTrace (prefixWord ++ tailWord_7345402) baseStart_7345402 baseEnd_7345402 := by
    simpa [prefixWord, tailWord_7345402, baseEnd_7345402] using wordTrace_append hprefix tailTrace_7345402
  have hstable : (prefixWord ++ tailWord_7345402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345402).length < 2 ^ (prefixWord ++ tailWord_7345402).sum := by decide
  have hdescent : baseEnd_7345402 < baseStart_7345402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345419 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 2, 1, 3]
def baseStart_7345419 : Nat := 118140960795 + 7345419 * 2 ^ 59
def prefixEnd_7345419 : Nat := 4983230072969 + 3 ^ 40 * 7345419 * 2
def baseEnd_7345419 : Nat := 3771730555668101748081539

theorem tailTrace_7345419 : CollatzResearch.WordTrace tailWord_7345419 prefixEnd_7345419 3771730555668101748081539 := by
  unfold tailWord_7345419
  simp only [CollatzResearch.WordTrace]
  refine ⟨267909440575808935534647311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178606293717205957023098207 267909440575808935534647311)
  ·
    refine ⟨401864160863713403301970967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267909440575808935534647311 401864160863713403301970967)
    ·
      refine ⟨602796241295570104952956451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401864160863713403301970967 602796241295570104952956451)
      ·
        refine ⟨904194361943355157429434677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602796241295570104952956451 904194361943355157429434677)
        ·
          refine ⟨84768221432189546009009501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 904194361943355157429434677 84768221432189546009009501)
          ·
            refine ⟨31788083037071079753378563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84768221432189546009009501 31788083037071079753378563)
            ·
              refine ⟨47682124555606619630067845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31788083037071079753378563 47682124555606619630067845)
              ·
                refine ⟨8940398354176241180637721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47682124555606619630067845 8940398354176241180637721)
                ·
                  refine ⟨6705298765632180885478291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8940398354176241180637721 6705298765632180885478291)
                  ·
                    refine ⟨10057948148448271328217437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6705298765632180885478291 10057948148448271328217437)
                    ·
                      refine ⟨3771730555668101748081539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10057948148448271328217437 3771730555668101748081539)
                      ·
                        rfl

theorem cell23_7345419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 1, 3].length) (baseStart_7345419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345419 prefixEnd_7345419 := by exact prefixLift 7345419
  have htrace : WordTrace (prefixWord ++ tailWord_7345419) baseStart_7345419 baseEnd_7345419 := by
    simpa [prefixWord, tailWord_7345419, baseEnd_7345419] using wordTrace_append hprefix tailTrace_7345419
  have hstable : (prefixWord ++ tailWord_7345419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345419).length < 2 ^ (prefixWord ++ tailWord_7345419).sum := by decide
  have hdescent : baseEnd_7345419 < baseStart_7345419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345420 : List Nat := [2, 2, 1, 2, 2, 5, 2, 2, 1, 2, 2]
def baseStart_7345420 : Nat := 118140960795 + 7345420 * 2 ^ 59
def prefixEnd_7345420 : Nat := 4983230072969 + 3 ^ 40 * 7345420 * 2
def baseEnd_7345420 : Nat := 3771731069148756244169035

theorem tailTrace_7345420 : CollatzResearch.WordTrace tailWord_7345420 prefixEnd_7345420 3771731069148756244169035 := by
  unfold tailWord_7345420
  simp only [CollatzResearch.WordTrace]
  refine ⟨133954738524402656352716857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178606318032536875136955809 133954738524402656352716857)
  ·
    refine ⟨100466053893301992264537643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133954738524402656352716857 100466053893301992264537643)
    ·
      refine ⟨150699080839952988396806465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100466053893301992264537643 150699080839952988396806465)
      ·
        refine ⟨113024310629964741297604849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150699080839952988396806465 113024310629964741297604849)
        ·
          refine ⟨84768232972473555973203637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113024310629964741297604849 84768232972473555973203637)
          ·
            refine ⟨7947021841169395872487841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84768232972473555973203637 7947021841169395872487841)
            ·
              refine ⟨5960266380877046904365881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7947021841169395872487841 5960266380877046904365881)
              ·
                refine ⟨4470199785657785178274411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5960266380877046904365881 4470199785657785178274411)
                ·
                  refine ⟨6705299678486677767411617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470199785657785178274411 6705299678486677767411617)
                  ·
                    refine ⟨5028974758865008325558713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6705299678486677767411617 5028974758865008325558713)
                    ·
                      refine ⟨3771731069148756244169035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5028974758865008325558713 3771731069148756244169035)
                      ·
                        rfl

theorem cell23_7345420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_7345420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345420 prefixEnd_7345420 := by exact prefixLift 7345420
  have htrace : WordTrace (prefixWord ++ tailWord_7345420) baseStart_7345420 baseEnd_7345420 := by
    simpa [prefixWord, tailWord_7345420, baseEnd_7345420] using wordTrace_append hprefix tailTrace_7345420
  have hstable : (prefixWord ++ tailWord_7345420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345420).length < 2 ^ (prefixWord ++ tailWord_7345420).sum := by decide
  have hdescent : baseEnd_7345420 < baseStart_7345420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345425 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_7345425 : Nat := 118140960795 + 7345425 * 2 ^ 59
def prefixEnd_7345425 : Nat := 4983230072969 + 3 ^ 40 * 7345425 * 2
def baseEnd_7345425 : Nat := 3771733636552028724606511

theorem tailTrace_7345425 : CollatzResearch.WordTrace tailWord_7345425 prefixEnd_7345425 3771733636552028724606511 := by
  unfold tailWord_7345425
  simp only [CollatzResearch.WordTrace]
  refine ⟨267909659413787198559365729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178606439609191465706243819 267909659413787198559365729)
  ·
    refine ⟨200932244560340398919524297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267909659413787198559365729 200932244560340398919524297)
    ·
      refine ⟨150699183420255299189643223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200932244560340398919524297 150699183420255299189643223)
      ·
        refine ⟨226048775130382948784464835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150699183420255299189643223 226048775130382948784464835)
        ·
          refine ⟨339073162695574423176697253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226048775130382948784464835 339073162695574423176697253)
          ·
            refine ⟨63576218005420204345630735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339073162695574423176697253 63576218005420204345630735)
            ·
              refine ⟨95364327008130306518446103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63576218005420204345630735 95364327008130306518446103)
              ·
                refine ⟨143046490512195459777669155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95364327008130306518446103 143046490512195459777669155)
                ·
                  refine ⟨214569735768293189666503733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143046490512195459777669155 214569735768293189666503733)
                  ·
                    refine ⟨20115912728277486531234725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 214569735768293189666503733 20115912728277486531234725)
                    ·
                      refine ⟨3771733636552028724606511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20115912728277486531234725 3771733636552028724606511)
                      ·
                        rfl

theorem cell23_7345425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_7345425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345425 prefixEnd_7345425 := by exact prefixLift 7345425
  have htrace : WordTrace (prefixWord ++ tailWord_7345425) baseStart_7345425 baseEnd_7345425 := by
    simpa [prefixWord, tailWord_7345425, baseEnd_7345425] using wordTrace_append hprefix tailTrace_7345425
  have hstable : (prefixWord ++ tailWord_7345425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345425).length < 2 ^ (prefixWord ++ tailWord_7345425).sum := by decide
  have hdescent : baseEnd_7345425 < baseStart_7345425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345426 : List Nat := [3, 2, 4, 2, 1, 2, 1, 8]
def baseStart_7345426 : Nat := 118140960795 + 7345426 * 2 ^ 59
def prefixEnd_7345426 : Nat := 4983230072969 + 3 ^ 40 * 7345426 * 2
def baseEnd_7345426 : Nat := 139693857408617897062741

theorem tailTrace_7345426 : CollatzResearch.WordTrace tailWord_7345426 prefixEnd_7345426 139693857408617897062741 := by
  unfold tailWord_7345426
  simp only [CollatzResearch.WordTrace]
  refine ⟨66977423971695893932538033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178606463924522383820101421 66977423971695893932538033)
  ·
    refine ⟨50233067978771920449403525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66977423971695893932538033 50233067978771920449403525)
    ·
      refine ⟨9418700246019735084263161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50233067978771920449403525 9418700246019735084263161)
      ·
        refine ⟨7064025184514801313197371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9418700246019735084263161 7064025184514801313197371)
        ·
          refine ⟨10596037776772201969796057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7064025184514801313197371 10596037776772201969796057)
          ·
            refine ⟨7947028332579151477347043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10596037776772201969796057 7947028332579151477347043)
            ·
              refine ⟨11920542498868727216020565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7947028332579151477347043 11920542498868727216020565)
              ·
                refine ⟨139693857408617897062741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11920542498868727216020565 139693857408617897062741)
                ·
                  rfl

theorem cell23_7345426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 8].length) (baseStart_7345426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345426 prefixEnd_7345426 := by exact prefixLift 7345426
  have htrace : WordTrace (prefixWord ++ tailWord_7345426) baseStart_7345426 baseEnd_7345426 := by
    simpa [prefixWord, tailWord_7345426, baseEnd_7345426] using wordTrace_append hprefix tailTrace_7345426
  have hstable : (prefixWord ++ tailWord_7345426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345426).length < 2 ^ (prefixWord ++ tailWord_7345426).sum := by decide
  have hdescent : baseEnd_7345426 < baseStart_7345426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345455 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 4]
def baseStart_7345455 : Nat := 118140960795 + 7345455 * 2 ^ 59
def prefixEnd_7345455 : Nat := 4983230072969 + 3 ^ 40 * 7345455 * 2
def baseEnd_7345455 : Nat := 3771749040971663607231373

theorem tailTrace_7345455 : CollatzResearch.WordTrace tailWord_7345455 prefixEnd_7345455 3771749040971663607231373 := by
  unfold tailWord_7345455
  simp only [CollatzResearch.WordTrace]
  refine ⟨267910753603678513682957819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178607169069119009121971879 267910753603678513682957819)
  ·
    refine ⟨401866130405517770524436729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267910753603678513682957819 401866130405517770524436729)
    ·
      refine ⟨301399597804138327893327547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401866130405517770524436729 301399597804138327893327547)
      ·
        refine ⟨452099396706207491839991321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301399597804138327893327547 452099396706207491839991321)
        ·
          refine ⟨339074547529655618879993491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452099396706207491839991321 339074547529655618879993491)
          ·
            refine ⟨508611821294483428319990237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339074547529655618879993491 508611821294483428319990237)
            ·
              refine ⟨190729432985431285619996339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508611821294483428319990237 190729432985431285619996339)
              ·
                refine ⟨286094149478146928429994509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190729432985431285619996339 286094149478146928429994509)
                ·
                  refine ⟨107285306054305098161247941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286094149478146928429994509 107285306054305098161247941)
                  ·
                    refine ⟨20115994885182205905233989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107285306054305098161247941 20115994885182205905233989)
                    ·
                      refine ⟨3771749040971663607231373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20115994885182205905233989 3771749040971663607231373)
                      ·
                        rfl

theorem cell23_7345455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_7345455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345455 prefixEnd_7345455 := by exact prefixLift 7345455
  have htrace : WordTrace (prefixWord ++ tailWord_7345455) baseStart_7345455 baseEnd_7345455 := by
    simpa [prefixWord, tailWord_7345455, baseEnd_7345455] using wordTrace_append hprefix tailTrace_7345455
  have hstable : (prefixWord ++ tailWord_7345455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345455).length < 2 ^ (prefixWord ++ tailWord_7345455).sum := by decide
  have hdescent : baseEnd_7345455 < baseStart_7345455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345459 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 1, 4, 2]
def baseStart_7345459 : Nat := 118140960795 + 7345459 * 2 ^ 59
def prefixEnd_7345459 : Nat := 4983230072969 + 3 ^ 40 * 7345459 * 2
def baseEnd_7345459 : Nat := 3771751094894281591581355

theorem tailTrace_7345459 : CollatzResearch.WordTrace tailWord_7345459 prefixEnd_7345459 3771751094894281591581355 := by
  unfold tailWord_7345459
  simp only [CollatzResearch.WordTrace]
  refine ⟨267910899495664022366103431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178607266330442681577402287 267910899495664022366103431)
  ·
    refine ⟨401866349243496033549155147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267910899495664022366103431 401866349243496033549155147)
    ·
      refine ⟨602799523865244050323732721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401866349243496033549155147 602799523865244050323732721)
      ·
        refine ⟨452099642898933037742799541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602799523865244050323732721 452099642898933037742799541)
        ·
          refine ⟨42384341521774972288387457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 452099642898933037742799541 42384341521774972288387457)
          ·
            refine ⟨31788256141331229216290593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42384341521774972288387457 31788256141331229216290593)
            ·
              refine ⟨23841192105998421912217945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31788256141331229216290593 23841192105998421912217945)
              ·
                refine ⟨17880894079498816434163459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23841192105998421912217945 17880894079498816434163459)
                ·
                  refine ⟨26821341119248224651245189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17880894079498816434163459 26821341119248224651245189)
                  ·
                    refine ⟨5029001459859042122108473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26821341119248224651245189 5029001459859042122108473)
                    ·
                      refine ⟨3771751094894281591581355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5029001459859042122108473 3771751094894281591581355)
                      ·
                        rfl

theorem cell23_7345459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 4, 2].length) (baseStart_7345459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345459 prefixEnd_7345459 := by exact prefixLift 7345459
  have htrace : WordTrace (prefixWord ++ tailWord_7345459) baseStart_7345459 baseEnd_7345459 := by
    simpa [prefixWord, tailWord_7345459, baseEnd_7345459] using wordTrace_append hprefix tailTrace_7345459
  have hstable : (prefixWord ++ tailWord_7345459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345459).length < 2 ^ (prefixWord ++ tailWord_7345459).sum := by decide
  have hdescent : baseEnd_7345459 < baseStart_7345459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345516 : List Nat := [2, 2, 1, 1, 5, 3, 1, 3, 5]
def baseStart_7345516 : Nat := 118140960795 + 7345516 * 2 ^ 59
def prefixEnd_7345516 : Nat := 4983230072969 + 3 ^ 40 * 7345516 * 2
def baseEnd_7345516 : Nat := 419086707032398652063177

theorem tailTrace_7345516 : CollatzResearch.WordTrace tailWord_7345516 prefixEnd_7345516 419086707032398652063177 := by
  unfold tailWord_7345516
  simp only [CollatzResearch.WordTrace]
  refine ⟨133956489228228760550464201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178608652304305014067285601 133956489228228760550464201)
  ·
    refine ⟨100467366921171570412848151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133956489228228760550464201 100467366921171570412848151)
    ·
      refine ⟨150701050381757355619272227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100467366921171570412848151 150701050381757355619272227)
      ·
        refine ⟨226051575572636033428908341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150701050381757355619272227 226051575572636033428908341)
        ·
          refine ⟨21192335209934628133960157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226051575572636033428908341 21192335209934628133960157)
          ·
            refine ⟨7947125703725485550235059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21192335209934628133960157 7947125703725485550235059)
            ·
              refine ⟨11920688555588228325352589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7947125703725485550235059 11920688555588228325352589)
              ·
                refine ⟨4470258208345585622007221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11920688555588228325352589 4470258208345585622007221)
                ·
                  refine ⟨419086707032398652063177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4470258208345585622007221 419086707032398652063177)
                  ·
                    rfl

theorem cell23_7345516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_7345516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345516 prefixEnd_7345516 := by exact prefixLift 7345516
  have htrace : WordTrace (prefixWord ++ tailWord_7345516) baseStart_7345516 baseEnd_7345516 := by
    simpa [prefixWord, tailWord_7345516, baseEnd_7345516] using wordTrace_append hprefix tailTrace_7345516
  have hstable : (prefixWord ++ tailWord_7345516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345516).length < 2 ^ (prefixWord ++ tailWord_7345516).sum := by decide
  have hdescent : baseEnd_7345516 < baseStart_7345516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345522 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_7345522 : Nat := 118140960795 + 7345522 * 2 ^ 59
def prefixEnd_7345522 : Nat := 4983230072969 + 3 ^ 40 * 7345522 * 2
def baseEnd_7345522 : Nat := 3771783444175514845093565

theorem tailTrace_7345522 : CollatzResearch.WordTrace tailWord_7345522 prefixEnd_7345522 3771783444175514845093565 := by
  unfold tailWord_7345522
  simp only [CollatzResearch.WordTrace]
  refine ⟨66978299323608946031411705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178608798196290522750431213 66978299323608946031411705)
  ·
    refine ⟨50233724492706709523558779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66978299323608946031411705 50233724492706709523558779)
    ·
      refine ⟨75350586739060064285338169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50233724492706709523558779 75350586739060064285338169)
      ·
        refine ⟨56512940054295048214003627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75350586739060064285338169 56512940054295048214003627)
        ·
          refine ⟨84769410081442572321005441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56512940054295048214003627 84769410081442572321005441)
          ·
            refine ⟨63577057561081929240754081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84769410081442572321005441 63577057561081929240754081)
            ·
              refine ⟨47682793170811446930565561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63577057561081929240754081 47682793170811446930565561)
              ·
                refine ⟨35762094878108585197924171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47682793170811446930565561 35762094878108585197924171)
                ·
                  refine ⟨53643142317162877796886257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35762094878108585197924171 53643142317162877796886257)
                  ·
                    refine ⟨40232356737872158347664693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53643142317162877796886257 40232356737872158347664693)
                    ·
                      refine ⟨3771783444175514845093565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40232356737872158347664693 3771783444175514845093565)
                      ·
                        rfl

theorem cell23_7345522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_7345522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345522 prefixEnd_7345522 := by exact prefixLift 7345522
  have htrace : WordTrace (prefixWord ++ tailWord_7345522) baseStart_7345522 baseEnd_7345522 := by
    simpa [prefixWord, tailWord_7345522, baseEnd_7345522] using wordTrace_append hprefix tailTrace_7345522
  have hstable : (prefixWord ++ tailWord_7345522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345522).length < 2 ^ (prefixWord ++ tailWord_7345522).sum := by decide
  have hdescent : baseEnd_7345522 < baseStart_7345522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345589 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 6]
def baseStart_7345589 : Nat := 118140960795 + 7345589 * 2 ^ 59
def prefixEnd_7345589 : Nat := 4983230072969 + 3 ^ 40 * 7345589 * 2
def baseEnd_7345589 : Nat := 419090871931040675883973

theorem tailTrace_7345589 : CollatzResearch.WordTrace tailWord_7345589 prefixEnd_7345589 419090871931040675883973 := by
  unfold tailWord_7345589
  simp only [CollatzResearch.WordTrace]
  refine ⟨267915640985193054568335821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178610427323462036378890547 267915640985193054568335821)
  ·
    refine ⟨100468365369447395463125933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267915640985193054568335821 100468365369447395463125933)
    ·
      refine ⟨37675637013542773298672225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100468365369447395463125933 37675637013542773298672225)
      ·
        refine ⟨28256727760157079974004169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37675637013542773298672225 28256727760157079974004169)
        ·
          refine ⟨21192545820117809980503127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28256727760157079974004169 21192545820117809980503127)
          ·
            refine ⟨31788818730176714970754691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21192545820117809980503127 31788818730176714970754691)
            ·
              refine ⟨47683228095265072456132037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31788818730176714970754691 47683228095265072456132037)
              ·
                refine ⟨8940605267862201085524757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47683228095265072456132037 8940605267862201085524757)
                ·
                  refine ⟨419090871931040675883973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8940605267862201085524757 419090871931040675883973)
                  ·
                    rfl

theorem cell23_7345589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_7345589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345589 prefixEnd_7345589 := by exact prefixLift 7345589
  have htrace : WordTrace (prefixWord ++ tailWord_7345589) baseStart_7345589 baseEnd_7345589 := by
    simpa [prefixWord, tailWord_7345589, baseEnd_7345589] using wordTrace_append hprefix tailTrace_7345589
  have hstable : (prefixWord ++ tailWord_7345589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345589).length < 2 ^ (prefixWord ++ tailWord_7345589).sum := by decide
  have hdescent : baseEnd_7345589 < baseStart_7345589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345593 : List Nat := [1, 2, 1, 4, 4, 1, 1, 4, 1, 4]
def baseStart_7345593 : Nat := 118140960795 + 7345593 * 2 ^ 59
def prefixEnd_7345593 : Nat := 4983230072969 + 3 ^ 40 * 7345593 * 2
def baseEnd_7345593 : Nat := 1257273300433994689101913

theorem tailTrace_7345593 : CollatzResearch.WordTrace tailWord_7345593 prefixEnd_7345593 1257273300433994689101913 := by
  unfold tailWord_7345593
  simp only [CollatzResearch.WordTrace]
  refine ⟨267915786877178563251481433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178610524584785708834320955 267915786877178563251481433)
  ·
    refine ⟨200936840157883922438611075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267915786877178563251481433 200936840157883922438611075)
    ·
      refine ⟨301405260236825883657916613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200936840157883922438611075 301405260236825883657916613)
      ·
        refine ⟨56513486294404853185859365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301405260236825883657916613 56513486294404853185859365)
        ·
          refine ⟨10596278680200909972348631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56513486294404853185859365 10596278680200909972348631)
          ·
            refine ⟨15894418020301364958522947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10596278680200909972348631 15894418020301364958522947)
            ·
              refine ⟨23841627030452047437784421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15894418020301364958522947 23841627030452047437784421)
              ·
                refine ⟨4470305068209758894584579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23841627030452047437784421 4470305068209758894584579)
                ·
                  refine ⟨6705457602314638341876869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470305068209758894584579 6705457602314638341876869)
                  ·
                    refine ⟨1257273300433994689101913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6705457602314638341876869 1257273300433994689101913)
                    ·
                      rfl

theorem cell23_7345593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 1, 4].length) (baseStart_7345593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345593 prefixEnd_7345593 := by exact prefixLift 7345593
  have htrace : WordTrace (prefixWord ++ tailWord_7345593) baseStart_7345593 baseEnd_7345593 := by
    simpa [prefixWord, tailWord_7345593, baseEnd_7345593] using wordTrace_append hprefix tailTrace_7345593
  have hstable : (prefixWord ++ tailWord_7345593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345593).length < 2 ^ (prefixWord ++ tailWord_7345593).sum := by decide
  have hdescent : baseEnd_7345593 < baseStart_7345593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345599 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 7, 1, 3]
def baseStart_7345599 : Nat := 118140960795 + 7345599 * 2 ^ 59
def prefixEnd_7345599 : Nat := 4983230072969 + 3 ^ 40 * 7345599 * 2
def baseEnd_7345599 : Nat := 3771822982185911043830711

theorem tailTrace_7345599 : CollatzResearch.WordTrace tailWord_7345599 prefixEnd_7345599 3771822982185911043830711 := by
  unfold tailWord_7345599
  simp only [CollatzResearch.WordTrace]
  refine ⟨267916005715156826276199851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178610670476771217517466567 267916005715156826276199851)
  ·
    refine ⟨401874008572735239414299777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267916005715156826276199851 401874008572735239414299777)
    ·
      refine ⟨301405506429551429560724833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401874008572735239414299777 301405506429551429560724833)
      ·
        refine ⟨226054129822163572170543625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301405506429551429560724833 226054129822163572170543625)
        ·
          refine ⟨169540597366622679127907719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226054129822163572170543625 169540597366622679127907719)
          ·
            refine ⟨254310896049934018691861579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169540597366622679127907719 254310896049934018691861579)
            ·
              refine ⟨381466344074901028037792369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254310896049934018691861579 381466344074901028037792369)
              ·
                refine ⟨286099758056175771028344277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381466344074901028037792369 286099758056175771028344277)
                ·
                  refine ⟨6705463079441619633476819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 286099758056175771028344277 6705463079441619633476819)
                  ·
                    refine ⟨10058194619162429450215229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6705463079441619633476819 10058194619162429450215229)
                    ·
                      refine ⟨3771822982185911043830711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10058194619162429450215229 3771822982185911043830711)
                      ·
                        rfl

theorem cell23_7345599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_7345599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345599 prefixEnd_7345599 := by exact prefixLift 7345599
  have htrace : WordTrace (prefixWord ++ tailWord_7345599) baseStart_7345599 baseEnd_7345599 := by
    simpa [prefixWord, tailWord_7345599, baseEnd_7345599] using wordTrace_append hprefix tailTrace_7345599
  have hstable : (prefixWord ++ tailWord_7345599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345599).length < 2 ^ (prefixWord ++ tailWord_7345599).sum := by decide
  have hdescent : baseEnd_7345599 < baseStart_7345599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345609 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 1, 5, 2]
def baseStart_7345609 : Nat := 118140960795 + 7345609 * 2 ^ 59
def prefixEnd_7345609 : Nat := 4983230072969 + 3 ^ 40 * 7345609 * 2
def baseEnd_7345609 : Nat := 3771828116992456004705665

theorem tailTrace_7345609 : CollatzResearch.WordTrace tailWord_7345609 prefixEnd_7345609 3771828116992456004705665 := by
  unfold tailWord_7345609
  simp only [CollatzResearch.WordTrace]
  refine ⟨267916370445120597984063881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178610913630080398656042587 267916370445120597984063881)
  ·
    refine ⟨200937277833840448488047911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267916370445120597984063881 200937277833840448488047911)
    ·
      refine ⟨301405916750760672732071867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200937277833840448488047911 301405916750760672732071867)
      ·
        refine ⟨452108875126141009098107801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301405916750760672732071867 452108875126141009098107801)
        ·
          refine ⟨339081656344605756823580851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452108875126141009098107801 339081656344605756823580851)
          ·
            refine ⟨508622484516908635235371277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339081656344605756823580851 508622484516908635235371277)
            ·
              refine ⟨190733431693840738213264229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508622484516908635235371277 190733431693840738213264229)
              ·
                refine ⟨35762518442595138414987043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190733431693840738213264229 35762518442595138414987043)
                ·
                  refine ⟨53643777663892707622480565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35762518442595138414987043 53643777663892707622480565)
                  ·
                    refine ⟨5029104155989941339607553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53643777663892707622480565 5029104155989941339607553)
                    ·
                      refine ⟨3771828116992456004705665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5029104155989941339607553 3771828116992456004705665)
                      ·
                        rfl

theorem cell23_7345609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 5, 2].length) (baseStart_7345609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345609 prefixEnd_7345609 := by exact prefixLift 7345609
  have htrace : WordTrace (prefixWord ++ tailWord_7345609) baseStart_7345609 baseEnd_7345609 := by
    simpa [prefixWord, tailWord_7345609, baseEnd_7345609] using wordTrace_append hprefix tailTrace_7345609
  have hstable : (prefixWord ++ tailWord_7345609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345609).length < 2 ^ (prefixWord ++ tailWord_7345609).sum := by decide
  have hdescent : baseEnd_7345609 < baseStart_7345609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345620 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_7345620 : Nat := 118140960795 + 7345620 * 2 ^ 59
def prefixEnd_7345620 : Nat := 4983230072969 + 3 ^ 40 * 7345620 * 2
def baseEnd_7345620 : Nat := 3771833765279655461668115

theorem tailTrace_7345620 : CollatzResearch.WordTrace tailWord_7345620 prefixEnd_7345620 3771833765279655461668115 := by
  unfold tailWord_7345620
  simp only [CollatzResearch.WordTrace]
  refine ⟨133958385824040373431357157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178611181098720497908476209 133958385824040373431357157)
  ·
    refine ⟨25117197342007570018379467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133958385824040373431357157 25117197342007570018379467)
    ·
      refine ⟨37675796013011355027569201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25117197342007570018379467 37675796013011355027569201)
      ·
        refine ⟨28256847009758516270676901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37675796013011355027569201 28256847009758516270676901)
        ·
          refine ⟨5298158814329721800751919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28256847009758516270676901 5298158814329721800751919)
          ·
            refine ⟨7947238221494582701127879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5298158814329721800751919 7947238221494582701127879)
            ·
              refine ⟨11920857332241874051691819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7947238221494582701127879 11920857332241874051691819)
              ·
                refine ⟨17881285998362811077537729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11920857332241874051691819 17881285998362811077537729)
                ·
                  refine ⟨13410964498772108308153297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17881285998362811077537729 13410964498772108308153297)
                  ·
                    refine ⟨10058223374079081231114973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13410964498772108308153297 10058223374079081231114973)
                    ·
                      refine ⟨3771833765279655461668115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10058223374079081231114973 3771833765279655461668115)
                      ·
                        rfl

theorem cell23_7345620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_7345620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345620 prefixEnd_7345620 := by exact prefixLift 7345620
  have htrace : WordTrace (prefixWord ++ tailWord_7345620) baseStart_7345620 baseEnd_7345620 := by
    simpa [prefixWord, tailWord_7345620, baseEnd_7345620] using wordTrace_append hprefix tailTrace_7345620
  have hstable : (prefixWord ++ tailWord_7345620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345620).length < 2 ^ (prefixWord ++ tailWord_7345620).sum := by decide
  have hdescent : baseEnd_7345620 < baseStart_7345620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345626 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2]
def baseStart_7345626 : Nat := 118140960795 + 7345626 * 2 ^ 59
def prefixEnd_7345626 : Nat := 4983230072969 + 3 ^ 40 * 7345626 * 2
def baseEnd_7345626 : Nat := 3771836846163582438193087

theorem tailTrace_7345626 : CollatzResearch.WordTrace tailWord_7345626 prefixEnd_7345626 3771836846163582438193087 := by
  unfold tailWord_7345626
  simp only [CollatzResearch.WordTrace]
  refine ⟨66979247621514752471858183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178611326990706006591621821 66979247621514752471858183)
  ·
    refine ⟨100468871432272128707787275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66979247621514752471858183 100468871432272128707787275)
    ·
      refine ⟨150703307148408193061680913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100468871432272128707787275 150703307148408193061680913)
      ·
        refine ⟨113027480361306144796260685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150703307148408193061680913 113027480361306144796260685)
        ·
          refine ⟨42385305135489804298597757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113027480361306144796260685 42385305135489804298597757)
          ·
            refine ⟨15894489425808676611974159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42385305135489804298597757 15894489425808676611974159)
            ·
              refine ⟨23841734138713014917961239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15894489425808676611974159 23841734138713014917961239)
              ·
                refine ⟨35762601208069522376941859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23841734138713014917961239 35762601208069522376941859)
                ·
                  refine ⟨53643901812104283565412789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35762601208069522376941859 53643901812104283565412789)
                  ·
                    refine ⟨5029115794884776584257449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53643901812104283565412789 5029115794884776584257449)
                    ·
                      refine ⟨3771836846163582438193087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5029115794884776584257449 3771836846163582438193087)
                      ·
                        rfl

theorem cell23_7345626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_7345626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345626 prefixEnd_7345626 := by exact prefixLift 7345626
  have htrace : WordTrace (prefixWord ++ tailWord_7345626) baseStart_7345626 baseEnd_7345626 := by
    simpa [prefixWord, tailWord_7345626, baseEnd_7345626] using wordTrace_append hprefix tailTrace_7345626
  have hstable : (prefixWord ++ tailWord_7345626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345626).length < 2 ^ (prefixWord ++ tailWord_7345626).sum := by decide
  have hdescent : baseEnd_7345626 < baseStart_7345626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345632 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 3, 6]
def baseStart_7345632 : Nat := 118140960795 + 7345632 * 2 ^ 59
def prefixEnd_7345632 : Nat := 4983230072969 + 3 ^ 40 * 7345632 * 2
def baseEnd_7345632 : Nat := 1257279975682503138239353

theorem tailTrace_7345632 : CollatzResearch.WordTrace tailWord_7345632 prefixEnd_7345632 1257279975682503138239353 := by
  unfold tailWord_7345632
  simp only [CollatzResearch.WordTrace]
  refine ⟨133958604662018636456075575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178611472882691515274767433 133958604662018636456075575)
  ·
    refine ⟨200937906993027954684113363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133958604662018636456075575 200937906993027954684113363)
    ·
      refine ⟨301406860489541932026170045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200937906993027954684113363 301406860489541932026170045)
      ·
        refine ⟨113027572683578224509813767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301406860489541932026170045 113027572683578224509813767)
        ·
          refine ⟨169541359025367336764720651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113027572683578224509813767 169541359025367336764720651)
          ·
            refine ⟨254312038538051005147080977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169541359025367336764720651 254312038538051005147080977)
            ·
              refine ⟨190734028903538253860310733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254312038538051005147080977 190734028903538253860310733)
              ·
                refine ⟨71525260838826845197616525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190734028903538253860310733 71525260838826845197616525)
                ·
                  refine ⟨26821972814560066949106197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71525260838826845197616525 26821972814560066949106197)
                  ·
                    refine ⟨1257279975682503138239353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26821972814560066949106197 1257279975682503138239353)
                    ·
                      rfl

theorem cell23_7345632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_7345632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345632 prefixEnd_7345632 := by exact prefixLift 7345632
  have htrace : WordTrace (prefixWord ++ tailWord_7345632) baseStart_7345632 baseEnd_7345632 := by
    simpa [prefixWord, tailWord_7345632, baseEnd_7345632] using wordTrace_append hprefix tailTrace_7345632
  have hstable : (prefixWord ++ tailWord_7345632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345632).length < 2 ^ (prefixWord ++ tailWord_7345632).sum := by decide
  have hdescent : baseEnd_7345632 < baseStart_7345632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345633 : List Nat := [1, 2, 3, 1, 2, 3, 1, 5, 1, 1, 3]
def baseStart_7345633 : Nat := 118140960795 + 7345633 * 2 ^ 59
def prefixEnd_7345633 : Nat := 4983230072969 + 3 ^ 40 * 7345633 * 2
def baseEnd_7345633 : Nat := 3771840440528163910805555

theorem tailTrace_7345633 : CollatzResearch.WordTrace tailWord_7345633 prefixEnd_7345633 3771840440528163910805555 := by
  unfold tailWord_7345633
  simp only [CollatzResearch.WordTrace]
  refine ⟨267917245797033650082937553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178611497198022433388625035 267917245797033650082937553)
  ·
    refine ⟨200937934347775237562203165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267917245797033650082937553 200937934347775237562203165)
    ·
      refine ⟨75351725380415714085826187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200937934347775237562203165 75351725380415714085826187)
      ·
        refine ⟨113027588070623571128739281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75351725380415714085826187 113027588070623571128739281)
        ·
          refine ⟨84770691052967678346554461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113027588070623571128739281 84770691052967678346554461)
          ·
            refine ⟨31789009144862879379957923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84770691052967678346554461 31789009144862879379957923)
            ·
              refine ⟨47683513717294319069936885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31789009144862879379957923 47683513717294319069936885)
              ·
                refine ⟨4470329410996342412806583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47683513717294319069936885 4470329410996342412806583)
                ·
                  refine ⟨6705494116494513619209875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470329410996342412806583 6705494116494513619209875)
                  ·
                    refine ⟨10058241174741770428814813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6705494116494513619209875 10058241174741770428814813)
                    ·
                      refine ⟨3771840440528163910805555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10058241174741770428814813 3771840440528163910805555)
                      ·
                        rfl

theorem cell23_7345633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_7345633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345633 prefixEnd_7345633 := by exact prefixLift 7345633
  have htrace : WordTrace (prefixWord ++ tailWord_7345633) baseStart_7345633 baseEnd_7345633 := by
    simpa [prefixWord, tailWord_7345633, baseEnd_7345633] using wordTrace_append hprefix tailTrace_7345633
  have hstable : (prefixWord ++ tailWord_7345633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345633).length < 2 ^ (prefixWord ++ tailWord_7345633).sum := by decide
  have hdescent : baseEnd_7345633 < baseStart_7345633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345650 : List Nat := [3, 2, 1, 4, 1, 1, 2, 4, 1, 1, 3]
def baseStart_7345650 : Nat := 118140960795 + 7345650 * 2 ^ 59
def prefixEnd_7345650 : Nat := 4983230072969 + 3 ^ 40 * 7345650 * 2
def baseEnd_7345650 : Nat := 3771849169699290344292977

theorem tailTrace_7345650 : CollatzResearch.WordTrace tailWord_7345650 prefixEnd_7345650 3771849169699290344292977 := by
  unfold tailWord_7345650
  simp only [CollatzResearch.WordTrace]
  refine ⟨66979466459493015496576601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178611910558648041324204269 66979466459493015496576601)
  ·
    refine ⟨50234599844619761622432451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66979466459493015496576601 50234599844619761622432451)
    ·
      refine ⟨75351899766929642433648677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50234599844619761622432451 75351899766929642433648677)
      ·
        refine ⟨14128481206299307956309127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75351899766929642433648677 14128481206299307956309127)
        ·
          refine ⟨21192721809448961934463691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14128481206299307956309127 21192721809448961934463691)
          ·
            refine ⟨31789082714173442901695537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21192721809448961934463691 31789082714173442901695537)
            ·
              refine ⟨23841812035630082176271653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31789082714173442901695537 23841812035630082176271653)
              ·
                refine ⟨4470339756680640408050935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23841812035630082176271653 4470339756680640408050935)
                ·
                  refine ⟨6705509635020960612076403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470339756680640408050935 6705509635020960612076403)
                  ·
                    refine ⟨10058264452531440918114605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6705509635020960612076403 10058264452531440918114605)
                    ·
                      refine ⟨3771849169699290344292977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10058264452531440918114605 3771849169699290344292977)
                      ·
                        rfl

theorem cell23_7345650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_7345650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345650 prefixEnd_7345650 := by exact prefixLift 7345650
  have htrace : WordTrace (prefixWord ++ tailWord_7345650) baseStart_7345650 baseEnd_7345650 := by
    simpa [prefixWord, tailWord_7345650, baseEnd_7345650] using wordTrace_append hprefix tailTrace_7345650
  have hstable : (prefixWord ++ tailWord_7345650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345650).length < 2 ^ (prefixWord ++ tailWord_7345650).sum := by decide
  have hdescent : baseEnd_7345650 < baseStart_7345650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345684 : List Nat := [2, 4, 3, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_7345684 : Nat := 118140960795 + 7345684 * 2 ^ 59
def prefixEnd_7345684 : Nat := 4983230072969 + 3 ^ 40 * 7345684 * 2
def baseEnd_7345684 : Nat := 3771866628041543211267821

theorem tailTrace_7345684 : CollatzResearch.WordTrace tailWord_7345684 prefixEnd_7345684 3771866628041543211267821 := by
  unfold tailWord_7345684
  simp only [CollatzResearch.WordTrace]
  refine ⟨133959552959924442896522053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178612737279899257195362737 133959552959924442896522053)
  ·
    refine ⟨25117416179985833043097885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133959552959924442896522053 25117416179985833043097885)
    ·
      refine ⟨9419031067494687391161707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25117416179985833043097885 9419031067494687391161707)
      ·
        refine ⟨14128546601242031086742561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9419031067494687391161707 14128546601242031086742561)
        ·
          refine ⟨10596409950931523315056921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14128546601242031086742561 10596409950931523315056921)
          ·
            refine ⟨7947307463198642486292691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10596409950931523315056921 7947307463198642486292691)
            ·
              refine ⟨11920961194797963729439037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7947307463198642486292691 11920961194797963729439037)
              ·
                refine ⟨4470360448049236398539639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11920961194797963729439037 4470360448049236398539639)
                ·
                  refine ⟨6705540672073854597809459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470360448049236398539639 6705540672073854597809459)
                  ·
                    refine ⟨10058311008110781896714189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6705540672073854597809459 10058311008110781896714189)
                    ·
                      refine ⟨3771866628041543211267821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10058311008110781896714189 3771866628041543211267821)
                      ·
                        rfl

theorem cell23_7345684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_7345684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345684 prefixEnd_7345684 := by exact prefixLift 7345684
  have htrace : WordTrace (prefixWord ++ tailWord_7345684) baseStart_7345684 baseEnd_7345684 := by
    simpa [prefixWord, tailWord_7345684, baseEnd_7345684] using wordTrace_append hprefix tailTrace_7345684
  have hstable : (prefixWord ++ tailWord_7345684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345684).length < 2 ^ (prefixWord ++ tailWord_7345684).sum := by decide
  have hdescent : baseEnd_7345684 < baseStart_7345684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345694 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7345694 : Nat := 118140960795 + 7345694 * 2 ^ 59
def prefixEnd_7345694 : Nat := 4983230072969 + 3 ^ 40 * 7345694 * 2
def baseEnd_7345694 : Nat := 3771871762848088172142775

theorem tailTrace_7345694 : CollatzResearch.WordTrace tailWord_7345694 prefixEnd_7345694 3771871762848088172142775 := by
  unfold tailWord_7345694
  simp only [CollatzResearch.WordTrace]
  refine ⟨33489933831226582187613517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178612980433208438333938757 33489933831226582187613517)
  ·
    refine ⟨12558725186709968320355069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33489933831226582187613517 12558725186709968320355069)
    ·
      refine ⟨4709521945016238120133151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12558725186709968320355069 4709521945016238120133151)
      ·
        refine ⟨7064282917524357180199727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4709521945016238120133151 7064282917524357180199727)
        ·
          refine ⟨10596424376286535770299591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7064282917524357180199727 10596424376286535770299591)
          ·
            refine ⟨15894636564429803655449387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10596424376286535770299591 15894636564429803655449387)
            ·
              refine ⟨23841954846644705483174081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15894636564429803655449387 23841954846644705483174081)
              ·
                refine ⟨17881466134983529112380561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23841954846644705483174081 17881466134983529112380561)
                ·
                  refine ⟨13411099601237646834285421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17881466134983529112380561 13411099601237646834285421)
                  ·
                    refine ⟨5029162350464117562857033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13411099601237646834285421 5029162350464117562857033)
                    ·
                      refine ⟨3771871762848088172142775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5029162350464117562857033 3771871762848088172142775)
                      ·
                        rfl

theorem cell23_7345694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7345694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345694 prefixEnd_7345694 := by exact prefixLift 7345694
  have htrace : WordTrace (prefixWord ++ tailWord_7345694) baseStart_7345694 baseEnd_7345694 := by
    simpa [prefixWord, tailWord_7345694, baseEnd_7345694] using wordTrace_append hprefix tailTrace_7345694
  have hstable : (prefixWord ++ tailWord_7345694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345694).length < 2 ^ (prefixWord ++ tailWord_7345694).sum := by decide
  have hdescent : baseEnd_7345694 < baseStart_7345694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345776 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 4]
def baseStart_7345776 : Nat := 118140960795 + 7345776 * 2 ^ 59
def prefixEnd_7345776 : Nat := 4983230072969 + 3 ^ 40 * 7345776 * 2
def baseEnd_7345776 : Nat := 3771913868261756851317397

theorem tailTrace_7345776 : CollatzResearch.WordTrace tailWord_7345776 prefixEnd_7345776 3771913868261756851317397 := by
  unfold tailWord_7345776
  simp only [CollatzResearch.WordTrace]
  refine ⟨133961230717757792752696591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178614974290343723670262121 133961230717757792752696591)
  ·
    refine ⟨200941846076636689129044887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133961230717757792752696591 200941846076636689129044887)
    ·
      refine ⟨301412769114955033693567331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200941846076636689129044887 301412769114955033693567331)
      ·
        refine ⟨452119153672432550540350997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301412769114955033693567331 452119153672432550540350997)
        ·
          refine ⟨21193085328395275806578953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 452119153672432550540350997 21193085328395275806578953)
          ·
            refine ⟨15894813996296456854934215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21193085328395275806578953 15894813996296456854934215)
            ·
              refine ⟨23842220994444685282401323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15894813996296456854934215 23842220994444685282401323)
              ·
                refine ⟨35763331491667027923601985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23842220994444685282401323 35763331491667027923601985)
                ·
                  refine ⟨26822498618750270942701489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35763331491667027923601985 26822498618750270942701489)
                  ·
                    refine ⟨20116873964062703207026117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26822498618750270942701489 20116873964062703207026117)
                    ·
                      refine ⟨3771913868261756851317397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20116873964062703207026117 3771913868261756851317397)
                      ·
                        rfl

theorem cell23_7345776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_7345776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345776 prefixEnd_7345776 := by exact prefixLift 7345776
  have htrace : WordTrace (prefixWord ++ tailWord_7345776) baseStart_7345776 baseEnd_7345776 := by
    simpa [prefixWord, tailWord_7345776, baseEnd_7345776] using wordTrace_append hprefix tailTrace_7345776
  have hstable : (prefixWord ++ tailWord_7345776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345776).length < 2 ^ (prefixWord ++ tailWord_7345776).sum := by decide
  have hdescent : baseEnd_7345776 < baseStart_7345776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345809 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_7345809 : Nat := 118140960795 + 7345809 * 2 ^ 59
def prefixEnd_7345809 : Nat := 4983230072969 + 3 ^ 40 * 7345809 * 2
def baseEnd_7345809 : Nat := 3771930813123355222204745

theorem tailTrace_7345809 : CollatzResearch.WordTrace tailWord_7345809 prefixEnd_7345809 3771930813123355222204745 := by
  unfold tailWord_7345809
  simp only [CollatzResearch.WordTrace]
  refine ⟨267923665044396032141344481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178615776696264021427562987 267923665044396032141344481)
  ·
    refine ⟨200942748783297024106008361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267923665044396032141344481 200942748783297024106008361)
    ·
      refine ⟨150707061587472768079506271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200942748783297024106008361 150707061587472768079506271)
      ·
        refine ⟨226060592381209152119259407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150707061587472768079506271 226060592381209152119259407)
        ·
          refine ⟨339090888571813728178889111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226060592381209152119259407 339090888571813728178889111)
          ·
            refine ⟨508636332857720592268333667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339090888571813728178889111 508636332857720592268333667)
            ·
              refine ⟨762954499286580888402500501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508636332857720592268333667 762954499286580888402500501)
              ·
                refine ⟨35763492154058479143867211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 762954499286580888402500501 35763492154058479143867211)
                ·
                  refine ⟨53645238231087718715800817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35763492154058479143867211 53645238231087718715800817)
                  ·
                    refine ⟨40233928673315789036850613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53645238231087718715800817 40233928673315789036850613)
                    ·
                      refine ⟨3771930813123355222204745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40233928673315789036850613 3771930813123355222204745)
                      ·
                        rfl

theorem cell23_7345809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_7345809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345809 prefixEnd_7345809 := by exact prefixLift 7345809
  have htrace : WordTrace (prefixWord ++ tailWord_7345809) baseStart_7345809 baseEnd_7345809 := by
    simpa [prefixWord, tailWord_7345809, baseEnd_7345809] using wordTrace_append hprefix tailTrace_7345809
  have hstable : (prefixWord ++ tailWord_7345809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345809).length < 2 ^ (prefixWord ++ tailWord_7345809).sum := by decide
  have hdescent : baseEnd_7345809 < baseStart_7345809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345856 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 3]
def baseStart_7345856 : Nat := 118140960795 + 7345856 * 2 ^ 59
def prefixEnd_7345856 : Nat := 4983230072969 + 3 ^ 40 * 7345856 * 2
def baseEnd_7345856 : Nat := 3771954946714116538317029

theorem tailTrace_7345856 : CollatzResearch.WordTrace tailWord_7345856 prefixEnd_7345856 3771954946714116538317029 := by
  unfold tailWord_7345856
  simp only [CollatzResearch.WordTrace]
  refine ⟨133962689637612879584152711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178616919516817172778870281 133962689637612879584152711)
  ·
    refine ⟨200944034456419319376229067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133962689637612879584152711 200944034456419319376229067)
    ·
      refine ⟨301416051684628979064343601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200944034456419319376229067 301416051684628979064343601)
      ·
        refine ⟨226062038763471734298257701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301416051684628979064343601 226062038763471734298257701)
        ·
          refine ⟨42386632268150950180923319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226062038763471734298257701 42386632268150950180923319)
          ·
            refine ⟨63579948402226425271384979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42386632268150950180923319 63579948402226425271384979)
            ·
              refine ⟨95369922603339637907077469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63579948402226425271384979 95369922603339637907077469)
              ·
                refine ⟨35763720976252364215154051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95369922603339637907077469 35763720976252364215154051)
                ·
                  refine ⟨53645581464378546322731077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35763720976252364215154051 53645581464378546322731077)
                  ·
                    refine ⟨10058546524570977435512077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53645581464378546322731077 10058546524570977435512077)
                    ·
                      refine ⟨3771954946714116538317029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10058546524570977435512077 3771954946714116538317029)
                      ·
                        rfl

theorem cell23_7345856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_7345856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345856 prefixEnd_7345856 := by exact prefixLift 7345856
  have htrace : WordTrace (prefixWord ++ tailWord_7345856) baseStart_7345856 baseEnd_7345856 := by
    simpa [prefixWord, tailWord_7345856, baseEnd_7345856] using wordTrace_append hprefix tailTrace_7345856
  have hstable : (prefixWord ++ tailWord_7345856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345856).length < 2 ^ (prefixWord ++ tailWord_7345856).sum := by decide
  have hdescent : baseEnd_7345856 < baseStart_7345856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345873 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 2, 2, 3]
def baseStart_7345873 : Nat := 118140960795 + 7345873 * 2 ^ 59
def prefixEnd_7345873 : Nat := 4983230072969 + 3 ^ 40 * 7345873 * 2
def baseEnd_7345873 : Nat := 3771963675885242971804451

theorem tailTrace_7345873 : CollatzResearch.WordTrace tailWord_7345873 prefixEnd_7345873 3771963675885242971804451 := by
  unfold tailWord_7345873
  simp only [CollatzResearch.WordTrace]
  refine ⟨267925999316164171071674273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178617332877442780714449515 267925999316164171071674273)
  ·
    refine ⟨200944499487123128303755705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267925999316164171071674273 200944499487123128303755705)
    ·
      refine ⟨150708374615342346227816779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200944499487123128303755705 150708374615342346227816779)
      ·
        refine ⟨226062561923013519341725169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150708374615342346227816779 226062561923013519341725169)
        ·
          refine ⟨169546921442260139506293877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226062561923013519341725169 169546921442260139506293877)
          ·
            refine ⟨15895023885211888078715051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169546921442260139506293877 15895023885211888078715051)
            ·
              refine ⟨23842535827817832118072577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15895023885211888078715051 23842535827817832118072577)
              ·
                refine ⟨17881901870863374088554433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23842535827817832118072577 17881901870863374088554433)
                ·
                  refine ⟨13411426403147530566415825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17881901870863374088554433 13411426403147530566415825)
                  ·
                    refine ⟨10058569802360647924811869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13411426403147530566415825 10058569802360647924811869)
                    ·
                      refine ⟨3771963675885242971804451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10058569802360647924811869 3771963675885242971804451)
                      ·
                        rfl

theorem cell23_7345873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_7345873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345873 prefixEnd_7345873 := by exact prefixLift 7345873
  have htrace : WordTrace (prefixWord ++ tailWord_7345873) baseStart_7345873 baseEnd_7345873 := by
    simpa [prefixWord, tailWord_7345873, baseEnd_7345873] using wordTrace_append hprefix tailTrace_7345873
  have hstable : (prefixWord ++ tailWord_7345873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345873).length < 2 ^ (prefixWord ++ tailWord_7345873).sum := by decide
  have hdescent : baseEnd_7345873 < baseStart_7345873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345903 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 5, 1, 3]
def baseStart_7345903 : Nat := 118140960795 + 7345903 * 2 ^ 59
def prefixEnd_7345903 : Nat := 4983230072969 + 3 ^ 40 * 7345903 * 2
def baseEnd_7345903 : Nat := 3771979080304877854429313

theorem tailTrace_7345903 : CollatzResearch.WordTrace tailWord_7345903 prefixEnd_7345903 3771979080304877854429313 := by
  unfold tailWord_7345903
  simp only [CollatzResearch.WordTrace]
  refine ⟨267927093506055486195266363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178618062337370324130177575 267927093506055486195266363)
  ·
    refine ⟨401890640259083229292899545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267927093506055486195266363 401890640259083229292899545)
    ·
      refine ⟨301417980194312421969674659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401890640259083229292899545 301417980194312421969674659)
      ·
        refine ⟨452126970291468632954511989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301417980194312421969674659 452126970291468632954511989)
        ·
          refine ⟨42386903464825184339485499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 452126970291468632954511989 42386903464825184339485499)
          ·
            refine ⟨63580355197237776509228249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42386903464825184339485499 63580355197237776509228249)
            ·
              refine ⟨47685266397928332381921187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63580355197237776509228249 47685266397928332381921187)
              ·
                refine ⟨71527899596892498572881781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47685266397928332381921187 71527899596892498572881781)
                ·
                  refine ⟨6705740587208671741207667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71527899596892498572881781 6705740587208671741207667)
                  ·
                    refine ⟨10058610880813007611811501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6705740587208671741207667 10058610880813007611811501)
                    ·
                      refine ⟨3771979080304877854429313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10058610880813007611811501 3771979080304877854429313)
                      ·
                        rfl

theorem cell23_7345903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 1, 3].length) (baseStart_7345903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345903 prefixEnd_7345903 := by exact prefixLift 7345903
  have htrace : WordTrace (prefixWord ++ tailWord_7345903) baseStart_7345903 baseEnd_7345903 := by
    simpa [prefixWord, tailWord_7345903, baseEnd_7345903] using wordTrace_append hprefix tailTrace_7345903
  have hstable : (prefixWord ++ tailWord_7345903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345903).length < 2 ^ (prefixWord ++ tailWord_7345903).sum := by decide
  have hdescent : baseEnd_7345903 < baseStart_7345903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345930 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2]
def baseStart_7345930 : Nat := 118140960795 + 7345930 * 2 ^ 59
def prefixEnd_7345930 : Nat := 4983230072969 + 3 ^ 40 * 7345930 * 2
def baseEnd_7345930 : Nat := 3771992944282549248791689

theorem tailTrace_7345930 : CollatzResearch.WordTrace tailWord_7345930 prefixEnd_7345930 3771992944282549248791689 := by
  unfold tailWord_7345930
  simp only [CollatzResearch.WordTrace]
  refine ⟨66982019569239417451624811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178618718851305113204332829 66982019569239417451624811)
  ·
    refine ⟨100473029353859126177437217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66982019569239417451624811 100473029353859126177437217)
    ·
      refine ⟨75354772015394344633077913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100473029353859126177437217 75354772015394344633077913)
      ·
        refine ⟨56516079011545758474808435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75354772015394344633077913 56516079011545758474808435)
        ·
          refine ⟨84774118517318637712212653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56516079011545758474808435 84774118517318637712212653)
          ·
            refine ⟨31790294443994489142079745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84774118517318637712212653 31790294443994489142079745)
            ·
              refine ⟨23842720832995866856559809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31790294443994489142079745 23842720832995866856559809)
              ·
                refine ⟨17882040624746900142419857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23842720832995866856559809 17882040624746900142419857)
                ·
                  refine ⟨13411530468560175106814893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17882040624746900142419857 13411530468560175106814893)
                  ·
                    refine ⟨5029323925710065665055585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13411530468560175106814893 5029323925710065665055585)
                    ·
                      refine ⟨3771992944282549248791689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5029323925710065665055585 3771992944282549248791689)
                      ·
                        rfl

theorem cell23_7345930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_7345930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345930 prefixEnd_7345930 := by exact prefixLift 7345930
  have htrace : WordTrace (prefixWord ++ tailWord_7345930) baseStart_7345930 baseEnd_7345930 := by
    simpa [prefixWord, tailWord_7345930, baseEnd_7345930] using wordTrace_append hprefix tailTrace_7345930
  have hstable : (prefixWord ++ tailWord_7345930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345930).length < 2 ^ (prefixWord ++ tailWord_7345930).sum := by decide
  have hdescent : baseEnd_7345930 < baseStart_7345930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345943 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_7345943 : Nat := 118140960795 + 7345943 * 2 ^ 59
def prefixEnd_7345943 : Nat := 4983230072969 + 3 ^ 40 * 7345943 * 2
def baseEnd_7345943 : Nat := 3771999619531057697929129

theorem tailTrace_7345943 : CollatzResearch.WordTrace tailWord_7345943 prefixEnd_7345943 3771999619531057697929129 := by
  unfold tailWord_7345943
  simp only [CollatzResearch.WordTrace]
  refine ⟨267928552425910573026722483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178619034950607048684481655 267928552425910573026722483)
  ·
    refine ⟨401892828638865859540083725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267928552425910573026722483 401892828638865859540083725)
    ·
      refine ⟨150709810739574697327531397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401892828638865859540083725 150709810739574697327531397)
      ·
        refine ⟨28258089513670255748912137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150709810739574697327531397 28258089513670255748912137)
        ·
          refine ⟨21193567135252691811684103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28258089513670255748912137 21193567135252691811684103)
          ·
            refine ⟨31790350702879037717526155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21193567135252691811684103 31790350702879037717526155)
            ·
              refine ⟨47685526054318556576289233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31790350702879037717526155 47685526054318556576289233)
              ·
                refine ⟨35764144540738917432216925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47685526054318556576289233 35764144540738917432216925)
                ·
                  refine ⟨13411554202777094037081347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35764144540738917432216925 13411554202777094037081347)
                  ·
                    refine ⟨20117331304165641055622021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13411554202777094037081347 20117331304165641055622021)
                    ·
                      refine ⟨3771999619531057697929129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20117331304165641055622021 3771999619531057697929129)
                      ·
                        rfl

theorem cell23_7345943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_7345943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345943 prefixEnd_7345943 := by exact prefixLift 7345943
  have htrace : WordTrace (prefixWord ++ tailWord_7345943) baseStart_7345943 baseEnd_7345943 := by
    simpa [prefixWord, tailWord_7345943, baseEnd_7345943] using wordTrace_append hprefix tailTrace_7345943
  have hstable : (prefixWord ++ tailWord_7345943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345943).length < 2 ^ (prefixWord ++ tailWord_7345943).sum := by decide
  have hdescent : baseEnd_7345943 < baseStart_7345943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345953 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 1, 6]
def baseStart_7345953 : Nat := 118140960795 + 7345953 * 2 ^ 59
def prefixEnd_7345953 : Nat := 4983230072969 + 3 ^ 40 * 7345953 * 2
def baseEnd_7345953 : Nat := 1257334918112534219601361

theorem tailTrace_7345953 : CollatzResearch.WordTrace tailWord_7345953 prefixEnd_7345953 1257334918112534219601361 := by
  unfold tailWord_7345953
  simp only [CollatzResearch.WordTrace]
  refine ⟨267928917155874344734586513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178619278103916229823057675 267928917155874344734586513)
  ·
    refine ⟨200946687866905758550939885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267928917155874344734586513 200946687866905758550939885)
    ·
      refine ⟨75355007950089659456602457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200946687866905758550939885 75355007950089659456602457)
      ·
        refine ⟨56516255962567244592451843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75355007950089659456602457 56516255962567244592451843)
        ·
          refine ⟨84774383943850866888677765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56516255962567244592451843 84774383943850866888677765)
          ·
            refine ⟨15895196989472037541627081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84774383943850866888677765 15895196989472037541627081)
            ·
              refine ⟨11921397742104028156220311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15895196989472037541627081 11921397742104028156220311)
              ·
                refine ⟨17882096613156042234330467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11921397742104028156220311 17882096613156042234330467)
                ·
                  refine ⟨26823144919734063351495701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17882096613156042234330467 26823144919734063351495701)
                  ·
                    refine ⟨1257334918112534219601361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26823144919734063351495701 1257334918112534219601361)
                    ·
                      rfl

theorem cell23_7345953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_7345953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345953 prefixEnd_7345953 := by exact prefixLift 7345953
  have htrace : WordTrace (prefixWord ++ tailWord_7345953) baseStart_7345953 baseEnd_7345953 := by
    simpa [prefixWord, tailWord_7345953, baseEnd_7345953] using wordTrace_append hprefix tailTrace_7345953
  have hstable : (prefixWord ++ tailWord_7345953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345953).length < 2 ^ (prefixWord ++ tailWord_7345953).sum := by decide
  have hdescent : baseEnd_7345953 < baseStart_7345953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345974 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_7345974 : Nat := 118140960795 + 7345974 * 2 ^ 59
def prefixEnd_7345974 : Nat := 4983230072969 + 3 ^ 40 * 7345974 * 2
def baseEnd_7345974 : Nat := 1257338512477115692213829

theorem tailTrace_7345974 : CollatzResearch.WordTrace tailWord_7345974 prefixEnd_7345974 1257338512477115692213829 := by
  unfold tailWord_7345974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16745605193049891582568811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178619788725865510214067317 16745605193049891582568811)
  ·
    refine ⟨25118407789574837373853217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16745605193049891582568811 25118407789574837373853217)
    ·
      refine ⟨18838805842181128030389913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25118407789574837373853217 18838805842181128030389913)
      ·
        refine ⟨14129104381635846022792435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18838805842181128030389913 14129104381635846022792435)
        ·
          refine ⟨21193656572453769034188653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14129104381635846022792435 21193656572453769034188653)
          ·
            refine ⟨7947621214670163387820745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21193656572453769034188653 7947621214670163387820745)
            ·
              refine ⟨5960715911002622540865559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7947621214670163387820745 5960715911002622540865559)
              ·
                refine ⟨8941073866503933811298339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960715911002622540865559 8941073866503933811298339)
                ·
                  refine ⟨13411610799755900716947509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8941073866503933811298339 13411610799755900716947509)
                  ·
                    refine ⟨1257338512477115692213829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13411610799755900716947509 1257338512477115692213829)
                    ·
                      rfl

theorem cell23_7345974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_7345974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345974 prefixEnd_7345974 := by exact prefixLift 7345974
  have htrace : WordTrace (prefixWord ++ tailWord_7345974) baseStart_7345974 baseEnd_7345974 := by
    simpa [prefixWord, tailWord_7345974, baseEnd_7345974] using wordTrace_append hprefix tailTrace_7345974
  have hstable : (prefixWord ++ tailWord_7345974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345974).length < 2 ^ (prefixWord ++ tailWord_7345974).sum := by decide
  have hdescent : baseEnd_7345974 < baseStart_7345974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345977 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7345977 : Nat := 118140960795 + 7345977 * 2 ^ 59
def prefixEnd_7345977 : Nat := 4983230072969 + 3 ^ 40 * 7345977 * 2
def baseEnd_7345977 : Nat := 3772017077873310564903973

theorem tailTrace_7345977 : CollatzResearch.WordTrace tailWord_7345977 prefixEnd_7345977 3772017077873310564903973 := by
  unfold tailWord_7345977
  simp only [CollatzResearch.WordTrace]
  refine ⟨267929792507787396833460185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178619861671858264555640123 267929792507787396833460185)
  ·
    refine ⟨200947344380840547625095139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267929792507787396833460185 200947344380840547625095139)
    ·
      refine ⟨301421016571260821437642709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200947344380840547625095139 301421016571260821437642709)
      ·
        refine ⟨7064555075888925502444751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 301421016571260821437642709 7064555075888925502444751)
        ·
          refine ⟨10596832613833388253667127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7064555075888925502444751 10596832613833388253667127)
          ·
            refine ⟨15895248920750082380500691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10596832613833388253667127 15895248920750082380500691)
            ·
              refine ⟨23842873381125123570751037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15895248920750082380500691 23842873381125123570751037)
              ·
                refine ⟨8941077517921921339031639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23842873381125123570751037 8941077517921921339031639)
                ·
                  refine ⟨13411616276882882008547459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8941077517921921339031639 13411616276882882008547459)
                  ·
                    refine ⟨20117424415324323012821189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13411616276882882008547459 20117424415324323012821189)
                    ·
                      refine ⟨3772017077873310564903973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20117424415324323012821189 3772017077873310564903973)
                      ·
                        rfl

theorem cell23_7345977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7345977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7345977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7345977 prefixEnd_7345977 := by exact prefixLift 7345977
  have htrace : WordTrace (prefixWord ++ tailWord_7345977) baseStart_7345977 baseEnd_7345977 := by
    simpa [prefixWord, tailWord_7345977, baseEnd_7345977] using wordTrace_append hprefix tailTrace_7345977
  have hstable : (prefixWord ++ tailWord_7345977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345977).length < 2 ^ (prefixWord ++ tailWord_7345977).sum := by decide
  have hdescent : baseEnd_7345977 < baseStart_7345977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346007 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 1, 2, 4]
def baseStart_7346007 : Nat := 118140960795 + 7346007 * 2 ^ 59
def prefixEnd_7346007 : Nat := 4983230072969 + 3 ^ 40 * 7346007 * 2
def baseEnd_7346007 : Nat := 3772032482292945447528835

theorem tailTrace_7346007 : CollatzResearch.WordTrace tailWord_7346007 prefixEnd_7346007 3772032482292945447528835 := by
  unfold tailWord_7346007
  simp only [CollatzResearch.WordTrace]
  refine ⟨267930886697678711957052275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178620591131785807971368183 267930886697678711957052275)
  ·
    refine ⟨401896330046518067935578413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267930886697678711957052275 401896330046518067935578413)
    ·
      refine ⟨150711123767444275475841905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401896330046518067935578413 150711123767444275475841905)
      ·
        refine ⟨113033342825583206606881429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150711123767444275475841905 113033342825583206606881429)
        ·
          refine ⟨5298437944949212809697567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113033342825583206606881429 5298437944949212809697567)
          ·
            refine ⟨7947656917423819214546351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5298437944949212809697567 7947656917423819214546351)
            ·
              refine ⟨11921485376135728821819527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7947656917423819214546351 11921485376135728821819527)
              ·
                refine ⟨17882228064203593232729291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11921485376135728821819527 17882228064203593232729291)
                ·
                  refine ⟨26823342096305389849093937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17882228064203593232729291 26823342096305389849093937)
                  ·
                    refine ⟨20117506572229042386820453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26823342096305389849093937 20117506572229042386820453)
                    ·
                      refine ⟨3772032482292945447528835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20117506572229042386820453 3772032482292945447528835)
                      ·
                        rfl

theorem cell23_7346007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_7346007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346007 prefixEnd_7346007 := by exact prefixLift 7346007
  have htrace : WordTrace (prefixWord ++ tailWord_7346007) baseStart_7346007 baseEnd_7346007 := by
    simpa [prefixWord, tailWord_7346007, baseEnd_7346007] using wordTrace_append hprefix tailTrace_7346007
  have hstable : (prefixWord ++ tailWord_7346007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346007).length < 2 ^ (prefixWord ++ tailWord_7346007).sum := by decide
  have hdescent : baseEnd_7346007 < baseStart_7346007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
