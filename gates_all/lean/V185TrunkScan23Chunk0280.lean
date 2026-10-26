import V185TrunkScan23Chunk0279

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1655665 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_1655665 : Nat := 118140960795 + 1655665 * 2 ^ 59
def prefixEnd_1655665 : Nat := 4983230072969 + 3 ^ 40 * 1655665 * 2
def baseEnd_1655665 : Nat := 850151947826369936773241

theorem tailTrace_1655665 : CollatzResearch.WordTrace tailWord_1655665 prefixEnd_1655665 850151947826369936773241 := by
  unfold tailWord_1655665
  simp only [CollatzResearch.WordTrace]
  refine ⟨60387063546815944915032449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40258042364543963276688299 60387063546815944915032449)
  ·
    refine ⟨45290297660111958686274337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60387063546815944915032449 45290297660111958686274337)
    ·
      refine ⟨33967723245083969014705753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45290297660111958686274337 33967723245083969014705753)
      ·
        refine ⟨25475792433812976761029315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33967723245083969014705753 25475792433812976761029315)
        ·
          refine ⟨38213688650719465141543973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25475792433812976761029315 38213688650719465141543973)
          ·
            refine ⟨7165066622009899714039495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38213688650719465141543973 7165066622009899714039495)
            ·
              refine ⟨10747599933014849571059243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7165066622009899714039495 10747599933014849571059243)
              ·
                refine ⟨16121399899522274356588865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10747599933014849571059243 16121399899522274356588865)
                ·
                  refine ⟨12091049924641705767441649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16121399899522274356588865 12091049924641705767441649)
                  ·
                    refine ⟨9068287443481279325581237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12091049924641705767441649 9068287443481279325581237)
                    ·
                      refine ⟨850151947826369936773241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9068287443481279325581237 850151947826369936773241)
                      ·
                        rfl

theorem cell23_1655665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_1655665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655665 prefixEnd_1655665 := by exact prefixLift 1655665
  have htrace : WordTrace (prefixWord ++ tailWord_1655665) baseStart_1655665 baseEnd_1655665 := by
    simpa [prefixWord, tailWord_1655665, baseEnd_1655665] using wordTrace_append hprefix tailTrace_1655665
  have hstable : (prefixWord ++ tailWord_1655665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655665).length < 2 ^ (prefixWord ++ tailWord_1655665).sum := by decide
  have hdescent : baseEnd_1655665 < baseStart_1655665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655669 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1655669 : Nat := 118140960795 + 1655669 * 2 ^ 59
def prefixEnd_1655669 : Nat := 4983230072969 + 3 ^ 40 * 1655669 * 2
def baseEnd_1655669 : Nat := 850154001748987921123223

theorem tailTrace_1655669 : CollatzResearch.WordTrace tailWord_1655669 prefixEnd_1655669 850154001748987921123223 := by
  unfold tailWord_1655669
  simp only [CollatzResearch.WordTrace]
  refine ⟨60387209438801453598178061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40258139625867635732118707 60387209438801453598178061)
  ·
    refine ⟨22645203539550545099316773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60387209438801453598178061 22645203539550545099316773)
    ·
      refine ⟨4245975663665727206121895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22645203539550545099316773 4245975663665727206121895)
      ·
        refine ⟨6368963495498590809182843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4245975663665727206121895 6368963495498590809182843)
        ·
          refine ⟨9553445243247886213774265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6368963495498590809182843 9553445243247886213774265)
          ·
            refine ⟨7165083932435914660330699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9553445243247886213774265 7165083932435914660330699)
            ·
              refine ⟨10747625898653871990496049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7165083932435914660330699 10747625898653871990496049)
              ·
                refine ⟨8060719423990403992872037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10747625898653871990496049 8060719423990403992872037)
                ·
                  refine ⟨1511384891998200748663507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8060719423990403992872037 1511384891998200748663507)
                  ·
                    refine ⟨2267077337997301122995261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1511384891998200748663507 2267077337997301122995261)
                    ·
                      refine ⟨850154001748987921123223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2267077337997301122995261 850154001748987921123223)
                      ·
                        rfl

theorem cell23_1655669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1655669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655669 prefixEnd_1655669 := by exact prefixLift 1655669
  have htrace : WordTrace (prefixWord ++ tailWord_1655669) baseStart_1655669 baseEnd_1655669 := by
    simpa [prefixWord, tailWord_1655669, baseEnd_1655669] using wordTrace_append hprefix tailTrace_1655669
  have hstable : (prefixWord ++ tailWord_1655669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655669).length < 2 ^ (prefixWord ++ tailWord_1655669).sum := by decide
  have hdescent : baseEnd_1655669 < baseStart_1655669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655670 : List Nat := [5, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_1655670 : Nat := 118140960795 + 1655670 * 2 ^ 59
def prefixEnd_1655670 : Nat := 4983230072969 + 3 ^ 40 * 1655670 * 2
def baseEnd_1655670 : Nat := 850154515229642417210719

theorem tailTrace_1655670 : CollatzResearch.WordTrace tailWord_1655670 prefixEnd_1655670 850154515229642417210719 := by
  unfold tailWord_1655670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774202869487364423060279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40258163941198553845976309 3774202869487364423060279)
  ·
    refine ⟨5661304304231046634590419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3774202869487364423060279 5661304304231046634590419)
    ·
      refine ⟨8491956456346569951885629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5661304304231046634590419 8491956456346569951885629)
      ·
        refine ⟨3184483671129963731957111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8491956456346569951885629 3184483671129963731957111)
        ·
          refine ⟨4776725506694945597935667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184483671129963731957111 4776725506694945597935667)
          ·
            refine ⟨7165088260042418396903501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776725506694945597935667 7165088260042418396903501)
            ·
              refine ⟨2686908097515906898838813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7165088260042418396903501 2686908097515906898838813)
              ·
                refine ⟨1007590536568465087064555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2686908097515906898838813 1007590536568465087064555)
                ·
                  refine ⟨1511385804852697630596833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007590536568465087064555 1511385804852697630596833)
                  ·
                    refine ⟨1133539353639523222947625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1511385804852697630596833 1133539353639523222947625)
                    ·
                      refine ⟨850154515229642417210719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133539353639523222947625 850154515229642417210719)
                      ·
                        rfl

theorem cell23_1655670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_1655670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655670 prefixEnd_1655670 := by exact prefixLift 1655670
  have htrace : WordTrace (prefixWord ++ tailWord_1655670) baseStart_1655670 baseEnd_1655670 := by
    simpa [prefixWord, tailWord_1655670, baseEnd_1655670] using wordTrace_append hprefix tailTrace_1655670
  have hstable : (prefixWord ++ tailWord_1655670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655670).length < 2 ^ (prefixWord ++ tailWord_1655670).sum := by decide
  have hdescent : baseEnd_1655670 < baseStart_1655670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655679 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 1, 3, 2]
def baseStart_1655679 : Nat := 118140960795 + 1655679 * 2 ^ 59
def prefixEnd_1655679 : Nat := 4983230072969 + 3 ^ 40 * 1655679 * 2
def baseEnd_1655679 : Nat := 850159136555532881998177

theorem tailTrace_1655679 : CollatzResearch.WordTrace tailWord_1655679 prefixEnd_1655679 850159136555532881998177 := by
  unfold tailWord_1655679
  simp only [CollatzResearch.WordTrace]
  refine ⟨60387574168765225306042091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40258382779176816870694727 60387574168765225306042091)
  ·
    refine ⟨90581361253147837959063137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60387574168765225306042091 90581361253147837959063137)
    ·
      refine ⟨67936020939860878469297353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90581361253147837959063137 67936020939860878469297353)
      ·
        refine ⟨50952015704895658851973015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67936020939860878469297353 50952015704895658851973015)
        ·
          refine ⟨76428023557343488277959523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50952015704895658851973015 76428023557343488277959523)
          ·
            refine ⟨114642035336015232416939285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76428023557343488277959523 114642035336015232416939285)
            ·
              refine ⟨5373845406375714019544029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114642035336015232416939285 5373845406375714019544029)
              ·
                refine ⟨2015192027390892757329011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5373845406375714019544029 2015192027390892757329011)
                ·
                  refine ⟨3022788041086339135993517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015192027390892757329011 3022788041086339135993517)
                  ·
                    refine ⟨1133545515407377175997569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022788041086339135993517 1133545515407377175997569)
                    ·
                      refine ⟨850159136555532881998177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133545515407377175997569 850159136555532881998177)
                      ·
                        rfl

theorem cell23_1655679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 3, 2].length) (baseStart_1655679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655679 prefixEnd_1655679 := by exact prefixLift 1655679
  have htrace : WordTrace (prefixWord ++ tailWord_1655679) baseStart_1655679 baseEnd_1655679 := by
    simpa [prefixWord, tailWord_1655679, baseEnd_1655679] using wordTrace_append hprefix tailTrace_1655679
  have hstable : (prefixWord ++ tailWord_1655679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655679).length < 2 ^ (prefixWord ++ tailWord_1655679).sum := by decide
  have hdescent : baseEnd_1655679 < baseStart_1655679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655705 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 4]
def baseStart_1655705 : Nat := 118140960795 + 1655705 * 2 ^ 59
def prefixEnd_1655705 : Nat := 4983230072969 + 3 ^ 40 * 1655705 * 2
def baseEnd_1655705 : Nat := 850172487052549780273057

theorem tailTrace_1655705 : CollatzResearch.WordTrace tailWord_1655705 prefixEnd_1655705 850172487052549780273057 := by
  unfold tailWord_1655705
  simp only [CollatzResearch.WordTrace]
  refine ⟨60388522466671031746488569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40259014977780687830992379 60388522466671031746488569)
  ·
    refine ⟨45291391850003273809866427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60388522466671031746488569 45291391850003273809866427)
    ·
      refine ⟨67937087775004910714799641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45291391850003273809866427 67937087775004910714799641)
      ·
        refine ⟨50952815831253683036099731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67937087775004910714799641 50952815831253683036099731)
        ·
          refine ⟨76429223746880524554149597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50952815831253683036099731 76429223746880524554149597)
          ·
            refine ⟨28660958905080196707806099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76429223746880524554149597 28660958905080196707806099)
            ·
              refine ⟨42991438357620295061709149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28660958905080196707806099 42991438357620295061709149)
              ·
                refine ⟨16121789384107610648140931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42991438357620295061709149 16121789384107610648140931)
                ·
                  refine ⟨24182684076161415972211397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16121789384107610648140931 24182684076161415972211397)
                  ·
                    refine ⟨4534253264280265494789637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24182684076161415972211397 4534253264280265494789637)
                    ·
                      refine ⟨850172487052549780273057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4534253264280265494789637 850172487052549780273057)
                      ·
                        rfl

theorem cell23_1655705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_1655705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655705 prefixEnd_1655705 := by exact prefixLift 1655705
  have htrace : WordTrace (prefixWord ++ tailWord_1655705) baseStart_1655705 baseEnd_1655705 := by
    simpa [prefixWord, tailWord_1655705, baseEnd_1655705] using wordTrace_append hprefix tailTrace_1655705
  have hstable : (prefixWord ++ tailWord_1655705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655705).length < 2 ^ (prefixWord ++ tailWord_1655705).sum := by decide
  have hdescent : baseEnd_1655705 < baseStart_1655705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655709 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_1655709 : Nat := 118140960795 + 1655709 * 2 ^ 59
def prefixEnd_1655709 : Nat := 4983230072969 + 3 ^ 40 * 1655709 * 2
def baseEnd_1655709 : Nat := 850174540975167764623039

theorem tailTrace_1655709 : CollatzResearch.WordTrace tailWord_1655709 prefixEnd_1655709 850174540975167764623039 := by
  unfold tailWord_1655709
  simp only [CollatzResearch.WordTrace]
  refine ⟨60388668358656540429634181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40259112239104360286422787 60388668358656540429634181)
  ·
    refine ⟨11322875317248101330556409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60388668358656540429634181 11322875317248101330556409)
    ·
      refine ⟨8492156487936075997917307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11322875317248101330556409 8492156487936075997917307)
      ·
        refine ⟨12738234731904113996875961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8492156487936075997917307 12738234731904113996875961)
        ·
          refine ⟨9553676048928085497656971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12738234731904113996875961 9553676048928085497656971)
          ·
            refine ⟨14330514073392128246485457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9553676048928085497656971 14330514073392128246485457)
            ·
              refine ⟨10747885555044096184864093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14330514073392128246485457 10747885555044096184864093)
              ·
                refine ⟨4030457083141536069324035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10747885555044096184864093 4030457083141536069324035)
                ·
                  refine ⟨6045685624712304103986053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030457083141536069324035 6045685624712304103986053)
                  ·
                    refine ⟨1133566054633557019497385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6045685624712304103986053 1133566054633557019497385)
                    ·
                      refine ⟨850174540975167764623039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133566054633557019497385 850174540975167764623039)
                      ·
                        rfl

theorem cell23_1655709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_1655709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655709 prefixEnd_1655709 := by exact prefixLift 1655709
  have htrace : WordTrace (prefixWord ++ tailWord_1655709) baseStart_1655709 baseEnd_1655709 := by
    simpa [prefixWord, tailWord_1655709, baseEnd_1655709] using wordTrace_append hprefix tailTrace_1655709
  have hstable : (prefixWord ++ tailWord_1655709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655709).length < 2 ^ (prefixWord ++ tailWord_1655709).sum := by decide
  have hdescent : baseEnd_1655709 < baseStart_1655709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655713 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1655713 : Nat := 118140960795 + 1655713 * 2 ^ 59
def prefixEnd_1655713 : Nat := 4983230072969 + 3 ^ 40 * 1655713 * 2
def baseEnd_1655713 : Nat := 850176594897785748973021

theorem tailTrace_1655713 : CollatzResearch.WordTrace tailWord_1655713 prefixEnd_1655713 850176594897785748973021 := by
  unfold tailWord_1655713
  simp only [CollatzResearch.WordTrace]
  refine ⟨60388814250642049112779793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40259209500428032741853195 60388814250642049112779793)
  ·
    refine ⟨45291610687981536834584845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60388814250642049112779793 45291610687981536834584845)
    ·
      refine ⟨16984354007993076312969317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45291610687981536834584845 16984354007993076312969317)
      ·
        refine ⟨3184566376498701808681747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16984354007993076312969317 3184566376498701808681747)
        ·
          refine ⟨4776849564748052713022621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184566376498701808681747 4776849564748052713022621)
          ·
            refine ⟨1791318586780519767383483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4776849564748052713022621 1791318586780519767383483)
            ·
              refine ⟨2686977880170779651075225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791318586780519767383483 2686977880170779651075225)
              ·
                refine ⟨2015233410128084738306419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2686977880170779651075225 2015233410128084738306419)
                ·
                  refine ⟨3022850115192127107459629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015233410128084738306419 3022850115192127107459629)
                  ·
                    refine ⟨1133568793197047665297361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022850115192127107459629 1133568793197047665297361)
                    ·
                      refine ⟨850176594897785748973021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133568793197047665297361 850176594897785748973021)
                      ·
                        rfl

theorem cell23_1655713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1655713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655713 prefixEnd_1655713 := by exact prefixLift 1655713
  have htrace : WordTrace (prefixWord ++ tailWord_1655713) baseStart_1655713 baseEnd_1655713 := by
    simpa [prefixWord, tailWord_1655713, baseEnd_1655713] using wordTrace_append hprefix tailTrace_1655713
  have hstable : (prefixWord ++ tailWord_1655713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655713).length < 2 ^ (prefixWord ++ tailWord_1655713).sum := by decide
  have hdescent : baseEnd_1655713 < baseStart_1655713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655715 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 7]
def baseStart_1655715 : Nat := 118140960795 + 1655715 * 2 ^ 59
def prefixEnd_1655715 : Nat := 4983230072969 + 3 ^ 40 * 1655715 * 2
def baseEnd_1655715 : Nat := 94464180206566082349779

theorem tailTrace_1655715 : CollatzResearch.WordTrace tailWord_1655715 prefixEnd_1655715 94464180206566082349779 := by
  unfold tailWord_1655715
  simp only [CollatzResearch.WordTrace]
  refine ⟨60388887196634803454352599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40259258131089868969568399 60388887196634803454352599)
  ·
    refine ⟨90583330794952205181528899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60388887196634803454352599 90583330794952205181528899)
    ·
      refine ⟨135874996192428307772293349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90583330794952205181528899 135874996192428307772293349)
      ·
        refine ⟨25476561786080307707305003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135874996192428307772293349 25476561786080307707305003)
        ·
          refine ⟨38214842679120461560957505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25476561786080307707305003 38214842679120461560957505)
          ·
            refine ⟨28661132009340346170718129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38214842679120461560957505 28661132009340346170718129)
            ·
              refine ⟨21495849007005259628038597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28661132009340346170718129 21495849007005259628038597)
              ·
                refine ⟨4030471688813486180257237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21495849007005259628038597 4030471688813486180257237)
                ·
                  refine ⟨94464180206566082349779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4030471688813486180257237 94464180206566082349779)
                  ·
                    rfl

theorem cell23_1655715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 7].length) (baseStart_1655715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655715 prefixEnd_1655715 := by exact prefixLift 1655715
  have htrace : WordTrace (prefixWord ++ tailWord_1655715) baseStart_1655715 baseEnd_1655715 := by
    simpa [prefixWord, tailWord_1655715, baseEnd_1655715] using wordTrace_append hprefix tailTrace_1655715
  have hstable : (prefixWord ++ tailWord_1655715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655715).length < 2 ^ (prefixWord ++ tailWord_1655715).sum := by decide
  have hdescent : baseEnd_1655715 < baseStart_1655715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655792 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 7, 4]
def baseStart_1655792 : Nat := 118140960795 + 1655792 * 2 ^ 59
def prefixEnd_1655792 : Nat := 4983230072969 + 3 ^ 40 * 1655792 * 2
def baseEnd_1655792 : Nat := 283405719956496979961719

theorem tailTrace_1655792 : CollatzResearch.WordTrace tailWord_1655792 prefixEnd_1655792 283405719956496979961719 := by
  unfold tailWord_1655792
  simp only [CollatzResearch.WordTrace]
  refine ⟨30195847808677922802452815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40261130411570563736603753 30195847808677922802452815)
  ·
    refine ⟨45293771713016884203679223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30195847808677922802452815 45293771713016884203679223)
    ·
      refine ⟨67940657569525326305518835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45293771713016884203679223 67940657569525326305518835)
      ·
        refine ⟨101910986354287989458278253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67940657569525326305518835 101910986354287989458278253)
        ·
          refine ⟨38216619882857996046854345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101910986354287989458278253 38216619882857996046854345)
          ·
            refine ⟨28662464912143497035140759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38216619882857996046854345 28662464912143497035140759)
            ·
              refine ⟨42993697368215245552711139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28662464912143497035140759 42993697368215245552711139)
              ·
                refine ⟨64490546052322868329066709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42993697368215245552711139 64490546052322868329066709)
                ·
                  refine ⟨1511497173101317226462501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 64490546052322868329066709 1511497173101317226462501)
                  ·
                    refine ⟨283405719956496979961719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1511497173101317226462501 283405719956496979961719)
                    ·
                      rfl

theorem cell23_1655792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7, 4].length) (baseStart_1655792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655792 prefixEnd_1655792 := by exact prefixLift 1655792
  have htrace : WordTrace (prefixWord ++ tailWord_1655792) baseStart_1655792 baseEnd_1655792 := by
    simpa [prefixWord, tailWord_1655792, baseEnd_1655792] using wordTrace_append hprefix tailTrace_1655792
  have hstable : (prefixWord ++ tailWord_1655792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655792).length < 2 ^ (prefixWord ++ tailWord_1655792).sum := by decide
  have hdescent : baseEnd_1655792 < baseStart_1655792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655809 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 3, 4]
def baseStart_1655809 : Nat := 118140960795 + 1655809 * 2 ^ 59
def prefixEnd_1655809 : Nat := 4983230072969 + 3 ^ 40 * 1655809 * 2
def baseEnd_1655809 : Nat := 283408629680205791124193

theorem tailTrace_1655809 : CollatzResearch.WordTrace tailWord_1655809 prefixEnd_1655809 283408629680205791124193 := by
  unfold tailWord_1655809
  simp only [CollatzResearch.WordTrace]
  refine ⟨60392315658294257508274481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40261543772196171672182987 60392315658294257508274481)
  ·
    refine ⟨45294236743720693131205861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60392315658294257508274481 45294236743720693131205861)
    ·
      refine ⟨8492669389447629962101099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45294236743720693131205861 8492669389447629962101099)
      ·
        refine ⟨12739004084171444943151649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8492669389447629962101099 12739004084171444943151649)
        ·
          refine ⟨9554253063128583707363737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12739004084171444943151649 9554253063128583707363737)
          ·
            refine ⟨7165689797346437780522803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9554253063128583707363737 7165689797346437780522803)
            ·
              refine ⟨10748534696019656670784205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7165689797346437780522803 10748534696019656670784205)
              ·
                refine ⟨4030700511007371251544077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10748534696019656670784205 4030700511007371251544077)
                ·
                  refine ⟨1511512691627764219329029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4030700511007371251544077 1511512691627764219329029)
                  ·
                    refine ⟨283408629680205791124193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1511512691627764219329029 283408629680205791124193)
                    ·
                      rfl

theorem cell23_1655809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_1655809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655809 prefixEnd_1655809 := by exact prefixLift 1655809
  have htrace : WordTrace (prefixWord ++ tailWord_1655809) baseStart_1655809 baseEnd_1655809 := by
    simpa [prefixWord, tailWord_1655809, baseEnd_1655809] using wordTrace_append hprefix tailTrace_1655809
  have hstable : (prefixWord ++ tailWord_1655809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655809).length < 2 ^ (prefixWord ++ tailWord_1655809).sum := by decide
  have hdescent : baseEnd_1655809 < baseStart_1655809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655843 : List Nat := [1, 1, 1, 4, 3, 4, 1, 3, 1, 4]
def baseStart_1655843 : Nat := 118140960795 + 1655843 * 2 ^ 59
def prefixEnd_1655843 : Nat := 4983230072969 + 3 ^ 40 * 1655843 * 2
def baseEnd_1655843 : Nat := 283414449127623413449141

theorem tailTrace_1655843 : CollatzResearch.WordTrace tailWord_1655843 prefixEnd_1655843 283414449127623413449141 := by
  unfold tailWord_1655843
  simp only [CollatzResearch.WordTrace]
  refine ⟨60393555740171081315012183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40262370493447387543341455 60393555740171081315012183)
  ·
    refine ⟨90590333610256621972518275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60393555740171081315012183 90590333610256621972518275)
    ·
      refine ⟨135885500415384932958777413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90590333610256621972518275 135885500415384932958777413)
      ·
        refine ⟨25478531327884674929770765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135885500415384932958777413 25478531327884674929770765)
        ·
          refine ⟨9554449247956753098664037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25478531327884674929770765 9554449247956753098664037)
          ·
            refine ⟨1791459233991891205999507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9554449247956753098664037 1791459233991891205999507)
            ·
              refine ⟨2687188850987836808999261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791459233991891205999507 2687188850987836808999261)
              ·
                refine ⟨1007695819120438803374723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2687188850987836808999261 1007695819120438803374723)
                ·
                  refine ⟨1511543728680658205062085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007695819120438803374723 1511543728680658205062085)
                  ·
                    refine ⟨283414449127623413449141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1511543728680658205062085 283414449127623413449141)
                    ·
                      rfl

theorem cell23_1655843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 1, 4].length) (baseStart_1655843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655843 prefixEnd_1655843 := by exact prefixLift 1655843
  have htrace : WordTrace (prefixWord ++ tailWord_1655843) baseStart_1655843 baseEnd_1655843 := by
    simpa [prefixWord, tailWord_1655843, baseEnd_1655843] using wordTrace_append hprefix tailTrace_1655843
  have hstable : (prefixWord ++ tailWord_1655843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655843).length < 2 ^ (prefixWord ++ tailWord_1655843).sum := by decide
  have hdescent : baseEnd_1655843 < baseStart_1655843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655866 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3]
def baseStart_1655866 : Nat := 118140960795 + 1655866 * 2 ^ 59
def prefixEnd_1655866 : Nat := 4983230072969 + 3 ^ 40 * 1655866 * 2
def baseEnd_1655866 : Nat := 850255157437923650359817

theorem tailTrace_1655866 : CollatzResearch.WordTrace tailWord_1655866 prefixEnd_1655866 850255157437923650359817 := by
  unfold tailWord_1655866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098598654771939060774863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40262929746058504162066301 15098598654771939060774863)
  ·
    refine ⟨22647897982157908591162295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15098598654771939060774863 22647897982157908591162295)
    ·
      refine ⟨33971846973236862886743443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22647897982157908591162295 33971846973236862886743443)
      ·
        refine ⟨50957770459855294330115165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33971846973236862886743443 50957770459855294330115165)
        ·
          refine ⟨19109163922445735373793187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50957770459855294330115165 19109163922445735373793187)
          ·
            refine ⟨28663745883668603060689781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19109163922445735373793187 28663745883668603060689781)
            ·
              refine ⟨2687226176593931536939667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28663745883668603060689781 2687226176593931536939667)
              ·
                refine ⟨4030839264890897305409501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687226176593931536939667 4030839264890897305409501)
                ·
                  refine ⟨1511564724334086489528563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4030839264890897305409501 1511564724334086489528563)
                  ·
                    refine ⟨2267347086501129734292845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1511564724334086489528563 2267347086501129734292845)
                    ·
                      refine ⟨850255157437923650359817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2267347086501129734292845 850255157437923650359817)
                      ·
                        rfl

theorem cell23_1655866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_1655866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655866 prefixEnd_1655866 := by exact prefixLift 1655866
  have htrace : WordTrace (prefixWord ++ tailWord_1655866) baseStart_1655866 baseEnd_1655866 := by
    simpa [prefixWord, tailWord_1655866, baseEnd_1655866] using wordTrace_append hprefix tailTrace_1655866
  have hstable : (prefixWord ++ tailWord_1655866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655866).length < 2 ^ (prefixWord ++ tailWord_1655866).sum := by decide
  have hdescent : baseEnd_1655866 < baseStart_1655866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655873 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 6]
def baseStart_1655873 : Nat := 118140960795 + 1655873 * 2 ^ 59
def prefixEnd_1655873 : Nat := 4983230072969 + 3 ^ 40 * 1655873 * 2
def baseEnd_1655873 : Nat := 94473194644722791441365

theorem tailTrace_1655873 : CollatzResearch.WordTrace tailWord_1655873 prefixEnd_1655873 94473194644722791441365 := by
  unfold tailWord_1655873
  simp only [CollatzResearch.WordTrace]
  refine ⟨60394649930062396438604273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40263099953374930959069515 60394649930062396438604273)
  ·
    refine ⟨45295987447546797328953205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60394649930062396438604273 45295987447546797328953205)
    ·
      refine ⟨4246498823207512249589363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45295987447546797328953205 4246498823207512249589363)
      ·
        refine ⟨6369748234811268374384045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4246498823207512249589363 6369748234811268374384045)
        ·
          refine ⟨2388655588054225640394017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6369748234811268374384045 2388655588054225640394017)
          ·
            refine ⟨1791491691040669230295513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2388655588054225640394017 1791491691040669230295513)
            ·
              refine ⟨1343618768280501922721635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1791491691040669230295513 1343618768280501922721635)
              ·
                refine ⟨2015428152420752884082453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343618768280501922721635 2015428152420752884082453)
                ·
                  refine ⟨94473194644722791441365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2015428152420752884082453 94473194644722791441365)
                  ·
                    rfl

theorem cell23_1655873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 6].length) (baseStart_1655873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655873 prefixEnd_1655873 := by exact prefixLift 1655873
  have htrace : WordTrace (prefixWord ++ tailWord_1655873) baseStart_1655873 baseEnd_1655873 := by
    simpa [prefixWord, tailWord_1655873, baseEnd_1655873] using wordTrace_append hprefix tailTrace_1655873
  have hstable : (prefixWord ++ tailWord_1655873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655873).length < 2 ^ (prefixWord ++ tailWord_1655873).sum := by decide
  have hdescent : baseEnd_1655873 < baseStart_1655873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655889 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 2, 6, 2]
def baseStart_1655889 : Nat := 118140960795 + 1655889 * 2 ^ 59
def prefixEnd_1655889 : Nat := 4983230072969 + 3 ^ 40 * 1655889 * 2
def baseEnd_1655889 : Nat := 850266967492977060372211

theorem tailTrace_1655889 : CollatzResearch.WordTrace tailWord_1655889 prefixEnd_1655889 850266967492977060372211 := by
  unfold tailWord_1655889
  simp only [CollatzResearch.WordTrace]
  refine ⟨60395233498004431171186721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40263488998669620780791147 60395233498004431171186721)
  ·
    refine ⟨45296425123503323378390041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60395233498004431171186721 45296425123503323378390041)
    ·
      refine ⟨33972318842627492533792531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45296425123503323378390041 33972318842627492533792531)
      ·
        refine ⟨50958478263941238800688797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33972318842627492533792531 50958478263941238800688797)
        ·
          refine ⟨19109429348977964550258299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50958478263941238800688797 19109429348977964550258299)
          ·
            refine ⟨28664144023466946825387449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19109429348977964550258299 28664144023466946825387449)
            ·
              refine ⟨21498108017600210119040587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28664144023466946825387449 21498108017600210119040587)
              ·
                refine ⟨32247162026400315178560881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21498108017600210119040587 32247162026400315178560881)
                ·
                  refine ⟨24185371519800236383920661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32247162026400315178560881 24185371519800236383920661)
                  ·
                    refine ⟨1133689289990636080496281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24185371519800236383920661 1133689289990636080496281)
                    ·
                      refine ⟨850266967492977060372211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133689289990636080496281 850266967492977060372211)
                      ·
                        rfl

theorem cell23_1655889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 6, 2].length) (baseStart_1655889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655889 prefixEnd_1655889 := by exact prefixLift 1655889
  have htrace : WordTrace (prefixWord ++ tailWord_1655889) baseStart_1655889 baseEnd_1655889 := by
    simpa [prefixWord, tailWord_1655889, baseEnd_1655889] using wordTrace_append hprefix tailTrace_1655889
  have hstable : (prefixWord ++ tailWord_1655889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655889).length < 2 ^ (prefixWord ++ tailWord_1655889).sum := by decide
  have hdescent : baseEnd_1655889 < baseStart_1655889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655916 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 2, 4]
def baseStart_1655916 : Nat := 118140960795 + 1655916 * 2 ^ 59
def prefixEnd_1655916 : Nat := 4983230072969 + 3 ^ 40 * 1655916 * 2
def baseEnd_1655916 : Nat := 283426943823549484911529

theorem tailTrace_1655916 : CollatzResearch.WordTrace tailWord_1655916 prefixEnd_1655916 283426943823549484911529 := by
  unfold tailWord_1655916
  simp only [CollatzResearch.WordTrace]
  refine ⟨30198109134453307391209801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40264145512604409854946401 30198109134453307391209801)
  ·
    refine ⟨22648581850839980543407351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30198109134453307391209801 22648581850839980543407351)
    ·
      refine ⟨33972872776259970815111027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22648581850839980543407351 33972872776259970815111027)
      ·
        refine ⟨50959309164389956222666541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33972872776259970815111027 50959309164389956222666541)
        ·
          refine ⟨19109740936646233583499953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50959309164389956222666541 19109740936646233583499953)
          ·
            refine ⟨14332305702484675187624965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19109740936646233583499953 14332305702484675187624965)
            ·
              refine ⟨2687307319215876597679681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14332305702484675187624965 2687307319215876597679681)
              ·
                refine ⟨2015480489411907448259761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2687307319215876597679681 2015480489411907448259761)
                ·
                  refine ⟨1511610367058930586194821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2015480489411907448259761 1511610367058930586194821)
                  ·
                    refine ⟨283426943823549484911529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1511610367058930586194821 283426943823549484911529)
                    ·
                      rfl

theorem cell23_1655916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_1655916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655916 prefixEnd_1655916 := by exact prefixLift 1655916
  have htrace : WordTrace (prefixWord ++ tailWord_1655916) baseStart_1655916 baseEnd_1655916 := by
    simpa [prefixWord, tailWord_1655916, baseEnd_1655916] using wordTrace_append hprefix tailTrace_1655916
  have hstable : (prefixWord ++ tailWord_1655916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655916).length < 2 ^ (prefixWord ++ tailWord_1655916).sum := by decide
  have hdescent : baseEnd_1655916 < baseStart_1655916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655917 : List Nat := [1, 5, 1, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_1655917 : Nat := 118140960795 + 1655917 * 2 ^ 59
def prefixEnd_1655917 : Nat := 4983230072969 + 3 ^ 40 * 1655917 * 2
def baseEnd_1655917 : Nat := 850281344951302950822083

theorem tailTrace_1655917 : CollatzResearch.WordTrace tailWord_1655917 prefixEnd_1655917 850281344951302950822083 := by
  unfold tailWord_1655917
  simp only [CollatzResearch.WordTrace]
  refine ⟨60396254741902991953206005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40264169827935327968804003 60396254741902991953206005)
  ·
    refine ⟨5662148882053405495613063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60396254741902991953206005 5662148882053405495613063)
    ·
      refine ⟨8493223323080108243419595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5662148882053405495613063 8493223323080108243419595)
      ·
        refine ⟨12739834984620162365129393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8493223323080108243419595 12739834984620162365129393)
        ·
          refine ⟨9554876238465121773847045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12739834984620162365129393 9554876238465121773847045)
          ·
            refine ⟨1791539294712210332596321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9554876238465121773847045 1791539294712210332596321)
            ·
              refine ⟨1343654471034157749447241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1791539294712210332596321 1343654471034157749447241)
              ·
                refine ⟨1007740853275618312085431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1343654471034157749447241 1007740853275618312085431)
                ·
                  refine ⟨1511611279913427468128147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007740853275618312085431 1511611279913427468128147)
                  ·
                    refine ⟨2267416919870141202192221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1511611279913427468128147 2267416919870141202192221)
                    ·
                      refine ⟨850281344951302950822083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2267416919870141202192221 850281344951302950822083)
                      ·
                        rfl

theorem cell23_1655917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_1655917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655917 prefixEnd_1655917 := by exact prefixLift 1655917
  have htrace : WordTrace (prefixWord ++ tailWord_1655917) baseStart_1655917 baseEnd_1655917 := by
    simpa [prefixWord, tailWord_1655917, baseEnd_1655917] using wordTrace_append hprefix tailTrace_1655917
  have hstable : (prefixWord ++ tailWord_1655917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655917).length < 2 ^ (prefixWord ++ tailWord_1655917).sum := by decide
  have hdescent : baseEnd_1655917 < baseStart_1655917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655926 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1655926 : Nat := 118140960795 + 1655926 * 2 ^ 59
def prefixEnd_1655926 : Nat := 4983230072969 + 3 ^ 40 * 1655926 * 2
def baseEnd_1655926 : Nat := 850285966277193415609541

theorem tailTrace_1655926 : CollatzResearch.WordTrace tailWord_1655926 prefixEnd_1655926 850285966277193415609541 := by
  unfold tailWord_1655926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774786437429399155642727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40264388665913590993522421 3774786437429399155642727)
  ·
    refine ⟨5662179656144098733464091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3774786437429399155642727 5662179656144098733464091)
    ·
      refine ⟨8493269484216148100196137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5662179656144098733464091 8493269484216148100196137)
      ·
        refine ⟨6369952113162111075147103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8493269484216148100196137 6369952113162111075147103)
        ·
          refine ⟨9554928169743166612720655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6369952113162111075147103 9554928169743166612720655)
          ·
            refine ⟨14332392254614749919080983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9554928169743166612720655 14332392254614749919080983)
            ·
              refine ⟨21498588381922124878621475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14332392254614749919080983 21498588381922124878621475)
              ·
                refine ⟨32247882572883187317932213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21498588381922124878621475 32247882572883187317932213)
                ·
                  refine ⟨3023238991207798811056145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32247882572883187317932213 3023238991207798811056145)
                  ·
                    refine ⟨2267429243405849108292109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3023238991207798811056145 2267429243405849108292109)
                    ·
                      refine ⟨850285966277193415609541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2267429243405849108292109 850285966277193415609541)
                      ·
                        rfl

theorem cell23_1655926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1655926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655926 prefixEnd_1655926 := by exact prefixLift 1655926
  have htrace : WordTrace (prefixWord ++ tailWord_1655926) baseStart_1655926 baseEnd_1655926 := by
    simpa [prefixWord, tailWord_1655926, baseEnd_1655926] using wordTrace_append hprefix tailTrace_1655926
  have hstable : (prefixWord ++ tailWord_1655926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655926).length < 2 ^ (prefixWord ++ tailWord_1655926).sum := by decide
  have hdescent : baseEnd_1655926 < baseStart_1655926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655960 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 1, 2, 3]
def baseStart_1655960 : Nat := 118140960795 + 1655960 * 2 ^ 59
def prefixEnd_1655960 : Nat := 4983230072969 + 3 ^ 40 * 1655960 * 2
def baseEnd_1655960 : Nat := 850303424619446282584385

theorem tailTrace_1655960 : CollatzResearch.WordTrace tailWord_1655960 prefixEnd_1655960 850303424619446282584385 := by
  unfold tailWord_1655960
  simp only [CollatzResearch.WordTrace]
  refine ⟨30198911540373605148510667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40265215387164806864680889 30198911540373605148510667)
  ·
    refine ⟨45298367310560407722766001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30198911540373605148510667 45298367310560407722766001)
    ·
      refine ⟨33973775482920305792074501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45298367310560407722766001 33973775482920305792074501)
      ·
        refine ⟨6370082903047557336013969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33973775482920305792074501 6370082903047557336013969)
        ·
          refine ⟨4777562177285668002010477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6370082903047557336013969 4777562177285668002010477)
          ·
            refine ⟨1791585816482125500753929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4777562177285668002010477 1791585816482125500753929)
            ·
              refine ⟨1343689362361594125565447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1791585816482125500753929 1343689362361594125565447)
              ·
                refine ⟨2015534043542391188348171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343689362361594125565447 2015534043542391188348171)
                ·
                  refine ⟨3023301065313586782522257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015534043542391188348171 3023301065313586782522257)
                  ·
                    refine ⟨2267475798985190086891693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3023301065313586782522257 2267475798985190086891693)
                    ·
                      refine ⟨850303424619446282584385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2267475798985190086891693 850303424619446282584385)
                      ·
                        rfl

theorem cell23_1655960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_1655960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655960 prefixEnd_1655960 := by exact prefixLift 1655960
  have htrace : WordTrace (prefixWord ++ tailWord_1655960) baseStart_1655960 baseEnd_1655960 := by
    simpa [prefixWord, tailWord_1655960, baseEnd_1655960] using wordTrace_append hprefix tailTrace_1655960
  have hstable : (prefixWord ++ tailWord_1655960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655960).length < 2 ^ (prefixWord ++ tailWord_1655960).sum := by decide
  have hdescent : baseEnd_1655960 < baseStart_1655960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655973 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 2, 1, 3]
def baseStart_1655973 : Nat := 118140960795 + 1655973 * 2 ^ 59
def prefixEnd_1655973 : Nat := 4983230072969 + 3 ^ 40 * 1655973 * 2
def baseEnd_1655973 : Nat := 850310099867954731721825

theorem tailTrace_1655973 : CollatzResearch.WordTrace tailWord_1655973 prefixEnd_1655973 850310099867954731721825 := by
  unfold tailWord_1655973
  simp only [CollatzResearch.WordTrace]
  refine ⟨60398297229700113517244573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40265531486466742344829715 60398297229700113517244573)
  ·
    refine ⟨22649361461137542568966715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60398297229700113517244573 22649361461137542568966715)
    ·
      refine ⟨33974042191706313853450073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22649361461137542568966715 33974042191706313853450073)
      ·
        refine ⟨25480531643779735390087555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33974042191706313853450073 25480531643779735390087555)
        ·
          refine ⟨38220797465669603085131333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25480531643779735390087555 38220797465669603085131333)
          ·
            refine ⟨7166399524813050578462125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38220797465669603085131333 7166399524813050578462125)
            ·
              refine ⟨2687399821804893966923297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7166399524813050578462125 2687399821804893966923297)
              ·
                refine ⟨2015549866353670475192473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2687399821804893966923297 2015549866353670475192473)
                ·
                  refine ⟨1511662399765252856394355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2015549866353670475192473 1511662399765252856394355)
                  ·
                    refine ⟨2267493599647879284591533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1511662399765252856394355 2267493599647879284591533)
                    ·
                      refine ⟨850310099867954731721825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2267493599647879284591533 850310099867954731721825)
                      ·
                        rfl

theorem cell23_1655973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_1655973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655973 prefixEnd_1655973 := by exact prefixLift 1655973
  have htrace : WordTrace (prefixWord ++ tailWord_1655973) baseStart_1655973 baseEnd_1655973 := by
    simpa [prefixWord, tailWord_1655973, baseEnd_1655973] using wordTrace_append hprefix tailTrace_1655973
  have hstable : (prefixWord ++ tailWord_1655973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655973).length < 2 ^ (prefixWord ++ tailWord_1655973).sum := by decide
  have hdescent : baseEnd_1655973 < baseStart_1655973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655999 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 3]
def baseStart_1655999 : Nat := 118140960795 + 1655999 * 2 ^ 59
def prefixEnd_1655999 : Nat := 4983230072969 + 3 ^ 40 * 1655999 * 2
def baseEnd_1655999 : Nat := 850323450364971629996705

theorem tailTrace_1655999 : CollatzResearch.WordTrace tailWord_1655999 prefixEnd_1655999 850323450364971629996705 := by
  unfold tailWord_1655999
  simp only [CollatzResearch.WordTrace]
  refine ⟨60399245527605919957691051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40266163685070613305127367 60399245527605919957691051)
  ·
    refine ⟨90598868291408879936536577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60399245527605919957691051 90598868291408879936536577)
    ·
      refine ⟨67949151218556659952402433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90598868291408879936536577 67949151218556659952402433)
      ·
        refine ⟨50961863413917494964301825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67949151218556659952402433 50961863413917494964301825)
        ·
          refine ⟨38221397560438121223226369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50961863413917494964301825 38221397560438121223226369)
          ·
            refine ⟨28666048170328590917419777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38221397560438121223226369 28666048170328590917419777)
            ·
              refine ⟨21499536127746443188064833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28666048170328590917419777 21499536127746443188064833)
              ·
                refine ⟨16124652095809832391048625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21499536127746443188064833 16124652095809832391048625)
                ·
                  refine ⟨12093489071857374293286469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16124652095809832391048625 12093489071857374293286469)
                  ·
                    refine ⟨2267529200973257679991213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12093489071857374293286469 2267529200973257679991213)
                    ·
                      refine ⟨850323450364971629996705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2267529200973257679991213 850323450364971629996705)
                      ·
                        rfl

theorem cell23_1655999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_1655999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655999 prefixEnd_1655999 := by exact prefixLift 1655999
  have htrace : WordTrace (prefixWord ++ tailWord_1655999) baseStart_1655999 baseEnd_1655999 := by
    simpa [prefixWord, tailWord_1655999, baseEnd_1655999] using wordTrace_append hprefix tailTrace_1655999
  have hstable : (prefixWord ++ tailWord_1655999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655999).length < 2 ^ (prefixWord ++ tailWord_1655999).sum := by decide
  have hdescent : baseEnd_1655999 < baseStart_1655999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656000 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 1, 3, 2]
def baseStart_1656000 : Nat := 118140960795 + 1656000 * 2 ^ 59
def prefixEnd_1656000 : Nat := 4983230072969 + 3 ^ 40 * 1656000 * 2
def baseEnd_1656000 : Nat := 850323963845626126084201

theorem tailTrace_1656000 : CollatzResearch.WordTrace tailWord_1656000 prefixEnd_1656000 850323963845626126084201 := by
  unfold tailWord_1656000
  simp only [CollatzResearch.WordTrace]
  refine ⟨30199641000301148564238727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40266188000401531418984969 30199641000301148564238727)
  ·
    refine ⟨45299461500451722846358091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30199641000301148564238727 45299461500451722846358091)
    ·
      refine ⟨67949192250677584269537137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45299461500451722846358091 67949192250677584269537137)
      ·
        refine ⟨50961894188008188202152853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67949192250677584269537137 50961894188008188202152853)
        ·
          refine ⟨2388838790062883821975915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50961894188008188202152853 2388838790062883821975915)
          ·
            refine ⟨3583258185094325732963873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388838790062883821975915 3583258185094325732963873)
            ·
              refine ⟨2687443638820744299722905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3583258185094325732963873 2687443638820744299722905)
              ·
                refine ⟨2015582729115558224792179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2687443638820744299722905 2015582729115558224792179)
                ·
                  refine ⟨3023374093673337337188269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015582729115558224792179 3023374093673337337188269)
                  ·
                    refine ⟨1133765285127501501445601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023374093673337337188269 1133765285127501501445601)
                    ·
                      refine ⟨850323963845626126084201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133765285127501501445601 850323963845626126084201)
                      ·
                        rfl

theorem cell23_1656000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 3, 2].length) (baseStart_1656000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656000 prefixEnd_1656000 := by exact prefixLift 1656000
  have htrace : WordTrace (prefixWord ++ tailWord_1656000) baseStart_1656000 baseEnd_1656000 := by
    simpa [prefixWord, tailWord_1656000, baseEnd_1656000] using wordTrace_append hprefix tailTrace_1656000
  have hstable : (prefixWord ++ tailWord_1656000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656000).length < 2 ^ (prefixWord ++ tailWord_1656000).sum := by decide
  have hdescent : baseEnd_1656000 < baseStart_1656000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656036 : List Nat := [2, 3, 1, 1, 1, 2, 2, 6, 5]
def baseStart_1656036 : Nat := 118140960795 + 1656036 * 2 ^ 59
def prefixEnd_1656036 : Nat := 4983230072969 + 3 ^ 40 * 1656036 * 2
def baseEnd_1656036 : Nat := 94482494349909776137115

theorem tailTrace_1656036 : CollatzResearch.WordTrace tailWord_1656036 prefixEnd_1656036 94482494349909776137115 := by
  unfold tailWord_1656036
  simp only [CollatzResearch.WordTrace]
  refine ⟨30200297514235937638393981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40267063352314583517858641 30200297514235937638393981)
  ·
    refine ⟨11325111567838476614397743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30200297514235937638393981 11325111567838476614397743)
    ·
      refine ⟨16987667351757714921596615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11325111567838476614397743 16987667351757714921596615)
      ·
        refine ⟨25481501027636572382394923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16987667351757714921596615 25481501027636572382394923)
        ·
          refine ⟨38222251541454858573592385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25481501027636572382394923 38222251541454858573592385)
          ·
            refine ⟨28666688656091143930194289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38222251541454858573592385 28666688656091143930194289)
            ·
              refine ⟨21500016492068357947645717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28666688656091143930194289 21500016492068357947645717)
              ·
                refine ⟨1007813273065704278795893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21500016492068357947645717 1007813273065704278795893)
                ·
                  refine ⟨94482494349909776137115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1007813273065704278795893 94482494349909776137115)
                  ·
                    rfl

theorem cell23_1656036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_1656036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656036 prefixEnd_1656036 := by exact prefixLift 1656036
  have htrace : WordTrace (prefixWord ++ tailWord_1656036) baseStart_1656036 baseEnd_1656036 := by
    simpa [prefixWord, tailWord_1656036, baseEnd_1656036] using wordTrace_append hprefix tailTrace_1656036
  have hstable : (prefixWord ++ tailWord_1656036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656036).length < 2 ^ (prefixWord ++ tailWord_1656036).sum := by decide
  have hdescent : baseEnd_1656036 < baseStart_1656036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656046 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_1656046 : Nat := 118140960795 + 1656046 * 2 ^ 59
def prefixEnd_1656046 : Nat := 4983230072969 + 3 ^ 40 * 1656046 * 2
def baseEnd_1656046 : Nat := 850347583955732946108989

theorem tailTrace_1656046 : CollatzResearch.WordTrace tailWord_1656046 prefixEnd_1656046 850347583955732946108989 := by
  unfold tailWord_1656046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550119969804455873081499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40267306505623764656434661 7550119969804455873081499)
  ·
    refine ⟨11325179954706683809622249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7550119969804455873081499 11325179954706683809622249)
    ·
      refine ⟨8493884966030012857216687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11325179954706683809622249 8493884966030012857216687)
      ·
        refine ⟨12740827449045019285825031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8493884966030012857216687 12740827449045019285825031)
        ·
          refine ⟨19111241173567528928737547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12740827449045019285825031 19111241173567528928737547)
          ·
            refine ⟨28666861760351293393106321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19111241173567528928737547 28666861760351293393106321)
            ·
              refine ⟨21500146320263470044829741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28666861760351293393106321 21500146320263470044829741)
              ·
                refine ⟨8062554870098801266811153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21500146320263470044829741 8062554870098801266811153)
                ·
                  refine ⟨6046916152574100950108365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8062554870098801266811153 6046916152574100950108365)
                  ·
                    refine ⟨2267593557215287856290637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6046916152574100950108365 2267593557215287856290637)
                    ·
                      refine ⟨850347583955732946108989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2267593557215287856290637 850347583955732946108989)
                      ·
                        rfl

theorem cell23_1656046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_1656046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656046 prefixEnd_1656046 := by exact prefixLift 1656046
  have htrace : WordTrace (prefixWord ++ tailWord_1656046) baseStart_1656046 baseEnd_1656046 := by
    simpa [prefixWord, tailWord_1656046, baseEnd_1656046] using wordTrace_append hprefix tailTrace_1656046
  have hstable : (prefixWord ++ tailWord_1656046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656046).length < 2 ^ (prefixWord ++ tailWord_1656046).sum := by decide
  have hdescent : baseEnd_1656046 < baseStart_1656046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656049 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 6, 5]
def baseStart_1656049 : Nat := 118140960795 + 1656049 * 2 ^ 59
def prefixEnd_1656049 : Nat := 4983230072969 + 3 ^ 40 * 1656049 * 2
def baseEnd_1656049 : Nat := 283449708132565478123825

theorem tailTrace_1656049 : CollatzResearch.WordTrace tailWord_1656049 prefixEnd_1656049 283449708132565478123825 := by
  unfold tailWord_1656049
  simp only [CollatzResearch.WordTrace]
  refine ⟨60401069177424778497011201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40267379451616518998007467 60401069177424778497011201)
  ·
    refine ⟨45300801883068583872758401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60401069177424778497011201 45300801883068583872758401)
    ·
      refine ⟨33975601412301437904568801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45300801883068583872758401 33975601412301437904568801)
      ·
        refine ⟨25481701059226078428426601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33975601412301437904568801 25481701059226078428426601)
        ·
          refine ⟨19111275794419558821319951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25481701059226078428426601 19111275794419558821319951)
          ·
            refine ⟨28666913691629338231979927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19111275794419558821319951 28666913691629338231979927)
            ·
              refine ⟨43000370537444007347969891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28666913691629338231979927 43000370537444007347969891)
              ·
                refine ⟨64500555806166011021954837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43000370537444007347969891 64500555806166011021954837)
                ·
                  refine ⟨3023463553414031766654133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64500555806166011021954837 3023463553414031766654133)
                  ·
                    refine ⟨283449708132565478123825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3023463553414031766654133 283449708132565478123825)
                    ·
                      rfl

theorem cell23_1656049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_1656049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656049 prefixEnd_1656049 := by exact prefixLift 1656049
  have htrace : WordTrace (prefixWord ++ tailWord_1656049) baseStart_1656049 baseEnd_1656049 := by
    simpa [prefixWord, tailWord_1656049, baseEnd_1656049] using wordTrace_append hprefix tailTrace_1656049
  have hstable : (prefixWord ++ tailWord_1656049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656049).length < 2 ^ (prefixWord ++ tailWord_1656049).sum := by decide
  have hdescent : baseEnd_1656049 < baseStart_1656049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656113 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 3, 4]
def baseStart_1656113 : Nat := 118140960795 + 1656113 * 2 ^ 59
def prefixEnd_1656113 : Nat := 4983230072969 + 3 ^ 40 * 1656113 * 2
def baseEnd_1656113 : Nat := 283460662386528061323727

theorem tailTrace_1656113 : CollatzResearch.WordTrace tailWord_1656113 prefixEnd_1656113 283460662386528061323727 := by
  unfold tailWord_1656113
  simp only [CollatzResearch.WordTrace]
  refine ⟨60403403449192917427340993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40268935632795278284893995 60403403449192917427340993)
  ·
    refine ⟨45302552586894688070505745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60403403449192917427340993 45302552586894688070505745)
    ·
      refine ⟨33976914440171016052879309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45302552586894688070505745 33976914440171016052879309)
      ·
        refine ⟨12741342915064131019829741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33976914440171016052879309 12741342915064131019829741)
        ·
          refine ⟨4778003593149049132436153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12741342915064131019829741 4778003593149049132436153)
          ·
            refine ⟨3583502694861786849327115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4778003593149049132436153 3583502694861786849327115)
            ·
              refine ⟨5375254042292680273990673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583502694861786849327115 5375254042292680273990673)
              ·
                refine ⟨4031440531719510205493005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5375254042292680273990673 4031440531719510205493005)
                ·
                  refine ⟨1511790199394816327059877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4031440531719510205493005 1511790199394816327059877)
                  ·
                    refine ⟨283460662386528061323727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1511790199394816327059877 283460662386528061323727)
                    ·
                      rfl

theorem cell23_1656113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_1656113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656113 prefixEnd_1656113 := by exact prefixLift 1656113
  have htrace : WordTrace (prefixWord ++ tailWord_1656113) baseStart_1656113 baseEnd_1656113 := by
    simpa [prefixWord, tailWord_1656113, baseEnd_1656113] using wordTrace_append hprefix tailTrace_1656113
  have hstable : (prefixWord ++ tailWord_1656113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656113).length < 2 ^ (prefixWord ++ tailWord_1656113).sum := by decide
  have hdescent : baseEnd_1656113 < baseStart_1656113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656126 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_1656126 : Nat := 118140960795 + 1656126 * 2 ^ 59
def prefixEnd_1656126 : Nat := 4983230072969 + 3 ^ 40 * 1656126 * 2
def baseEnd_1656126 : Nat := 94487629156454737012069

theorem tailTrace_1656126 : CollatzResearch.WordTrace tailWord_1656126 prefixEnd_1656126 94487629156454737012069 := by
  unfold tailWord_1656126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550484699768227580945529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40269251732097213765042821 7550484699768227580945529)
  ·
    refine ⟨5662863524826170685709147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7550484699768227580945529 5662863524826170685709147)
    ·
      refine ⟨8494295287239256028563721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5662863524826170685709147 8494295287239256028563721)
      ·
        refine ⟨6370721465429442021422791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8494295287239256028563721 6370721465429442021422791)
        ·
          refine ⟨9556082198144163032134187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6370721465429442021422791 9556082198144163032134187)
          ·
            refine ⟨14334123297216244548201281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9556082198144163032134187 14334123297216244548201281)
            ·
              refine ⟨10750592472912183411150961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14334123297216244548201281 10750592472912183411150961)
              ·
                refine ⟨8062944354684137558363221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10750592472912183411150961 8062944354684137558363221)
                ·
                  refine ⟨94487629156454737012069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8062944354684137558363221 94487629156454737012069)
                  ·
                    rfl

theorem cell23_1656126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_1656126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656126 prefixEnd_1656126 := by exact prefixLift 1656126
  have htrace : WordTrace (prefixWord ++ tailWord_1656126) baseStart_1656126 baseEnd_1656126 := by
    simpa [prefixWord, tailWord_1656126, baseEnd_1656126] using wordTrace_append hprefix tailTrace_1656126
  have hstable : (prefixWord ++ tailWord_1656126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656126).length < 2 ^ (prefixWord ++ tailWord_1656126).sum := by decide
  have hdescent : baseEnd_1656126 < baseStart_1656126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656153 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 3, 1, 3]
def baseStart_1656153 : Nat := 118140960795 + 1656153 * 2 ^ 59
def prefixEnd_1656153 : Nat := 4983230072969 + 3 ^ 40 * 1656153 * 2
def baseEnd_1656153 : Nat := 850402526385764027470997

theorem tailTrace_1656153 : CollatzResearch.WordTrace tailWord_1656153 prefixEnd_1656153 850402526385764027470997 := by
  unfold tailWord_1656153
  simp only [CollatzResearch.WordTrace]
  refine ⟨60404862369048004258797113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40269908246032002839198075 60404862369048004258797113)
  ·
    refine ⟨45303646776786003194097835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60404862369048004258797113 45303646776786003194097835)
    ·
      refine ⟨67955470165179004791146753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45303646776786003194097835 67955470165179004791146753)
      ·
        refine ⟨50966602623884253593360065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67955470165179004791146753 50966602623884253593360065)
        ·
          refine ⟨38224951967913190195020049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50966602623884253593360065 38224951967913190195020049)
          ·
            refine ⟨28668713975934892646265037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38224951967913190195020049 28668713975934892646265037)
            ·
              refine ⟨10750767740975584742349389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28668713975934892646265037 10750767740975584742349389)
              ·
                refine ⟨4031537902865844278381021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10750767740975584742349389 4031537902865844278381021)
                ·
                  refine ⟨1511826713574691604392883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4031537902865844278381021 1511826713574691604392883)
                  ·
                    refine ⟨2267740070362037406589325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1511826713574691604392883 2267740070362037406589325)
                    ·
                      refine ⟨850402526385764027470997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2267740070362037406589325 850402526385764027470997)
                      ·
                        rfl

theorem cell23_1656153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_1656153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656153 prefixEnd_1656153 := by exact prefixLift 1656153
  have htrace : WordTrace (prefixWord ++ tailWord_1656153) baseStart_1656153 baseEnd_1656153 := by
    simpa [prefixWord, tailWord_1656153, baseEnd_1656153] using wordTrace_append hprefix tailTrace_1656153
  have hstable : (prefixWord ++ tailWord_1656153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656153).length < 2 ^ (prefixWord ++ tailWord_1656153).sum := by decide
  have hdescent : baseEnd_1656153 < baseStart_1656153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656163 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 1, 5, 2]
def baseStart_1656163 : Nat := 118140960795 + 1656163 * 2 ^ 59
def prefixEnd_1656163 : Nat := 4983230072969 + 3 ^ 40 * 1656163 * 2
def baseEnd_1656163 : Nat := 850407661192308988345951

theorem tailTrace_1656163 : CollatzResearch.WordTrace tailWord_1656163 prefixEnd_1656163 850407661192308988345951 := by
  unfold tailWord_1656163
  simp only [CollatzResearch.WordTrace]
  refine ⟨60405227099011775966661143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40270151399341183977774095 60405227099011775966661143)
  ·
    refine ⟨90607840648517663949991715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60405227099011775966661143 90607840648517663949991715)
    ·
      refine ⟨135911760972776495924987573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90607840648517663949991715 135911760972776495924987573)
      ·
        refine ⟨12741727591197796492967585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135911760972776495924987573 12741727591197796492967585)
        ·
          refine ⟨9556295693398347369725689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12741727591197796492967585 9556295693398347369725689)
          ·
            refine ⟨7167221770048760527294267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9556295693398347369725689 7167221770048760527294267)
            ·
              refine ⟨10750832655073140790941401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167221770048760527294267 10750832655073140790941401)
              ·
                refine ⟨8063124491304855593206051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10750832655073140790941401 8063124491304855593206051)
                ·
                  refine ⟨12094686736957283389809077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8063124491304855593206051 12094686736957283389809077)
                  ·
                    refine ⟨1133876881589745317794601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12094686736957283389809077 1133876881589745317794601)
                    ·
                      refine ⟨850407661192308988345951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133876881589745317794601 850407661192308988345951)
                      ·
                        rfl

theorem cell23_1656163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_1656163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656163 prefixEnd_1656163 := by exact prefixLift 1656163
  have htrace : WordTrace (prefixWord ++ tailWord_1656163) baseStart_1656163 baseEnd_1656163 := by
    simpa [prefixWord, tailWord_1656163, baseEnd_1656163] using wordTrace_append hprefix tailTrace_1656163
  have hstable : (prefixWord ++ tailWord_1656163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656163).length < 2 ^ (prefixWord ++ tailWord_1656163).sum := by decide
  have hdescent : baseEnd_1656163 < baseStart_1656163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656173 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_1656173 : Nat := 118140960795 + 1656173 * 2 ^ 59
def prefixEnd_1656173 : Nat := 4983230072969 + 3 ^ 40 * 1656173 * 2
def baseEnd_1656173 : Nat := 283470931999617983073635

theorem tailTrace_1656173 : CollatzResearch.WordTrace tailWord_1656173 prefixEnd_1656173 283470931999617983073635 := by
  unfold tailWord_1656173
  simp only [CollatzResearch.WordTrace]
  refine ⟨60405591828975547674525173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40270394552650365116350115 60405591828975547674525173)
  ·
    refine ⟨5663024233966457594486735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60405591828975547674525173 5663024233966457594486735)
    ·
      refine ⟨8494536350949686391730103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5663024233966457594486735 8494536350949686391730103)
      ·
        refine ⟨12741804526424529587595155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8494536350949686391730103 12741804526424529587595155)
        ·
          refine ⟨19112706789636794381392733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12741804526424529587595155 19112706789636794381392733)
          ·
            refine ⟨7167265046113797893022275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19112706789636794381392733 7167265046113797893022275)
            ·
              refine ⟨10750897569170696839533413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167265046113797893022275 10750897569170696839533413)
              ·
                refine ⟨2015793294219505657412515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10750897569170696839533413 2015793294219505657412515)
                ·
                  refine ⟨3023689941329258486118773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015793294219505657412515 3023689941329258486118773)
                  ·
                    refine ⟨283470931999617983073635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3023689941329258486118773 283470931999617983073635)
                    ·
                      rfl

theorem cell23_1656173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_1656173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656173 prefixEnd_1656173 := by exact prefixLift 1656173
  have htrace : WordTrace (prefixWord ++ tailWord_1656173) baseStart_1656173 baseEnd_1656173 := by
    simpa [prefixWord, tailWord_1656173, baseEnd_1656173] using wordTrace_append hprefix tailTrace_1656173
  have hstable : (prefixWord ++ tailWord_1656173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656173).length < 2 ^ (prefixWord ++ tailWord_1656173).sum := by decide
  have hdescent : baseEnd_1656173 < baseStart_1656173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656203 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 2, 4]
def baseStart_1656203 : Nat := 118140960795 + 1656203 * 2 ^ 59
def prefixEnd_1656203 : Nat := 4983230072969 + 3 ^ 40 * 1656203 * 2
def baseEnd_1656203 : Nat := 283476066806162943948589

theorem tailTrace_1656203 : CollatzResearch.WordTrace tailWord_1656203 prefixEnd_1656203 283476066806162943948589 := by
  unfold tailWord_1656203
  simp only [CollatzResearch.WordTrace]
  refine ⟨60406686018866862798117263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40271124012577908532078175 60406686018866862798117263)
  ·
    refine ⟨90610029028300294197175895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60406686018866862798117263 90610029028300294197175895)
    ·
      refine ⟨135915043542450441295763843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90610029028300294197175895 135915043542450441295763843)
      ·
        refine ⟨203872565313675661943645765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135915043542450441295763843 203872565313675661943645765)
        ·
          refine ⟨38226105996314186614433581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203872565313675661943645765 38226105996314186614433581)
          ·
            refine ⟨14334789748617819980412593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38226105996314186614433581 14334789748617819980412593)
            ·
              refine ⟨10751092311463364985309445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14334789748617819980412593 10751092311463364985309445)
              ·
                refine ⟨2015829808399380934745521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10751092311463364985309445 2015829808399380934745521)
                ·
                  refine ⟨1511872356299535701059141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2015829808399380934745521 1511872356299535701059141)
                  ·
                    refine ⟨283476066806162943948589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1511872356299535701059141 283476066806162943948589)
                    ·
                      rfl

theorem cell23_1656203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 4].length) (baseStart_1656203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656203 prefixEnd_1656203 := by exact prefixLift 1656203
  have htrace : WordTrace (prefixWord ++ tailWord_1656203) baseStart_1656203 baseEnd_1656203 := by
    simpa [prefixWord, tailWord_1656203, baseEnd_1656203] using wordTrace_append hprefix tailTrace_1656203
  have hstable : (prefixWord ++ tailWord_1656203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656203).length < 2 ^ (prefixWord ++ tailWord_1656203).sum := by decide
  have hdescent : baseEnd_1656203 < baseStart_1656203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656243 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 6, 1, 3]
def baseStart_1656243 : Nat := 118140960795 + 1656243 * 2 ^ 59
def prefixEnd_1656243 : Nat := 4983230072969 + 3 ^ 40 * 1656243 * 2
def baseEnd_1656243 : Nat := 850448739644668675345583

theorem tailTrace_1656243 : CollatzResearch.WordTrace tailWord_1656243 prefixEnd_1656243 850448739644668675345583 := by
  unfold tailWord_1656243
  simp only [CollatzResearch.WordTrace]
  refine ⟨60408144938721949629573383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40272096625814633086382255 60408144938721949629573383)
  ·
    refine ⟨90612217408082924444360075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60408144938721949629573383 90612217408082924444360075)
    ·
      refine ⟨135918326112124386666540113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90612217408082924444360075 135918326112124386666540113)
      ·
        refine ⟨101938744584093289999905085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135918326112124386666540113 101938744584093289999905085)
        ·
          refine ⟨38227029219034983749964407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101938744584093289999905085 38227029219034983749964407)
          ·
            refine ⟨57340543828552475624946611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38227029219034983749964407 57340543828552475624946611)
            ·
              refine ⟨86010815742828713437419917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57340543828552475624946611 86010815742828713437419917)
              ·
                refine ⟨32254055903560767539032469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86010815742828713437419917 32254055903560767539032469)
                ·
                  refine ⟨1511908870479410978392147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32254055903560767539032469 1511908870479410978392147)
                  ·
                    refine ⟨2267863305719116467588221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1511908870479410978392147 2267863305719116467588221)
                    ·
                      refine ⟨850448739644668675345583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2267863305719116467588221 850448739644668675345583)
                      ·
                        rfl

theorem cell23_1656243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 1, 3].length) (baseStart_1656243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656243 prefixEnd_1656243 := by exact prefixLift 1656243
  have htrace : WordTrace (prefixWord ++ tailWord_1656243) baseStart_1656243 baseEnd_1656243 := by
    simpa [prefixWord, tailWord_1656243, baseEnd_1656243] using wordTrace_append hprefix tailTrace_1656243
  have hstable : (prefixWord ++ tailWord_1656243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656243).length < 2 ^ (prefixWord ++ tailWord_1656243).sum := by decide
  have hdescent : baseEnd_1656243 < baseStart_1656243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656256 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_1656256 : Nat := 118140960795 + 1656256 * 2 ^ 59
def prefixEnd_1656256 : Nat := 4983230072969 + 3 ^ 40 * 1656256 * 2
def baseEnd_1656256 : Nat := 850455414893177124483023

theorem tailTrace_1656256 : CollatzResearch.WordTrace tailWord_1656256 prefixEnd_1656256 850455414893177124483023 := by
  unfold tailWord_1656256
  simp only [CollatzResearch.WordTrace]
  refine ⟨30204309543837426424898311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40272412725116568566531081 30204309543837426424898311)
  ·
    refine ⟨45306464315756139637347467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30204309543837426424898311 45306464315756139637347467)
    ·
      refine ⟨67959696473634209456021201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45306464315756139637347467 67959696473634209456021201)
      ·
        refine ⟨50969772355225657092015901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67959696473634209456021201 50969772355225657092015901)
        ·
          refine ⟨19113664633209621409505963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50969772355225657092015901 19113664633209621409505963)
          ·
            refine ⟨28670496949814432114258945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19113664633209621409505963 28670496949814432114258945)
            ·
              refine ⟨21502872712360824085694209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28670496949814432114258945 21502872712360824085694209)
              ·
                refine ⟨16127154534270618064270657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21502872712360824085694209 16127154534270618064270657)
                ·
                  refine ⟨12095365900702963548202993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16127154534270618064270657 12095365900702963548202993)
                  ·
                    refine ⟨9071524425527222661152245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12095365900702963548202993 9071524425527222661152245)
                    ·
                      refine ⟨850455414893177124483023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9071524425527222661152245 850455414893177124483023)
                      ·
                        rfl

theorem cell23_1656256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_1656256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656256 prefixEnd_1656256 := by exact prefixLift 1656256
  have htrace : WordTrace (prefixWord ++ tailWord_1656256) baseStart_1656256 baseEnd_1656256 := by
    simpa [prefixWord, tailWord_1656256, baseEnd_1656256] using wordTrace_append hprefix tailTrace_1656256
  have hstable : (prefixWord ++ tailWord_1656256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656256).length < 2 ^ (prefixWord ++ tailWord_1656256).sum := by decide
  have hdescent : baseEnd_1656256 < baseStart_1656256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656270 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2]
def baseStart_1656270 : Nat := 118140960795 + 1656270 * 2 ^ 59
def prefixEnd_1656270 : Nat := 4983230072969 + 3 ^ 40 * 1656270 * 2
def baseEnd_1656270 : Nat := 850462603622340069707959

theorem tailTrace_1656270 : CollatzResearch.WordTrace tailWord_1656270 prefixEnd_1656270 850462603622340069707959 := by
  unfold tailWord_1656270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7551141213703016655100783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40272753139749422160537509 7551141213703016655100783)
  ·
    refine ⟨11326711820554524982651175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7551141213703016655100783 11326711820554524982651175)
    ·
      refine ⟨16990067730831787473976763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11326711820554524982651175 16990067730831787473976763)
      ·
        refine ⟨25485101596247681210965145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16990067730831787473976763 25485101596247681210965145)
        ·
          refine ⟨19113826197185760908223859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25485101596247681210965145 19113826197185760908223859)
          ·
            refine ⟨28670739295778641362335789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19113826197185760908223859 28670739295778641362335789)
            ·
              refine ⟨10751527235916990510875921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28670739295778641362335789 10751527235916990510875921)
              ·
                refine ⟨8063645426937742883156941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10751527235916990510875921 8063645426937742883156941)
                ·
                  refine ⟨3023867035101653581183853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8063645426937742883156941 3023867035101653581183853)
                  ·
                    refine ⟨1133950138163120092943945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023867035101653581183853 1133950138163120092943945)
                    ·
                      refine ⟨850462603622340069707959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133950138163120092943945 850462603622340069707959)
                      ·
                        rfl

theorem cell23_1656270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_1656270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656270 prefixEnd_1656270 := by exact prefixLift 1656270
  have htrace : WordTrace (prefixWord ++ tailWord_1656270) baseStart_1656270 baseEnd_1656270 := by
    simpa [prefixWord, tailWord_1656270, baseEnd_1656270] using wordTrace_append hprefix tailTrace_1656270
  have hstable : (prefixWord ++ tailWord_1656270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656270).length < 2 ^ (prefixWord ++ tailWord_1656270).sum := by decide
  have hdescent : baseEnd_1656270 < baseStart_1656270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656304 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 1, 3, 2]
def baseStart_1656304 : Nat := 118140960795 + 1656304 * 2 ^ 59
def prefixEnd_1656304 : Nat := 4983230072969 + 3 ^ 40 * 1656304 * 2
def baseEnd_1656304 : Nat := 850480061964592936682803

theorem tailTrace_1656304 : CollatzResearch.WordTrace tailWord_1656304 prefixEnd_1656304 850480061964592936682803 := by
  unfold tailWord_1656304
  simp only [CollatzResearch.WordTrace]
  refine ⟨30205184895750478523771983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40273579861000638031695977 30205184895750478523771983)
  ·
    refine ⟨45307777343625717785657975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30205184895750478523771983 45307777343625717785657975)
    ·
      refine ⟨67961666015438576678486963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45307777343625717785657975 67961666015438576678486963)
      ·
        refine ⟨101942499023157865017730445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67961666015438576678486963 101942499023157865017730445)
        ·
          refine ⟨38228437133684199381648917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101942499023157865017730445 38228437133684199381648917)
          ·
            refine ⟨1791957990641446846014793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38228437133684199381648917 1791957990641446846014793)
            ·
              refine ⟨1343968492981085134511095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1791957990641446846014793 1343968492981085134511095)
              ·
                refine ⟨2015952739471627701766643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343968492981085134511095 2015952739471627701766643)
                ·
                  refine ⟨3023929109207441552649965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015952739471627701766643 3023929109207441552649965)
                  ·
                    refine ⟨1133973415952790582243737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023929109207441552649965 1133973415952790582243737)
                    ·
                      refine ⟨850480061964592936682803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133973415952790582243737 850480061964592936682803)
                      ·
                        rfl

theorem cell23_1656304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 3, 2].length) (baseStart_1656304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656304 prefixEnd_1656304 := by exact prefixLift 1656304
  have htrace : WordTrace (prefixWord ++ tailWord_1656304) baseStart_1656304 baseEnd_1656304 := by
    simpa [prefixWord, tailWord_1656304, baseEnd_1656304] using wordTrace_append hprefix tailTrace_1656304
  have hstable : (prefixWord ++ tailWord_1656304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656304).length < 2 ^ (prefixWord ++ tailWord_1656304).sum := by decide
  have hdescent : baseEnd_1656304 < baseStart_1656304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656317 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 4, 2, 2]
def baseStart_1656317 : Nat := 118140960795 + 1656317 * 2 ^ 59
def prefixEnd_1656317 : Nat := 4983230072969 + 3 ^ 40 * 1656317 * 2
def baseEnd_1656317 : Nat := 850486737213101385820243

theorem tailTrace_1656317 : CollatzResearch.WordTrace tailWord_1656317 prefixEnd_1656317 850486737213101385820243 := by
  unfold tailWord_1656317
  simp only [CollatzResearch.WordTrace]
  refine ⟨60410843940453860267767205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40273895960302573511844803 60410843940453860267767205)
  ·
    refine ⟨11327033238835098800206351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60410843940453860267767205 11327033238835098800206351)
    ·
      refine ⟨16990549858252648200309527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11327033238835098800206351 16990549858252648200309527)
      ·
        refine ⟨25485824787378972300464291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16990549858252648200309527 25485824787378972300464291)
        ·
          refine ⟨38228737181068458450696437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25485824787378972300464291 38228737181068458450696437)
          ·
            refine ⟨3583944110725167979752791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38228737181068458450696437 3583944110725167979752791)
            ·
              refine ⟨5375916166087751969629187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583944110725167979752791 5375916166087751969629187)
              ·
                refine ⟨8063874249131627954443781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375916166087751969629187 8063874249131627954443781)
                ·
                  refine ⟨1511976421712180241458209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8063874249131627954443781 1511976421712180241458209)
                  ·
                    refine ⟨1133982316284135181093657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1511976421712180241458209 1133982316284135181093657)
                    ·
                      refine ⟨850486737213101385820243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133982316284135181093657 850486737213101385820243)
                      ·
                        rfl

theorem cell23_1656317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_1656317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656317 prefixEnd_1656317 := by exact prefixLift 1656317
  have htrace : WordTrace (prefixWord ++ tailWord_1656317) baseStart_1656317 baseEnd_1656317 := by
    simpa [prefixWord, tailWord_1656317, baseEnd_1656317] using wordTrace_append hprefix tailTrace_1656317
  have hstable : (prefixWord ++ tailWord_1656317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656317).length < 2 ^ (prefixWord ++ tailWord_1656317).sum := by decide
  have hdescent : baseEnd_1656317 < baseStart_1656317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656334 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2]
def baseStart_1656334 : Nat := 118140960795 + 1656334 * 2 ^ 59
def prefixEnd_1656334 : Nat := 4983230072969 + 3 ^ 40 * 1656334 * 2
def baseEnd_1656334 : Nat := 850495466384227819307665

theorem tailTrace_1656334 : CollatzResearch.WordTrace tailWord_1656334 prefixEnd_1656334 850495466384227819307665 := by
  unfold tailWord_1656334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7551432997674034021392007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40274309320928181447424037 7551432997674034021392007)
  ·
    refine ⟨11327149496511051032088011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7551432997674034021392007 11327149496511051032088011)
    ·
      refine ⟨16990724244766576548132017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11327149496511051032088011 16990724244766576548132017)
      ·
        refine ⟨12743043183574932411099013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16990724244766576548132017 12743043183574932411099013)
        ·
          refine ⟨2389320596920299827081065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12743043183574932411099013 2389320596920299827081065)
          ·
            refine ⟨1791990447690224870310799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2389320596920299827081065 1791990447690224870310799)
            ·
              refine ⟨2687985671535337305466199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791990447690224870310799 2687985671535337305466199)
              ·
                refine ⟨4031978507303005958199299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687985671535337305466199 4031978507303005958199299)
                ·
                  refine ⟨6047967760954508937298949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031978507303005958199299 6047967760954508937298949)
                  ·
                    refine ⟨1133993955178970425743553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6047967760954508937298949 1133993955178970425743553)
                    ·
                      refine ⟨850495466384227819307665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133993955178970425743553 850495466384227819307665)
                      ·
                        rfl

theorem cell23_1656334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_1656334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656334 prefixEnd_1656334 := by exact prefixLift 1656334
  have htrace : WordTrace (prefixWord ++ tailWord_1656334) baseStart_1656334 baseEnd_1656334 := by
    simpa [prefixWord, tailWord_1656334, baseEnd_1656334] using wordTrace_append hprefix tailTrace_1656334
  have hstable : (prefixWord ++ tailWord_1656334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656334).length < 2 ^ (prefixWord ++ tailWord_1656334).sum := by decide
  have hdescent : baseEnd_1656334 < baseStart_1656334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656353 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 1, 7]
def baseStart_1656353 : Nat := 118140960795 + 1656353 * 2 ^ 59
def prefixEnd_1656353 : Nat := 4983230072969 + 3 ^ 40 * 1656353 * 2
def baseEnd_1656353 : Nat := 283501740838887748323359

theorem tailTrace_1656353 : CollatzResearch.WordTrace tailWord_1656353 prefixEnd_1656353 283501740838887748323359 := by
  unfold tailWord_1656353
  simp only [CollatzResearch.WordTrace]
  refine ⟨60412156968323438416077713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40274771312215625610718475 60412156968323438416077713)
  ·
    refine ⟨45309117726242578812058285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60412156968323438416077713 45309117726242578812058285)
    ·
      refine ⟨16990919147340967054521857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45309117726242578812058285 16990919147340967054521857)
      ·
        refine ⟨12743189360505725290891393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16990919147340967054521857 12743189360505725290891393)
        ·
          refine ⟨9557392020379293968168545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12743189360505725290891393 9557392020379293968168545)
          ·
            refine ⟨7168044015284470476126409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9557392020379293968168545 7168044015284470476126409)
            ·
              refine ⟨5376033011463352857094807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7168044015284470476126409 5376033011463352857094807)
              ·
                refine ⟨8064049517195029285642211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5376033011463352857094807 8064049517195029285642211)
                ·
                  refine ⟨12096074275792543928463317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8064049517195029285642211 12096074275792543928463317)
                  ·
                    refine ⟨283501740838887748323359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12096074275792543928463317 283501740838887748323359)
                    ·
                      rfl

theorem cell23_1656353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_1656353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656353 prefixEnd_1656353 := by exact prefixLift 1656353
  have htrace : WordTrace (prefixWord ++ tailWord_1656353) baseStart_1656353 baseEnd_1656353 := by
    simpa [prefixWord, tailWord_1656353, baseEnd_1656353] using wordTrace_append hprefix tailTrace_1656353
  have hstable : (prefixWord ++ tailWord_1656353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656353).length < 2 ^ (prefixWord ++ tailWord_1656353).sum := by decide
  have hdescent : baseEnd_1656353 < baseStart_1656353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656374 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_1656374 : Nat := 118140960795 + 1656374 * 2 ^ 59
def prefixEnd_1656374 : Nat := 4983230072969 + 3 ^ 40 * 1656374 * 2
def baseEnd_1656374 : Nat := 94501778401156406978609

theorem tailTrace_1656374 : CollatzResearch.WordTrace tailWord_1656374 prefixEnd_1656374 94501778401156406978609 := by
  unfold tailWord_1656374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775807681327959937662011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40275281934164906001728117 3775807681327959937662011)
  ·
    refine ⟨5663711521991939906493017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3775807681327959937662011 5663711521991939906493017)
    ·
      refine ⟨4247783641493954929869763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5663711521991939906493017 4247783641493954929869763)
      ·
        refine ⟨6371675462240932394804645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4247783641493954929869763 6371675462240932394804645)
        ·
          refine ⟨1194689149170174824025871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6371675462240932394804645 1194689149170174824025871)
          ·
            refine ⟨1792033723755262236038807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194689149170174824025871 1792033723755262236038807)
            ·
              refine ⟨2688050585632893354058211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792033723755262236038807 2688050585632893354058211)
              ·
                refine ⟨4032075878449340031087317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688050585632893354058211 4032075878449340031087317)
                ·
                  refine ⟨94501778401156406978609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4032075878449340031087317 94501778401156406978609)
                  ·
                    rfl

theorem cell23_1656374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_1656374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656374 prefixEnd_1656374 := by exact prefixLift 1656374
  have htrace : WordTrace (prefixWord ++ tailWord_1656374) baseStart_1656374 baseEnd_1656374 := by
    simpa [prefixWord, tailWord_1656374, baseEnd_1656374] using wordTrace_append hprefix tailTrace_1656374
  have hstable : (prefixWord ++ tailWord_1656374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656374).length < 2 ^ (prefixWord ++ tailWord_1656374).sum := by decide
  have hdescent : baseEnd_1656374 < baseStart_1656374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656380 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_1656380 : Nat := 118140960795 + 1656380 * 2 ^ 59
def prefixEnd_1656380 : Nat := 4983230072969 + 3 ^ 40 * 1656380 * 2
def baseEnd_1656380 : Nat := 850519086494334639332453

theorem tailTrace_1656380 : CollatzResearch.WordTrace tailWord_1656380 prefixEnd_1656380 850519086494334639332453 := by
  unfold tailWord_1656380
  simp only [CollatzResearch.WordTrace]
  refine ⟨30206570869612811013655297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40275427826150414684873729 30206570869612811013655297)
  ·
    refine ⟨22654928152209608260241473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30206570869612811013655297 22654928152209608260241473)
    ·
      refine ⟨16991196114157206195181105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22654928152209608260241473 16991196114157206195181105)
      ·
        refine ⟨12743397085617904646385829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16991196114157206195181105 12743397085617904646385829)
        ·
          refine ⟨2389386953553357121197343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12743397085617904646385829 2389386953553357121197343)
          ·
            refine ⟨3584080430330035681796015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389386953553357121197343 3584080430330035681796015)
            ·
              refine ⟨5376120645495053522694023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3584080430330035681796015 5376120645495053522694023)
              ·
                refine ⟨8064180968242580284041035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5376120645495053522694023 8064180968242580284041035)
                ·
                  refine ⟨12096271452363870426061553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8064180968242580284041035 12096271452363870426061553)
                  ·
                    refine ⟨9072203589272902819546165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12096271452363870426061553 9072203589272902819546165)
                    ·
                      refine ⟨850519086494334639332453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9072203589272902819546165 850519086494334639332453)
                      ·
                        rfl

theorem cell23_1656380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_1656380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656380 prefixEnd_1656380 := by exact prefixLift 1656380
  have htrace : WordTrace (prefixWord ++ tailWord_1656380) baseStart_1656380 baseEnd_1656380 := by
    simpa [prefixWord, tailWord_1656380, baseEnd_1656380] using wordTrace_append hprefix tailTrace_1656380
  have hstable : (prefixWord ++ tailWord_1656380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656380).length < 2 ^ (prefixWord ++ tailWord_1656380).sum := by decide
  have hdescent : baseEnd_1656380 < baseStart_1656380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656393 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 3, 4, 3]
def baseStart_1656393 : Nat := 118140960795 + 1656393 * 2 ^ 59
def prefixEnd_1656393 : Nat := 4983230072969 + 3 ^ 40 * 1656393 * 2
def baseEnd_1656393 : Nat := 850525761742843088469893

theorem tailTrace_1656393 : CollatzResearch.WordTrace tailWord_1656393 prefixEnd_1656393 850525761742843088469893 := by
  unfold tailWord_1656393
  simp only [CollatzResearch.WordTrace]
  refine ⟨60413615888178525247533833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40275743925452350165022555 60413615888178525247533833)
  ·
    refine ⟨45310211916133893935650375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60413615888178525247533833 45310211916133893935650375)
    ·
      refine ⟨67965317874200840903475563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45310211916133893935650375 67965317874200840903475563)
      ·
        refine ⟨101947976811301261355213345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67965317874200840903475563 101947976811301261355213345)
        ·
          refine ⟨76460982608475946016410009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101947976811301261355213345 76460982608475946016410009)
          ·
            refine ⟨57345736956356959512307507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76460982608475946016410009 57345736956356959512307507)
            ·
              refine ⟨86018605434535439268461261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57345736956356959512307507 86018605434535439268461261)
              ·
                refine ⟨32256977037950789725672973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86018605434535439268461261 32256977037950789725672973)
                ·
                  refine ⟨12096366389231546147127365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32256977037950789725672973 12096366389231546147127365)
                  ·
                    refine ⟨2268068697980914902586381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12096366389231546147127365 2268068697980914902586381)
                    ·
                      refine ⟨850525761742843088469893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2268068697980914902586381 850525761742843088469893)
                      ·
                        rfl

theorem cell23_1656393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4, 3].length) (baseStart_1656393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656393 prefixEnd_1656393 := by exact prefixLift 1656393
  have htrace : WordTrace (prefixWord ++ tailWord_1656393) baseStart_1656393 baseEnd_1656393 := by
    simpa [prefixWord, tailWord_1656393, baseEnd_1656393] using wordTrace_append hprefix tailTrace_1656393
  have hstable : (prefixWord ++ tailWord_1656393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656393).length < 2 ^ (prefixWord ++ tailWord_1656393).sum := by decide
  have hdescent : baseEnd_1656393 < baseStart_1656393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656417 : List Nat := [1, 2, 3, 1, 1, 3, 2, 5, 1, 4]
def baseStart_1656417 : Nat := 118140960795 + 1656417 * 2 ^ 59
def prefixEnd_1656417 : Nat := 4983230072969 + 3 ^ 40 * 1656417 * 2
def baseEnd_1656417 : Nat := 283512695092850331523261

theorem tailTrace_1656417 : CollatzResearch.WordTrace tailWord_1656417 prefixEnd_1656417 283512695092850331523261 := by
  unfold tailWord_1656417
  simp only [CollatzResearch.WordTrace]
  refine ⟨60414491240091577346407505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40276327493394384897605003 60414491240091577346407505)
  ·
    refine ⟨45310868430068683009805629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60414491240091577346407505 45310868430068683009805629)
    ·
      refine ⟨16991575661275756128677111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45310868430068683009805629 16991575661275756128677111)
      ·
        refine ⟨25487363491913634193015667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16991575661275756128677111 25487363491913634193015667)
        ·
          refine ⟨38231045237870451289523501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25487363491913634193015667 38231045237870451289523501)
          ·
            refine ⟨14336641964201419233571313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38231045237870451289523501 14336641964201419233571313)
            ·
              refine ⟨10752481473151064425178485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14336641964201419233571313 10752481473151064425178485)
              ·
                refine ⟨1008045138107912289860483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10752481473151064425178485 1008045138107912289860483)
                ·
                  refine ⟨1512067707161868434790725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008045138107912289860483 1512067707161868434790725)
                  ·
                    refine ⟨283512695092850331523261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1512067707161868434790725 283512695092850331523261)
                    ·
                      rfl

theorem cell23_1656417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_1656417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656417 prefixEnd_1656417 := by exact prefixLift 1656417
  have htrace : WordTrace (prefixWord ++ tailWord_1656417) baseStart_1656417 baseEnd_1656417 := by
    simpa [prefixWord, tailWord_1656417, baseEnd_1656417] using wordTrace_append hprefix tailTrace_1656417
  have hstable : (prefixWord ++ tailWord_1656417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656417).length < 2 ^ (prefixWord ++ tailWord_1656417).sum := by decide
  have hdescent : baseEnd_1656417 < baseStart_1656417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656434 : List Nat := [3, 2, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_1656434 : Nat := 118140960795 + 1656434 * 2 ^ 59
def prefixEnd_1656434 : Nat := 4983230072969 + 3 ^ 40 * 1656434 * 2
def baseEnd_1656434 : Nat := 283515604816559142685735

theorem tailTrace_1656434 : CollatzResearch.WordTrace tailWord_1656434 prefixEnd_1656434 283515604816559142685735 := by
  unfold tailWord_1656434
  simp only [CollatzResearch.WordTrace]
  refine ⟨15103777820257497312444089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40276740854019992833184237 15103777820257497312444089)
  ·
    refine ⟨11327833365193122984333067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15103777820257497312444089 11327833365193122984333067)
    ·
      refine ⟨16991750047789684476499601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11327833365193122984333067 16991750047789684476499601)
      ·
        refine ⟨12743812535842263357374701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16991750047789684476499601 12743812535842263357374701)
        ·
          refine ⟨4778929700940848759015513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12743812535842263357374701 4778929700940848759015513)
          ·
            refine ⟨3584197275705636569261635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4778929700940848759015513 3584197275705636569261635)
            ·
              refine ⟨5376295913558454853892453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3584197275705636569261635 5376295913558454853892453)
              ·
                refine ⟨1008055483792210285104835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5376295913558454853892453 1008055483792210285104835)
                ·
                  refine ⟨1512083225688315427657253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008055483792210285104835 1512083225688315427657253)
                  ·
                    refine ⟨283515604816559142685735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1512083225688315427657253 283515604816559142685735)
                    ·
                      rfl

theorem cell23_1656434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_1656434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656434 prefixEnd_1656434 := by exact prefixLift 1656434
  have htrace : WordTrace (prefixWord ++ tailWord_1656434) baseStart_1656434 baseEnd_1656434 := by
    simpa [prefixWord, tailWord_1656434, baseEnd_1656434] using wordTrace_append hprefix tailTrace_1656434
  have hstable : (prefixWord ++ tailWord_1656434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656434).length < 2 ^ (prefixWord ++ tailWord_1656434).sum := by decide
  have hdescent : baseEnd_1656434 < baseStart_1656434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656443 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 5, 5]
def baseStart_1656443 : Nat := 118140960795 + 1656443 * 2 ^ 59
def prefixEnd_1656443 : Nat := 4983230072969 + 3 ^ 40 * 1656443 * 2
def baseEnd_1656443 : Nat := 283517145258522630948221

theorem tailTrace_1656443 : CollatzResearch.WordTrace tailWord_1656443 prefixEnd_1656443 283517145258522630948221 := by
  unfold tailWord_1656443
  simp only [CollatzResearch.WordTrace]
  refine ⟨60415439537997383786853983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40276959691998255857902655 60415439537997383786853983)
  ·
    refine ⟨90623159306996075680280975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60415439537997383786853983 90623159306996075680280975)
    ·
      refine ⟨135934738960494113520421463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90623159306996075680280975 135934738960494113520421463)
      ·
        refine ⟨203902108440741170280632195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135934738960494113520421463 203902108440741170280632195)
        ·
          refine ⟨305853162661111755420948293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203902108440741170280632195 305853162661111755420948293)
          ·
            refine ⟨57347467998958454141427805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305853162661111755420948293 57347467998958454141427805)
            ·
              refine ⟨21505300499609420303035427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57347467998958454141427805 21505300499609420303035427)
              ·
                refine ⟨32257950749414130454553141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21505300499609420303035427 32257950749414130454553141)
                ·
                  refine ⟨3024182882757574730114357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32257950749414130454553141 3024182882757574730114357)
                  ·
                    refine ⟨283517145258522630948221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3024182882757574730114357 283517145258522630948221)
                    ·
                      rfl

theorem cell23_1656443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 5].length) (baseStart_1656443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656443 prefixEnd_1656443 := by exact prefixLift 1656443
  have htrace : WordTrace (prefixWord ++ tailWord_1656443) baseStart_1656443 baseEnd_1656443 := by
    simpa [prefixWord, tailWord_1656443, baseEnd_1656443] using wordTrace_append hprefix tailTrace_1656443
  have hstable : (prefixWord ++ tailWord_1656443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656443).length < 2 ^ (prefixWord ++ tailWord_1656443).sum := by decide
  have hdescent : baseEnd_1656443 < baseStart_1656443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656453 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_1656453 : Nat := 118140960795 + 1656453 * 2 ^ 59
def prefixEnd_1656453 : Nat := 4983230072969 + 3 ^ 40 * 1656453 * 2
def baseEnd_1656453 : Nat := 850556570582112853719617

theorem tailTrace_1656453 : CollatzResearch.WordTrace tailWord_1656453 prefixEnd_1656453 850556570582112853719617 := by
  unfold tailWord_1656453
  simp only [CollatzResearch.WordTrace]
  refine ⟨60415804267961155494718013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40277202845307436996478675 60415804267961155494718013)
  ·
    refine ⟨22655926600485433310519255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60415804267961155494718013 22655926600485433310519255)
    ·
      refine ⟨33983889900728149965778883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22655926600485433310519255 33983889900728149965778883)
      ·
        refine ⟨50975834851092224948668325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33983889900728149965778883 50975834851092224948668325)
        ·
          refine ⟨9557969034579792177875311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50975834851092224948668325 9557969034579792177875311)
          ·
            refine ⟨14336953551869688266812967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9557969034579792177875311 14336953551869688266812967)
            ·
              refine ⟨21505430327804532400219451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14336953551869688266812967 21505430327804532400219451)
              ·
                refine ⟨32258145491706798600329177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21505430327804532400219451 32258145491706798600329177)
                ·
                  refine ⟨24193609118780098950246883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32258145491706798600329177 24193609118780098950246883)
                  ·
                    refine ⟨36290413678170148425370325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24193609118780098950246883 36290413678170148425370325)
                    ·
                      refine ⟨850556570582112853719617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36290413678170148425370325 850556570582112853719617)
                      ·
                        rfl

theorem cell23_1656453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_1656453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656453 prefixEnd_1656453 := by exact prefixLift 1656453
  have htrace : WordTrace (prefixWord ++ tailWord_1656453) baseStart_1656453 baseEnd_1656453 := by
    simpa [prefixWord, tailWord_1656453, baseEnd_1656453] using wordTrace_append hprefix tailTrace_1656453
  have hstable : (prefixWord ++ tailWord_1656453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656453).length < 2 ^ (prefixWord ++ tailWord_1656453).sum := by decide
  have hdescent : baseEnd_1656453 < baseStart_1656453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656460 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 1, 5]
def baseStart_1656460 : Nat := 118140960795 + 1656460 * 2 ^ 59
def prefixEnd_1656460 : Nat := 4983230072969 + 3 ^ 40 * 1656460 * 2
def baseEnd_1656460 : Nat := 283520054982231442110695

theorem tailTrace_1656460 : CollatzResearch.WordTrace tailWord_1656460 prefixEnd_1656460 283520054982231442110695 := by
  unfold tailWord_1656460
  simp only [CollatzResearch.WordTrace]
  refine ⟨30208029789467897845111417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40277373052623863793481889 30208029789467897845111417)
  ·
    refine ⟨22656022342100923383833563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30208029789467897845111417 22656022342100923383833563)
    ·
      refine ⟨33984033513151385075750345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22656022342100923383833563 33984033513151385075750345)
      ·
        refine ⟨25488025134863538806812759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33984033513151385075750345 25488025134863538806812759)
        ·
          refine ⟨38232037702295308210219139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25488025134863538806812759 38232037702295308210219139)
          ·
            refine ⟨57348056553442962315328709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38232037702295308210219139 57348056553442962315328709)
            ·
              refine ⟨10752760603770555434124133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57348056553442962315328709 10752760603770555434124133)
              ·
                refine ⟨2016142613206979143898275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10752760603770555434124133 2016142613206979143898275)
                ·
                  refine ⟨3024213919810468715847413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016142613206979143898275 3024213919810468715847413)
                  ·
                    refine ⟨283520054982231442110695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3024213919810468715847413 283520054982231442110695)
                    ·
                      rfl

theorem cell23_1656460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_1656460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656460 prefixEnd_1656460 := by exact prefixLift 1656460
  have htrace : WordTrace (prefixWord ++ tailWord_1656460) baseStart_1656460 baseEnd_1656460 := by
    simpa [prefixWord, tailWord_1656460, baseEnd_1656460] using wordTrace_append hprefix tailTrace_1656460
  have hstable : (prefixWord ++ tailWord_1656460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656460).length < 2 ^ (prefixWord ++ tailWord_1656460).sum := by decide
  have hdescent : baseEnd_1656460 < baseStart_1656460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656473 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 3, 6]
def baseStart_1656473 : Nat := 118140960795 + 1656473 * 2 ^ 59
def prefixEnd_1656473 : Nat := 4983230072969 + 3 ^ 40 * 1656473 * 2
def baseEnd_1656473 : Nat := 283522280065067591823175

theorem tailTrace_1656473 : CollatzResearch.WordTrace tailWord_1656473 prefixEnd_1656473 283522280065067591823175 := by
  unfold tailWord_1656473
  simp only [CollatzResearch.WordTrace]
  refine ⟨60416533727888698910446073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40277689151925799273630715 60416533727888698910446073)
  ·
    refine ⟨45312400295916524182834555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60416533727888698910446073 45312400295916524182834555)
    ·
      refine ⟨67968600443874786274251833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45312400295916524182834555 67968600443874786274251833)
      ·
        refine ⟨50976450332906089705688875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67968600443874786274251833 50976450332906089705688875)
        ·
          refine ⟨76464675499359134558533313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50976450332906089705688875 76464675499359134558533313)
          ·
            refine ⟨57348506624519350918899985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76464675499359134558533313 57348506624519350918899985)
            ·
              refine ⟨43011379968389513189174989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57348506624519350918899985 43011379968389513189174989)
              ·
                refine ⟨16129267488146067445940621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43011379968389513189174989 16129267488146067445940621)
                ·
                  refine ⟨6048475308054775292227733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16129267488146067445940621 6048475308054775292227733)
                  ·
                    refine ⟨283522280065067591823175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6048475308054775292227733 283522280065067591823175)
                    ·
                      rfl

theorem cell23_1656473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_1656473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656473 prefixEnd_1656473 := by exact prefixLift 1656473
  have htrace : WordTrace (prefixWord ++ tailWord_1656473) baseStart_1656473 baseEnd_1656473 := by
    simpa [prefixWord, tailWord_1656473, baseEnd_1656473] using wordTrace_append hprefix tailTrace_1656473
  have hstable : (prefixWord ++ tailWord_1656473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656473).length < 2 ^ (prefixWord ++ tailWord_1656473).sum := by decide
  have hdescent : baseEnd_1656473 < baseStart_1656473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656523 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 6]
def baseStart_1656523 : Nat := 118140960795 + 1656523 * 2 ^ 59
def prefixEnd_1656523 : Nat := 4983230072969 + 3 ^ 40 * 1656523 * 2
def baseEnd_1656523 : Nat := 850592514227927579844295

theorem tailTrace_1656523 : CollatzResearch.WordTrace tailWord_1656523 prefixEnd_1656523 850592514227927579844295 := by
  unfold tailWord_1656523
  simp only [CollatzResearch.WordTrace]
  refine ⟨60418357377707557449766223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40278904918471704966510815 60418357377707557449766223)
  ·
    refine ⟨90627536066561336174649335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60418357377707557449766223 90627536066561336174649335)
    ·
      refine ⟨135941304099842004261974003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90627536066561336174649335 135941304099842004261974003)
      ·
        refine ⟨203911956149763006392961005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135941304099842004261974003 203911956149763006392961005)
        ·
          refine ⟨76466983556161127397360377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203911956149763006392961005 76466983556161127397360377)
          ·
            refine ⟨57350237667120845548020283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76466983556161127397360377 57350237667120845548020283)
            ·
              refine ⟨86025356500681268322030425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57350237667120845548020283 86025356500681268322030425)
              ·
                refine ⟨64519017375510951241522819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86025356500681268322030425 64519017375510951241522819)
                ·
                  refine ⟨96778526063266426862284229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64519017375510951241522819 96778526063266426862284229)
                  ·
                    refine ⟨18145973636862455036678293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96778526063266426862284229 18145973636862455036678293)
                    ·
                      refine ⟨850592514227927579844295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18145973636862455036678293 850592514227927579844295)
                      ·
                        rfl

theorem cell23_1656523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_1656523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656523 prefixEnd_1656523 := by exact prefixLift 1656523
  have htrace : WordTrace (prefixWord ++ tailWord_1656523) baseStart_1656523 baseEnd_1656523 := by
    simpa [prefixWord, tailWord_1656523, baseEnd_1656523] using wordTrace_append hprefix tailTrace_1656523
  have hstable : (prefixWord ++ tailWord_1656523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656523).length < 2 ^ (prefixWord ++ tailWord_1656523).sum := by decide
  have hdescent : baseEnd_1656523 < baseStart_1656523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656525 : List Nat := [1, 6, 2, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_1656525 : Nat := 118140960795 + 1656525 * 2 ^ 59
def prefixEnd_1656525 : Nat := 4983230072969 + 3 ^ 40 * 1656525 * 2
def baseEnd_1656525 : Nat := 850593541189236572019287

theorem tailTrace_1656525 : CollatzResearch.WordTrace tailWord_1656525 prefixEnd_1656525 850593541189236572019287 := by
  unfold tailWord_1656525
  simp only [CollatzResearch.WordTrace]
  refine ⟨60418430323700311791339029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40278953549133541194226019 60418430323700311791339029)
  ·
    refine ⟨2832113921423452115219017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60418430323700311791339029 2832113921423452115219017)
    ·
      refine ⟨2124085441067589086414263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2832113921423452115219017 2124085441067589086414263)
      ·
        refine ⟨3186128161601383629621395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2124085441067589086414263 3186128161601383629621395)
        ·
          refine ⟨4779192242402075444432093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3186128161601383629621395 4779192242402075444432093)
          ·
            refine ⟨1792197090900778291662035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4779192242402075444432093 1792197090900778291662035)
            ·
              refine ⟨2688295636351167437493053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792197090900778291662035 2688295636351167437493053)
              ·
                refine ⟨1008110863631687789059895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2688295636351167437493053 1008110863631687789059895)
                ·
                  refine ⟨1512166295447531683589843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008110863631687789059895 1512166295447531683589843)
                  ·
                    refine ⟨2268249443171297525384765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1512166295447531683589843 2268249443171297525384765)
                    ·
                      refine ⟨850593541189236572019287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2268249443171297525384765 850593541189236572019287)
                      ·
                        rfl

theorem cell23_1656525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_1656525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656525 prefixEnd_1656525 := by exact prefixLift 1656525
  have htrace : WordTrace (prefixWord ++ tailWord_1656525) baseStart_1656525 baseEnd_1656525 := by
    simpa [prefixWord, tailWord_1656525, baseEnd_1656525] using wordTrace_append hprefix tailTrace_1656525
  have hstable : (prefixWord ++ tailWord_1656525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656525).length < 2 ^ (prefixWord ++ tailWord_1656525).sum := by decide
  have hdescent : baseEnd_1656525 < baseStart_1656525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656548 : List Nat := [2, 3, 1, 1, 1, 3, 5, 2, 1, 2, 2]
def baseStart_1656548 : Nat := 118140960795 + 1656548 * 2 ^ 59
def prefixEnd_1656548 : Nat := 4983230072969 + 3 ^ 40 * 1656548 * 2
def baseEnd_1656548 : Nat := 850605351244289982031681

theorem tailTrace_1656548 : CollatzResearch.WordTrace tailWord_1656548 prefixEnd_1656548 850605351244289982031681 := by
  unfold tailWord_1656548
  simp only [CollatzResearch.WordTrace]
  refine ⟨30209634601308493359713149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40279512801744657812950865 30209634601308493359713149)
  ·
    refine ⟨11328612975490685009892431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30209634601308493359713149 11328612975490685009892431)
    ·
      refine ⟨16992919463236027514838647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11328612975490685009892431 16992919463236027514838647)
      ·
        refine ⟨25489379194854041272257971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16992919463236027514838647 25489379194854041272257971)
        ·
          refine ⟨38234068792281061908386957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25489379194854041272257971 38234068792281061908386957)
          ·
            refine ⟨14337775797105398215645109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38234068792281061908386957 14337775797105398215645109)
            ·
              refine ⟨1344166480978631082716729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14337775797105398215645109 1344166480978631082716729)
              ·
                refine ⟨1008124860733973312037547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1344166480978631082716729 1008124860733973312037547)
                ·
                  refine ⟨1512187291100959968056321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008124860733973312037547 1512187291100959968056321)
                  ·
                    refine ⟨1134140468325719976042241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1512187291100959968056321 1134140468325719976042241)
                    ·
                      refine ⟨850605351244289982031681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134140468325719976042241 850605351244289982031681)
                      ·
                        rfl

theorem cell23_1656548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_1656548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656548 prefixEnd_1656548 := by exact prefixLift 1656548
  have htrace : WordTrace (prefixWord ++ tailWord_1656548) baseStart_1656548 baseEnd_1656548 := by
    simpa [prefixWord, tailWord_1656548, baseEnd_1656548] using wordTrace_append hprefix tailTrace_1656548
  have hstable : (prefixWord ++ tailWord_1656548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656548).length < 2 ^ (prefixWord ++ tailWord_1656548).sum := by decide
  have hdescent : baseEnd_1656548 < baseStart_1656548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656587 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 3, 4, 2]
def baseStart_1656587 : Nat := 118140960795 + 1656587 * 2 ^ 59
def prefixEnd_1656587 : Nat := 4983230072969 + 3 ^ 40 * 1656587 * 2
def baseEnd_1656587 : Nat := 850625376989815329444001

theorem tailTrace_1656587 : CollatzResearch.WordTrace tailWord_1656587 prefixEnd_1656587 850625376989815329444001 := by
  unfold tailWord_1656587
  simp only [CollatzResearch.WordTrace]
  refine ⟨60420691649475696380096015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40280461099650464253397343 60420691649475696380096015)
  ·
    refine ⟨90631037474213544570144023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60420691649475696380096015 90631037474213544570144023)
    ·
      refine ⟨135946556211320316855216035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90631037474213544570144023 135946556211320316855216035)
      ·
        refine ⟨203919834316980475282824053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135946556211320316855216035 203919834316980475282824053)
        ·
          refine ⟨19117484467216919557764755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203919834316980475282824053 19117484467216919557764755)
          ·
            refine ⟨28676226700825379336647133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19117484467216919557764755 28676226700825379336647133)
            ·
              refine ⟨10753585012809517251242675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28676226700825379336647133 10753585012809517251242675)
              ·
                refine ⟨16130377519214275876864013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10753585012809517251242675 16130377519214275876864013)
                ·
                  refine ⟨6048891569705353453824005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16130377519214275876864013 6048891569705353453824005)
                  ·
                    refine ⟨1134167169319753772592001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048891569705353453824005 1134167169319753772592001)
                    ·
                      refine ⟨850625376989815329444001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134167169319753772592001 850625376989815329444001)
                      ·
                        rfl

theorem cell23_1656587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 4, 2].length) (baseStart_1656587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656587 prefixEnd_1656587 := by exact prefixLift 1656587
  have htrace : WordTrace (prefixWord ++ tailWord_1656587) baseStart_1656587 baseEnd_1656587 := by
    simpa [prefixWord, tailWord_1656587, baseEnd_1656587] using wordTrace_append hprefix tailTrace_1656587
  have hstable : (prefixWord ++ tailWord_1656587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656587).length < 2 ^ (prefixWord ++ tailWord_1656587).sum := by decide
  have hdescent : baseEnd_1656587 < baseStart_1656587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656627 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 7]
def baseStart_1656627 : Nat := 118140960795 + 1656627 * 2 ^ 59
def prefixEnd_1656627 : Nat := 4983230072969 + 3 ^ 40 * 1656627 * 2
def baseEnd_1656627 : Nat := 94516212912888352549313

theorem tailTrace_1656627 : CollatzResearch.WordTrace tailWord_1656627 prefixEnd_1656627 94516212912888352549313 := by
  unfold tailWord_1656627
  simp only [CollatzResearch.WordTrace]
  refine ⟨60422150569330783211552135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40281433712887188807701423 60422150569330783211552135)
  ·
    refine ⟨90633225853996174817328203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60422150569330783211552135 90633225853996174817328203)
    ·
      refine ⟨135949838780994262225992305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90633225853996174817328203 135949838780994262225992305)
      ·
        refine ⟨101962379085745696669494229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135949838780994262225992305 101962379085745696669494229)
        ·
          refine ⟨2389743259822164765691271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 101962379085745696669494229 2389743259822164765691271)
          ·
            refine ⟨3584614889733247148536907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389743259822164765691271 3584614889733247148536907)
            ·
              refine ⟨5376922334599870722805361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3584614889733247148536907 5376922334599870722805361)
              ·
                refine ⟨4032691750949903042104021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5376922334599870722805361 4032691750949903042104021)
                ·
                  refine ⟨94516212912888352549313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4032691750949903042104021 94516212912888352549313)
                  ·
                    rfl

theorem cell23_1656627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 7].length) (baseStart_1656627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656627 prefixEnd_1656627 := by exact prefixLift 1656627
  have htrace : WordTrace (prefixWord ++ tailWord_1656627) baseStart_1656627 baseEnd_1656627 := by
    simpa [prefixWord, tailWord_1656627, baseEnd_1656627] using wordTrace_append hprefix tailTrace_1656627
  have hstable : (prefixWord ++ tailWord_1656627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656627).length < 2 ^ (prefixWord ++ tailWord_1656627).sum := by decide
  have hdescent : baseEnd_1656627 < baseStart_1656627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656697 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 1, 4, 3]
def baseStart_1656697 : Nat := 118140960795 + 1656697 * 2 ^ 59
def prefixEnd_1656697 : Nat := 4983230072969 + 3 ^ 40 * 1656697 * 2
def baseEnd_1656697 : Nat := 850681859861809899068495

theorem tailTrace_1656697 : CollatzResearch.WordTrace tailWord_1656697 prefixEnd_1656697 850681859861809899068495 := by
  unfold tailWord_1656697
  simp only [CollatzResearch.WordTrace]
  refine ⟨60424703679077185166600345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40283135786051456777733563 60424703679077185166600345)
  ·
    refine ⟨45318527759307888874950259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60424703679077185166600345 45318527759307888874950259)
    ·
      refine ⟨67977791638961833312425389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45318527759307888874950259 67977791638961833312425389)
      ·
        refine ⟨25491671864610687492159521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67977791638961833312425389 25491671864610687492159521)
        ·
          refine ⟨19118753898458015619119641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25491671864610687492159521 19118753898458015619119641)
          ·
            refine ⟨14339065423843511714339731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19118753898458015619119641 14339065423843511714339731)
            ·
              refine ⟨21508598135765267571509597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14339065423843511714339731 21508598135765267571509597)
              ·
                refine ⟨8065724300911975339316099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21508598135765267571509597 8065724300911975339316099)
                ·
                  refine ⟨12098586451367963008974149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8065724300911975339316099 12098586451367963008974149)
                  ·
                    refine ⟨2268484959631493064182653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12098586451367963008974149 2268484959631493064182653)
                    ·
                      refine ⟨850681859861809899068495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2268484959631493064182653 850681859861809899068495)
                      ·
                        rfl

theorem cell23_1656697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_1656697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656697 prefixEnd_1656697 := by exact prefixLift 1656697
  have htrace : WordTrace (prefixWord ++ tailWord_1656697) baseStart_1656697 baseEnd_1656697 := by
    simpa [prefixWord, tailWord_1656697, baseEnd_1656697] using wordTrace_append hprefix tailTrace_1656697
  have hstable : (prefixWord ++ tailWord_1656697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656697).length < 2 ^ (prefixWord ++ tailWord_1656697).sum := by decide
  have hdescent : baseEnd_1656697 < baseStart_1656697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656754 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2]
def baseStart_1656754 : Nat := 118140960795 + 1656754 * 2 ^ 59
def prefixEnd_1656754 : Nat := 4983230072969 + 3 ^ 40 * 1656754 * 2
def baseEnd_1656754 : Nat := 850711128259116176055733

theorem tailTrace_1656754 : CollatzResearch.WordTrace tailWord_1656754 prefixEnd_1656754 850711128259116176055733 := by
  unfold tailWord_1656754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15106695659967670975356329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40284521759913789267616877 15106695659967670975356329)
  ·
    refine ⟨11330021744975753231517247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15106695659967670975356329 11330021744975753231517247)
    ·
      refine ⟨16995032617463629847275871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11330021744975753231517247 16995032617463629847275871)
      ·
        refine ⟨25492548926195444770913807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16995032617463629847275871 25492548926195444770913807)
        ·
          refine ⟨38238823389293167156370711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25492548926195444770913807 38238823389293167156370711)
          ·
            refine ⟨57358235083939750734556067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38238823389293167156370711 57358235083939750734556067)
            ·
              refine ⟨86037352625909626101834101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57358235083939750734556067 86037352625909626101834101)
              ·
                refine ⟨8066001808679027447046947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86037352625909626101834101 8066001808679027447046947)
                ·
                  refine ⟨12099002713018541170570421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8066001808679027447046947 12099002713018541170570421)
                  ·
                    refine ⟨1134281504345488234740977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12099002713018541170570421 1134281504345488234740977)
                    ·
                      refine ⟨850711128259116176055733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134281504345488234740977 850711128259116176055733)
                      ·
                        rfl

theorem cell23_1656754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_1656754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656754 prefixEnd_1656754 := by exact prefixLift 1656754
  have htrace : WordTrace (prefixWord ++ tailWord_1656754) baseStart_1656754 baseEnd_1656754 := by
    simpa [prefixWord, tailWord_1656754, baseEnd_1656754] using wordTrace_append hprefix tailTrace_1656754
  have hstable : (prefixWord ++ tailWord_1656754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656754).length < 2 ^ (prefixWord ++ tailWord_1656754).sum := by decide
  have hdescent : baseEnd_1656754 < baseStart_1656754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656801 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 5, 2, 2]
def baseStart_1656801 : Nat := 118140960795 + 1656801 * 2 ^ 59
def prefixEnd_1656801 : Nat := 4983230072969 + 3 ^ 40 * 1656801 * 2
def baseEnd_1656801 : Nat := 850735261849877492168017

theorem tailTrace_1656801 : CollatzResearch.WordTrace tailWord_1656801 prefixEnd_1656801 850735261849877492168017 := by
  unfold tailWord_1656801
  simp only [CollatzResearch.WordTrace]
  refine ⟨60428496870700410928386257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40285664580466940618924171 60428496870700410928386257)
  ·
    refine ⟨45321372653025308196289693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60428496870700410928386257 45321372653025308196289693)
    ·
      refine ⟨16995514744884490573608635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45321372653025308196289693 16995514744884490573608635)
      ·
        refine ⟨25493272117326735860412953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16995514744884490573608635 25493272117326735860412953)
        ·
          refine ⟨19119954087995051895309715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25493272117326735860412953 19119954087995051895309715)
          ·
            refine ⟨28679931131992577842964573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19119954087995051895309715 28679931131992577842964573)
            ·
              refine ⟨10754974174497216691111715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28679931131992577842964573 10754974174497216691111715)
              ·
                refine ⟨16132461261745825036667573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10754974174497216691111715 16132461261745825036667573)
                ·
                  refine ⟨1512418243288671097187585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16132461261745825036667573 1512418243288671097187585)
                  ·
                    refine ⟨1134313682466503322890689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1512418243288671097187585 1134313682466503322890689)
                    ·
                      refine ⟨850735261849877492168017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134313682466503322890689 850735261849877492168017)
                      ·
                        rfl

theorem cell23_1656801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_1656801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656801 prefixEnd_1656801 := by exact prefixLift 1656801
  have htrace : WordTrace (prefixWord ++ tailWord_1656801) baseStart_1656801 baseEnd_1656801 := by
    simpa [prefixWord, tailWord_1656801, baseEnd_1656801] using wordTrace_append hprefix tailTrace_1656801
  have hstable : (prefixWord ++ tailWord_1656801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656801).length < 2 ^ (prefixWord ++ tailWord_1656801).sum := by decide
  have hdescent : baseEnd_1656801 < baseStart_1656801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656804 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_1656804 : Nat := 118140960795 + 1656804 * 2 ^ 59
def prefixEnd_1656804 : Nat := 4983230072969 + 3 ^ 40 * 1656804 * 2
def baseEnd_1656804 : Nat := 850736802291840980430503

theorem tailTrace_1656804 : CollatzResearch.WordTrace tailWord_1656804 prefixEnd_1656804 850736802291840980430503 := by
  unfold tailWord_1656804
  simp only [CollatzResearch.WordTrace]
  refine ⟨30214303144844771220372733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40285737526459694960496977 30214303144844771220372733)
  ·
    refine ⟨11330363679316789207639775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30214303144844771220372733 11330363679316789207639775)
    ·
      refine ⟨16995545518975183811459663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11330363679316789207639775 16995545518975183811459663)
      ·
        refine ⟨25493318278462775717189495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16995545518975183811459663 25493318278462775717189495)
        ·
          refine ⟨38239977417694163575784243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25493318278462775717189495 38239977417694163575784243)
          ·
            refine ⟨57359966126541245363676365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38239977417694163575784243 57359966126541245363676365)
            ·
              refine ⟨21509987297452967011378637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57359966126541245363676365 21509987297452967011378637)
              ·
                refine ⟨8066245236544862629266989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21509987297452967011378637 8066245236544862629266989)
                ·
                  refine ⟨3024841963704323485975121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8066245236544862629266989 3024841963704323485975121)
                  ·
                    refine ⟨2268631472778242614481341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3024841963704323485975121 2268631472778242614481341)
                    ·
                      refine ⟨850736802291840980430503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2268631472778242614481341 850736802291840980430503)
                      ·
                        rfl

theorem cell23_1656804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_1656804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656804 prefixEnd_1656804 := by exact prefixLift 1656804
  have htrace : WordTrace (prefixWord ++ tailWord_1656804) baseStart_1656804 baseEnd_1656804 := by
    simpa [prefixWord, tailWord_1656804, baseEnd_1656804] using wordTrace_append hprefix tailTrace_1656804
  have hstable : (prefixWord ++ tailWord_1656804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656804).length < 2 ^ (prefixWord ++ tailWord_1656804).sum := by decide
  have hdescent : baseEnd_1656804 < baseStart_1656804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656851 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 2, 1, 3]
def baseStart_1656851 : Nat := 118140960795 + 1656851 * 2 ^ 59
def prefixEnd_1656851 : Nat := 4983230072969 + 3 ^ 40 * 1656851 * 2
def baseEnd_1656851 : Nat := 850760935882602296542787

theorem tailTrace_1656851 : CollatzResearch.WordTrace tailWord_1656851 prefixEnd_1656851 850760935882602296542787 := by
  unfold tailWord_1656851
  simp only [CollatzResearch.WordTrace]
  refine ⟨60430320520519269467706407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40286880347012846311804271 60430320520519269467706407)
  ·
    refine ⟨90645480780778904201559611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60430320520519269467706407 90645480780778904201559611)
    ·
      refine ⟨135968221171168356302339417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90645480780778904201559611 135968221171168356302339417)
      ·
        refine ⟨101976165878376267226754563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135968221171168356302339417 101976165878376267226754563)
        ·
          refine ⟨152964248817564400840131845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101976165878376267226754563 152964248817564400840131845)
          ·
            refine ⟨28680796653293325157524721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152964248817564400840131845 28680796653293325157524721)
            ·
              refine ⟨21510597489969993868143541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28680796653293325157524721 21510597489969993868143541)
              ·
                refine ⟨2016618514684686925138457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21510597489969993868143541 2016618514684686925138457)
                ·
                  refine ⟨1512463886013515193853843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2016618514684686925138457 1512463886013515193853843)
                  ·
                    refine ⟨2268695829020272790780765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1512463886013515193853843 2268695829020272790780765)
                    ·
                      refine ⟨850760935882602296542787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2268695829020272790780765 850760935882602296542787)
                      ·
                        rfl

theorem cell23_1656851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 1, 3].length) (baseStart_1656851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656851 prefixEnd_1656851 := by exact prefixLift 1656851
  have htrace : WordTrace (prefixWord ++ tailWord_1656851) baseStart_1656851 baseEnd_1656851 := by
    simpa [prefixWord, tailWord_1656851, baseEnd_1656851] using wordTrace_append hprefix tailTrace_1656851
  have hstable : (prefixWord ++ tailWord_1656851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656851).length < 2 ^ (prefixWord ++ tailWord_1656851).sum := by decide
  have hdescent : baseEnd_1656851 < baseStart_1656851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656907 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 9]
def baseStart_1656907 : Nat := 118140960795 + 1656907 * 2 ^ 59
def prefixEnd_1656907 : Nat := 4983230072969 + 3 ^ 40 * 1656907 * 2
def baseEnd_1656907 : Nat := 850789690799254077442529

theorem tailTrace_1656907 : CollatzResearch.WordTrace tailWord_1656907 prefixEnd_1656907 850789690799254077442529 := by
  unfold tailWord_1656907
  simp only [CollatzResearch.WordTrace]
  refine ⟨60432363008316391031744975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40288242005544260687829983 60432363008316391031744975)
  ·
    refine ⟨90648544512474586547617463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60432363008316391031744975 90648544512474586547617463)
    ·
      refine ⟨135972816768711879821426195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90648544512474586547617463 135972816768711879821426195)
      ·
        refine ⟨203959225153067819732139293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135972816768711879821426195 203959225153067819732139293)
        ·
          refine ⟨76484709432400432399552235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203959225153067819732139293 76484709432400432399552235)
          ·
            refine ⟨114727064148600648599328353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76484709432400432399552235 114727064148600648599328353)
            ·
              refine ⟨86045298111450486449496265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114727064148600648599328353 86045298111450486449496265)
              ·
                refine ⟨64533973583587864837122199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86045298111450486449496265 64533973583587864837122199)
                ·
                  refine ⟨96800960375381797255683299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64533973583587864837122199 96800960375381797255683299)
                  ·
                    refine ⟨145201440563072695883524949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96800960375381797255683299 145201440563072695883524949)
                    ·
                      refine ⟨850789690799254077442529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 145201440563072695883524949 850789690799254077442529)
                      ·
                        rfl

theorem cell23_1656907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_1656907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656907 prefixEnd_1656907 := by exact prefixLift 1656907
  have htrace : WordTrace (prefixWord ++ tailWord_1656907) baseStart_1656907 baseEnd_1656907 := by
    simpa [prefixWord, tailWord_1656907, baseEnd_1656907] using wordTrace_append hprefix tailTrace_1656907
  have hstable : (prefixWord ++ tailWord_1656907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656907).length < 2 ^ (prefixWord ++ tailWord_1656907).sum := by decide
  have hdescent : baseEnd_1656907 < baseStart_1656907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656925 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_1656925 : Nat := 118140960795 + 1656925 * 2 ^ 59
def prefixEnd_1656925 : Nat := 4983230072969 + 3 ^ 40 * 1656925 * 2
def baseEnd_1656925 : Nat := 850798933451035007017447

theorem tailTrace_1656925 : CollatzResearch.WordTrace tailWord_1656925 prefixEnd_1656925 850798933451035007017447 := by
  unfold tailWord_1656925
  simp only [CollatzResearch.WordTrace]
  refine ⟨60433019522251180105900229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40288679681500786737266819 60433019522251180105900229)
  ·
    refine ⟨11331191160422096269856293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60433019522251180105900229 11331191160422096269856293)
    ·
      refine ⟨2124598342579143050598055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11331191160422096269856293 2124598342579143050598055)
      ·
        refine ⟨3186897513868714575897083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2124598342579143050598055 3186897513868714575897083)
        ·
          refine ⟨4780346270803071863845625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3186897513868714575897083 4780346270803071863845625)
          ·
            refine ⟨3585259703102303897884219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4780346270803071863845625 3585259703102303897884219)
            ·
              refine ⟨5377889554653455846826329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585259703102303897884219 5377889554653455846826329)
              ·
                refine ⟨4033417165990091885119747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5377889554653455846826329 4033417165990091885119747)
                ·
                  refine ⟨6050125748985137827679621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033417165990091885119747 6050125748985137827679621)
                  ·
                    refine ⟨1134398577934713342689929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6050125748985137827679621 1134398577934713342689929)
                    ·
                      refine ⟨850798933451035007017447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134398577934713342689929 850798933451035007017447)
                      ·
                        rfl

theorem cell23_1656925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_1656925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656925 prefixEnd_1656925 := by exact prefixLift 1656925
  have htrace : WordTrace (prefixWord ++ tailWord_1656925) baseStart_1656925 baseEnd_1656925 := by
    simpa [prefixWord, tailWord_1656925, baseEnd_1656925] using wordTrace_append hprefix tailTrace_1656925
  have hstable : (prefixWord ++ tailWord_1656925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656925).length < 2 ^ (prefixWord ++ tailWord_1656925).sum := by decide
  have hdescent : baseEnd_1656925 < baseStart_1656925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656941 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_1656941 : Nat := 118140960795 + 1656941 * 2 ^ 59
def prefixEnd_1656941 : Nat := 4983230072969 + 3 ^ 40 * 1656941 * 2
def baseEnd_1656941 : Nat := 850807149141506944417373

theorem tailTrace_1656941 : CollatzResearch.WordTrace tailWord_1656941 prefixEnd_1656941 850807149141506944417373 := by
  unfold tailWord_1656941
  simp only [CollatzResearch.WordTrace]
  refine ⟨60433603090193214838482677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40289068726795476558988451 60433603090193214838482677)
  ·
    refine ⟨5665650289705613891107751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60433603090193214838482677 5665650289705613891107751)
    ·
      refine ⟨8498475434558420836661627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5665650289705613891107751 8498475434558420836661627)
      ·
        refine ⟨12747713151837631254992441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8498475434558420836661627 12747713151837631254992441)
        ·
          refine ⟨9560784863878223441244331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12747713151837631254992441 9560784863878223441244331)
          ·
            refine ⟨14341177295817335161866497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9560784863878223441244331 14341177295817335161866497)
            ·
              refine ⟨10755882971863001371399873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14341177295817335161866497 10755882971863001371399873)
              ·
                refine ⟨8066912228897251028549905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10755882971863001371399873 8066912228897251028549905)
                ·
                  refine ⟨6050184171672938271412429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8066912228897251028549905 6050184171672938271412429)
                  ·
                    refine ⟨2268819064377351851779661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6050184171672938271412429 2268819064377351851779661)
                    ·
                      refine ⟨850807149141506944417373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2268819064377351851779661 850807149141506944417373)
                      ·
                        rfl

theorem cell23_1656941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_1656941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656941 prefixEnd_1656941 := by exact prefixLift 1656941
  have htrace : WordTrace (prefixWord ++ tailWord_1656941) baseStart_1656941 baseEnd_1656941 := by
    simpa [prefixWord, tailWord_1656941, baseEnd_1656941] using wordTrace_append hprefix tailTrace_1656941
  have hstable : (prefixWord ++ tailWord_1656941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656941).length < 2 ^ (prefixWord ++ tailWord_1656941).sum := by decide
  have hdescent : baseEnd_1656941 < baseStart_1656941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656951 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 2, 5, 2]
def baseStart_1656951 : Nat := 118140960795 + 1656951 * 2 ^ 59
def prefixEnd_1656951 : Nat := 4983230072969 + 3 ^ 40 * 1656951 * 2
def baseEnd_1656951 : Nat := 850812283948051905292327

theorem tailTrace_1656951 : CollatzResearch.WordTrace tailWord_1656951 prefixEnd_1656951 850812283948051905292327 := by
  unfold tailWord_1656951
  simp only [CollatzResearch.WordTrace]
  refine ⟨60433967820156986546346707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40289311880104657697564471 60433967820156986546346707)
  ·
    refine ⟨90650951730235479819520061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60433967820156986546346707 90650951730235479819520061)
    ·
      refine ⟨33994106898838304932320023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90650951730235479819520061 33994106898838304932320023)
      ·
        refine ⟨50991160348257457398480035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33994106898838304932320023 50991160348257457398480035)
        ·
          refine ⟨76486740522386186097720053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50991160348257457398480035 76486740522386186097720053)
          ·
            refine ⟨7170631923973704946661255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76486740522386186097720053 7170631923973704946661255)
            ·
              refine ⟨10755947885960557419991883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7170631923973704946661255 10755947885960557419991883)
              ·
                refine ⟨16133921828940836129987825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10755947885960557419991883 16133921828940836129987825)
                ·
                  refine ⟨12100441371705627097490869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16133921828940836129987825 12100441371705627097490869)
                  ·
                    refine ⟨1134416378597402540389769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12100441371705627097490869 1134416378597402540389769)
                    ·
                      refine ⟨850812283948051905292327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134416378597402540389769 850812283948051905292327)
                      ·
                        rfl

theorem cell23_1656951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 5, 2].length) (baseStart_1656951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656951 prefixEnd_1656951 := by exact prefixLift 1656951
  have htrace : WordTrace (prefixWord ++ tailWord_1656951) baseStart_1656951 baseEnd_1656951 := by
    simpa [prefixWord, tailWord_1656951, baseEnd_1656951] using wordTrace_append hprefix tailTrace_1656951
  have hstable : (prefixWord ++ tailWord_1656951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656951).length < 2 ^ (prefixWord ++ tailWord_1656951).sum := by decide
  have hdescent : baseEnd_1656951 < baseStart_1656951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656981 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 1, 6, 2]
def baseStart_1656981 : Nat := 118140960795 + 1656981 * 2 ^ 59
def prefixEnd_1656981 : Nat := 4983230072969 + 3 ^ 40 * 1656981 * 2
def baseEnd_1656981 : Nat := 850827688367686787917189

theorem tailTrace_1656981 : CollatzResearch.WordTrace tailWord_1656981 prefixEnd_1656981 850827688367686787917189 := by
  unfold tailWord_1656981
  simp only [CollatzResearch.WordTrace]
  refine ⟨60435062010048301669938797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40290041340032201113292531 60435062010048301669938797)
  ·
    refine ⟨22663148253768113126227049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60435062010048301669938797 22663148253768113126227049)
    ·
      refine ⟨16997361190326084844670287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22663148253768113126227049 16997361190326084844670287)
      ·
        refine ⟨25496041785489127267005431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16997361190326084844670287 25496041785489127267005431)
        ·
          refine ⟨38244062678233690900508147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25496041785489127267005431 38244062678233690900508147)
          ·
            refine ⟨57366094017350536350762221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38244062678233690900508147 57366094017350536350762221)
            ·
              refine ⟨21512285256506451131535833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57366094017350536350762221 21512285256506451131535833)
              ·
                refine ⟨16134213942379838348651875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21512285256506451131535833 16134213942379838348651875)
                ·
                  refine ⟨24201320913569757522977813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16134213942379838348651875 24201320913569757522977813)
                  ·
                    refine ⟨1134436917823582383889585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24201320913569757522977813 1134436917823582383889585)
                    ·
                      refine ⟨850827688367686787917189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134436917823582383889585 850827688367686787917189)
                      ·
                        rfl

theorem cell23_1656981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_1656981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1656981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1656981 prefixEnd_1656981 := by exact prefixLift 1656981
  have htrace : WordTrace (prefixWord ++ tailWord_1656981) baseStart_1656981 baseEnd_1656981 := by
    simpa [prefixWord, tailWord_1656981, baseEnd_1656981] using wordTrace_append hprefix tailTrace_1656981
  have hstable : (prefixWord ++ tailWord_1656981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656981).length < 2 ^ (prefixWord ++ tailWord_1656981).sum := by decide
  have hdescent : baseEnd_1656981 < baseStart_1656981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657042 : List Nat := [3, 2, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_1657042 : Nat := 118140960795 + 1657042 * 2 ^ 59
def prefixEnd_1657042 : Nat := 4983230072969 + 3 ^ 40 * 1657042 * 2
def baseEnd_1657042 : Nat := 283619670229203683084803

theorem tailTrace_1657042 : CollatzResearch.WordTrace tailWord_1657042 prefixEnd_1657042 283619670229203683084803 := by
  unfold tailWord_1657042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109321715706827271977345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40291524575218206058606253 15109321715706827271977345)
  ·
    refine ⟨11331991286780120453983009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15109321715706827271977345 11331991286780120453983009)
    ·
      refine ⟨8498993465085090340487257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11331991286780120453983009 8498993465085090340487257)
      ·
        refine ⟨6374245098813817755365443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8498993465085090340487257 6374245098813817755365443)
        ·
          refine ⟨9561367648220726633048165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6374245098813817755365443 9561367648220726633048165)
          ·
            refine ⟨1792756434041386243696531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9561367648220726633048165 1792756434041386243696531)
            ·
              refine ⟨2689134651062079365544797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792756434041386243696531 2689134651062079365544797)
              ·
                refine ⟨1008425494148279762079299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2689134651062079365544797 1008425494148279762079299)
                ·
                  refine ⟨1512638241222419643118949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008425494148279762079299 1512638241222419643118949)
                  ·
                    refine ⟨283619670229203683084803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1512638241222419643118949 283619670229203683084803)
                    ·
                      rfl

theorem cell23_1657042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_1657042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657042 prefixEnd_1657042 := by exact prefixLift 1657042
  have htrace : WordTrace (prefixWord ++ tailWord_1657042) baseStart_1657042 baseEnd_1657042 := by
    simpa [prefixWord, tailWord_1657042, baseEnd_1657042] using wordTrace_append hprefix tailTrace_1657042
  have hstable : (prefixWord ++ tailWord_1657042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657042).length < 2 ^ (prefixWord ++ tailWord_1657042).sum := by decide
  have hdescent : baseEnd_1657042 < baseStart_1657042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657052 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1657052 : Nat := 118140960795 + 1657052 * 2 ^ 59
def prefixEnd_1657052 : Nat := 4983230072969 + 3 ^ 40 * 1657052 * 2
def baseEnd_1657052 : Nat := 850864145494156010129363

theorem tailTrace_1657052 : CollatzResearch.WordTrace tailWord_1657052 prefixEnd_1657052 850864145494156010129363 := by
  unfold tailWord_1657052
  simp only [CollatzResearch.WordTrace]
  refine ⟨30218825796395540397886705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40291767728527387197182273 30218825796395540397886705)
  ·
    refine ⟨22664119347296655298415029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30218825796395540397886705 22664119347296655298415029)
    ·
      refine ⟨2124761188809061434226409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22664119347296655298415029 2124761188809061434226409)
      ·
        refine ⟨1593570891606796075669807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2124761188809061434226409 1593570891606796075669807)
        ·
          refine ⟨2390356337410194113504711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593570891606796075669807 2390356337410194113504711)
          ·
            refine ⟨3585534506115291170257067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390356337410194113504711 3585534506115291170257067)
            ·
              refine ⟨5378301759172936755385601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585534506115291170257067 5378301759172936755385601)
              ·
                refine ⟨4033726319379702566539201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5378301759172936755385601 4033726319379702566539201)
                ·
                  refine ⟨3025294739534776924904401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4033726319379702566539201 3025294739534776924904401)
                  ·
                    refine ⟨2268971054651082693678301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3025294739534776924904401 2268971054651082693678301)
                    ·
                      refine ⟨850864145494156010129363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2268971054651082693678301 850864145494156010129363)
                      ·
                        rfl

theorem cell23_1657052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1657052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657052 prefixEnd_1657052 := by exact prefixLift 1657052
  have htrace : WordTrace (prefixWord ++ tailWord_1657052) baseStart_1657052 baseEnd_1657052 := by
    simpa [prefixWord, tailWord_1657052, baseEnd_1657052] using wordTrace_append hprefix tailTrace_1657052
  have hstable : (prefixWord ++ tailWord_1657052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657052).length < 2 ^ (prefixWord ++ tailWord_1657052).sum := by decide
  have hdescent : baseEnd_1657052 < baseStart_1657052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657059 : List Nat := [1, 1, 1, 8, 1, 1, 3, 2, 1, 4]
def baseStart_1657059 : Nat := 118140960795 + 1657059 * 2 ^ 59
def prefixEnd_1657059 : Nat := 4983230072969 + 3 ^ 40 * 1657059 * 2
def baseEnd_1657059 : Nat := 283622579952912494247277

theorem tailTrace_1657059 : CollatzResearch.WordTrace tailWord_1657059 prefixEnd_1657059 283622579952912494247277 := by
  unfold tailWord_1657059
  simp only [CollatzResearch.WordTrace]
  refine ⟨60437906903765720991278231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40291937935843813994185487 60437906903765720991278231)
  ·
    refine ⟨90656860355648581486917347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60437906903765720991278231 90656860355648581486917347)
    ·
      refine ⟨135985290533472872230376021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90656860355648581486917347 135985290533472872230376021)
      ·
        refine ⟨1593577623439135221449719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 135985290533472872230376021 1593577623439135221449719)
        ·
          refine ⟨2390366435158702832174579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593577623439135221449719 2390366435158702832174579)
          ·
            refine ⟨3585549652738054248261869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390366435158702832174579 3585549652738054248261869)
            ·
              refine ⟨1344581119776770343098201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3585549652738054248261869 1344581119776770343098201)
              ·
                refine ⟨1008435839832577757323651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1344581119776770343098201 1008435839832577757323651)
                ·
                  refine ⟨1512653759748866635985477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008435839832577757323651 1512653759748866635985477)
                  ·
                    refine ⟨283622579952912494247277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1512653759748866635985477 283622579952912494247277)
                    ·
                      rfl

theorem cell23_1657059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 1, 4].length) (baseStart_1657059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657059 prefixEnd_1657059 := by exact prefixLift 1657059
  have htrace : WordTrace (prefixWord ++ tailWord_1657059) baseStart_1657059 baseEnd_1657059 := by
    simpa [prefixWord, tailWord_1657059, baseEnd_1657059] using wordTrace_append hprefix tailTrace_1657059
  have hstable : (prefixWord ++ tailWord_1657059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657059).length < 2 ^ (prefixWord ++ tailWord_1657059).sum := by decide
  have hdescent : baseEnd_1657059 < baseStart_1657059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657081 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 6, 4]
def baseStart_1657081 : Nat := 118140960795 + 1657081 * 2 ^ 59
def prefixEnd_1657081 : Nat := 4983230072969 + 3 ^ 40 * 1657081 * 2
def baseEnd_1657081 : Nat := 283626345477712132222243

theorem tailTrace_1657081 : CollatzResearch.WordTrace tailWord_1657081 prefixEnd_1657081 283626345477712132222243 := by
  unfold tailWord_1657081
  simp only [CollatzResearch.WordTrace]
  refine ⟨60438709309686018748579097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40292472873124012499052731 60438709309686018748579097)
  ·
    refine ⟨45329031982264514061434323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60438709309686018748579097 45329031982264514061434323)
    ·
      refine ⟨67993547973396771092151485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45329031982264514061434323 67993547973396771092151485)
      ·
        refine ⟨25497580490023789159556807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67993547973396771092151485 25497580490023789159556807)
        ·
          refine ⟨38246370735035683739335211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25497580490023789159556807 38246370735035683739335211)
          ·
            refine ⟨57369556102553525609002817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38246370735035683739335211 57369556102553525609002817)
            ·
              refine ⟨43027167076915144206752113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57369556102553525609002817 43027167076915144206752113)
              ·
                refine ⟨32270375307686358155064085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43027167076915144206752113 32270375307686358155064085)
                ·
                  refine ⟨1512673842547798038518629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32270375307686358155064085 1512673842547798038518629)
                  ·
                    refine ⟨283626345477712132222243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1512673842547798038518629 283626345477712132222243)
                    ·
                      rfl

theorem cell23_1657081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 4].length) (baseStart_1657081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657081 prefixEnd_1657081 := by exact prefixLift 1657081
  have htrace : WordTrace (prefixWord ++ tailWord_1657081) baseStart_1657081 baseEnd_1657081 := by
    simpa [prefixWord, tailWord_1657081, baseEnd_1657081] using wordTrace_append hprefix tailTrace_1657081
  have hstable : (prefixWord ++ tailWord_1657081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657081).length < 2 ^ (prefixWord ++ tailWord_1657081).sum := by decide
  have hdescent : baseEnd_1657081 < baseStart_1657081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657088 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 4]
def baseStart_1657088 : Nat := 118140960795 + 1657088 * 2 ^ 59
def prefixEnd_1657088 : Nat := 4983230072969 + 3 ^ 40 * 1657088 * 2
def baseEnd_1657088 : Nat := 850882630797717869279197

theorem tailTrace_1657088 : CollatzResearch.WordTrace tailWord_1657088 prefixEnd_1657088 850882630797717869279197 := by
  unfold tailWord_1657088
  simp only [CollatzResearch.WordTrace]
  refine ⟨30219482310330329472041959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40292643080440439296055945 30219482310330329472041959)
  ·
    refine ⟨45329223465495494208062939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30219482310330329472041959 45329223465495494208062939)
    ·
      refine ⟨67993835198243241312094409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45329223465495494208062939 67993835198243241312094409)
      ·
        refine ⟨50995376398682430984070807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67993835198243241312094409 50995376398682430984070807)
        ·
          refine ⟨76493064598023646476106211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50995376398682430984070807 76493064598023646476106211)
          ·
            refine ⟨114739596897035469714159317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76493064598023646476106211 114739596897035469714159317)
            ·
              refine ⟨2689209302274268821425609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 114739596897035469714159317 2689209302274268821425609)
              ·
                refine ⟨2016906976705701616069207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689209302274268821425609 2016906976705701616069207)
                ·
                  refine ⟨3025360465058552424103811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016906976705701616069207 3025360465058552424103811)
                  ·
                    refine ⟨4538040697587828636155717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3025360465058552424103811 4538040697587828636155717)
                    ·
                      refine ⟨850882630797717869279197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4538040697587828636155717 850882630797717869279197)
                      ·
                        rfl

theorem cell23_1657088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_1657088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657088 prefixEnd_1657088 := by exact prefixLift 1657088
  have htrace : WordTrace (prefixWord ++ tailWord_1657088) baseStart_1657088 baseEnd_1657088 := by
    simpa [prefixWord, tailWord_1657088, baseEnd_1657088] using wordTrace_append hprefix tailTrace_1657088
  have hstable : (prefixWord ++ tailWord_1657088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657088).length < 2 ^ (prefixWord ++ tailWord_1657088).sum := by decide
  have hdescent : baseEnd_1657088 < baseStart_1657088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657092 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_1657092 : Nat := 118140960795 + 1657092 * 2 ^ 59
def prefixEnd_1657092 : Nat := 4983230072969 + 3 ^ 40 * 1657092 * 2
def baseEnd_1657092 : Nat := 850884684720335853629179

theorem tailTrace_1657092 : CollatzResearch.WordTrace tailWord_1657092 prefixEnd_1657092 850884684720335853629179 := by
  unfold tailWord_1657092
  simp only [CollatzResearch.WordTrace]
  refine ⟨30219555256323083813614765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40292740341764111751486353 30219555256323083813614765)
  ·
    refine ⟨11332333221121156430105537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30219555256323083813614765 11332333221121156430105537)
    ·
      refine ⟨8499249915840867322579153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11332333221121156430105537 8499249915840867322579153)
      ·
        refine ⟨6374437436880650491934365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8499249915840867322579153 6374437436880650491934365)
        ·
          refine ⟨2390414038830243934475387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6374437436880650491934365 2390414038830243934475387)
          ·
            refine ⟨3585621058245365901713081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390414038830243934475387 3585621058245365901713081)
            ·
              refine ⟨2689215793684024426284811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3585621058245365901713081 2689215793684024426284811)
              ·
                refine ⟨4033823690526036639427217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689215793684024426284811 4033823690526036639427217)
                ·
                  refine ⟨3025367767894527479570413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4033823690526036639427217 3025367767894527479570413)
                  ·
                    refine ⟨1134512912960447804838905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3025367767894527479570413 1134512912960447804838905)
                    ·
                      refine ⟨850884684720335853629179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134512912960447804838905 850884684720335853629179)
                      ·
                        rfl

theorem cell23_1657092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_1657092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657092 prefixEnd_1657092 := by exact prefixLift 1657092
  have htrace : WordTrace (prefixWord ++ tailWord_1657092) baseStart_1657092 baseEnd_1657092 := by
    simpa [prefixWord, tailWord_1657092, baseEnd_1657092] using wordTrace_append hprefix tailTrace_1657092
  have hstable : (prefixWord ++ tailWord_1657092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657092).length < 2 ^ (prefixWord ++ tailWord_1657092).sum := by decide
  have hdescent : baseEnd_1657092 < baseStart_1657092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657105 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 1, 1, 4]
def baseStart_1657105 : Nat := 118140960795 + 1657105 * 2 ^ 59
def prefixEnd_1657105 : Nat := 4983230072969 + 3 ^ 40 * 1657105 * 2
def baseEnd_1657105 : Nat := 850891359968844302766619

theorem tailTrace_1657105 : CollatzResearch.WordTrace tailWord_1657105 prefixEnd_1657105 850891359968844302766619 := by
  unfold tailWord_1657105
  simp only [CollatzResearch.WordTrace]
  refine ⟨60439584661599070847452769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40293056441066047231635179 60439584661599070847452769)
  ·
    refine ⟨45329688496199303135589577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60439584661599070847452769 45329688496199303135589577)
    ·
      refine ⟨33997266372149477351692183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45329688496199303135589577 33997266372149477351692183)
      ·
        refine ⟨50995899558224216027538275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33997266372149477351692183 50995899558224216027538275)
        ·
          refine ⟨76493849337336324041307413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50995899558224216027538275 76493849337336324041307413)
          ·
            refine ⟨3585649187687640189436285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76493849337336324041307413 3585649187687640189436285)
            ·
              refine ⟨1344618445382865071038607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3585649187687640189436285 1344618445382865071038607)
              ·
                refine ⟨2016927668074297606557911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344618445382865071038607 2016927668074297606557911)
                ·
                  refine ⟨3025391502111446409836867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016927668074297606557911 3025391502111446409836867)
                  ·
                    refine ⟨4538087253167169614755301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3025391502111446409836867 4538087253167169614755301)
                    ·
                      refine ⟨850891359968844302766619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4538087253167169614755301 850891359968844302766619)
                      ·
                        rfl

theorem cell23_1657105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 1, 4].length) (baseStart_1657105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657105 prefixEnd_1657105 := by exact prefixLift 1657105
  have htrace : WordTrace (prefixWord ++ tailWord_1657105) baseStart_1657105 baseEnd_1657105 := by
    simpa [prefixWord, tailWord_1657105, baseEnd_1657105] using wordTrace_append hprefix tailTrace_1657105
  have hstable : (prefixWord ++ tailWord_1657105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657105).length < 2 ^ (prefixWord ++ tailWord_1657105).sum := by decide
  have hdescent : baseEnd_1657105 < baseStart_1657105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657141 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1657141 : Nat := 118140960795 + 1657141 * 2 ^ 59
def prefixEnd_1657141 : Nat := 4983230072969 + 3 ^ 40 * 1657141 * 2
def baseEnd_1657141 : Nat := 283636615090802053972151

theorem tailTrace_1657141 : CollatzResearch.WordTrace tailWord_1657141 prefixEnd_1657141 283636615090802053972151 := by
  unfold tailWord_1657141
  simp only [CollatzResearch.WordTrace]
  refine ⟨60440897689468648995763277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40293931792979099330508851 60440897689468648995763277)
  ·
    refine ⟨22665336633550743373411229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60440897689468648995763277 22665336633550743373411229)
    ·
      refine ⟨8499501237581528765029211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22665336633550743373411229 8499501237581528765029211)
      ·
        refine ⟨12749251856372293147543817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8499501237581528765029211 12749251856372293147543817)
        ·
          refine ⟨9561938892279219860657863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12749251856372293147543817 9561938892279219860657863)
          ·
            refine ⟨14342908338418829790986795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9561938892279219860657863 14342908338418829790986795)
            ·
              refine ⟨21514362507628244686480193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14342908338418829790986795 21514362507628244686480193)
              ·
                refine ⟨16135771880721183514860145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21514362507628244686480193 16135771880721183514860145)
                ·
                  refine ⟨12101828910540887636145109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16135771880721183514860145 12101828910540887636145109)
                  ·
                    refine ⟨283636615090802053972151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12101828910540887636145109 283636615090802053972151)
                    ·
                      rfl

theorem cell23_1657141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1657141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657141 prefixEnd_1657141 := by exact prefixLift 1657141
  have htrace : WordTrace (prefixWord ++ tailWord_1657141) baseStart_1657141 baseEnd_1657141 := by
    simpa [prefixWord, tailWord_1657141, baseEnd_1657141] using wordTrace_append hprefix tailTrace_1657141
  have hstable : (prefixWord ++ tailWord_1657141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657141).length < 2 ^ (prefixWord ++ tailWord_1657141).sum := by decide
  have hdescent : baseEnd_1657141 < baseStart_1657141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657151 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_1657151 : Nat := 118140960795 + 1657151 * 2 ^ 59
def prefixEnd_1657151 : Nat := 4983230072969 + 3 ^ 40 * 1657151 * 2
def baseEnd_1657151 : Nat := 850914980078951122791407

theorem tailTrace_1657151 : CollatzResearch.WordTrace tailWord_1657151 prefixEnd_1657151 850914980078951122791407 := by
  unfold tailWord_1657151
  simp only [CollatzResearch.WordTrace]
  refine ⟨60441262419432420703627307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40294174946288280469084871 60441262419432420703627307)
  ·
    refine ⟨90661893629148631055440961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60441262419432420703627307 90661893629148631055440961)
    ·
      refine ⟨67996420221861473291580721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90661893629148631055440961 67996420221861473291580721)
      ·
        refine ⟨50997315166396104968685541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67996420221861473291580721 50997315166396104968685541)
        ·
          refine ⟨9561996593699269681628539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50997315166396104968685541 9561996593699269681628539)
          ·
            refine ⟨14342994890548904522442809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9561996593699269681628539 14342994890548904522442809)
            ·
              refine ⟨10757246167911678391832107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14342994890548904522442809 10757246167911678391832107)
              ·
                refine ⟨16135869251867517587748161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10757246167911678391832107 16135869251867517587748161)
                ·
                  refine ⟨12101901938900638190811121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16135869251867517587748161 12101901938900638190811121)
                  ·
                    refine ⟨9076426454175478643108341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12101901938900638190811121 9076426454175478643108341)
                    ·
                      refine ⟨850914980078951122791407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9076426454175478643108341 850914980078951122791407)
                      ·
                        rfl

theorem cell23_1657151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_1657151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657151 prefixEnd_1657151 := by exact prefixLift 1657151
  have htrace : WordTrace (prefixWord ++ tailWord_1657151) baseStart_1657151 baseEnd_1657151 := by
    simpa [prefixWord, tailWord_1657151, baseEnd_1657151] using wordTrace_append hprefix tailTrace_1657151
  have hstable : (prefixWord ++ tailWord_1657151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657151).length < 2 ^ (prefixWord ++ tailWord_1657151).sum := by decide
  have hdescent : baseEnd_1657151 < baseStart_1657151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657156 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_1657156 : Nat := 118140960795 + 1657156 * 2 ^ 59
def prefixEnd_1657156 : Nat := 4983230072969 + 3 ^ 40 * 1657156 * 2
def baseEnd_1657156 : Nat := 850917547482223603228885

theorem tailTrace_1657156 : CollatzResearch.WordTrace tailWord_1657156 prefixEnd_1657156 850917547482223603228885 := by
  unfold tailWord_1657156
  simp only [CollatzResearch.WordTrace]
  refine ⟨30220722392207153278779661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40294296522942871038372881 30220722392207153278779661)
  ·
    refine ⟨11332770897077682479542373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30220722392207153278779661 11332770897077682479542373)
    ·
      refine ⟨2124894543202065464914195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11332770897077682479542373 2124894543202065464914195)
      ·
        refine ⟨3187341814803098197371293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2124894543202065464914195 3187341814803098197371293)
        ·
          refine ⟨1195253180551161824014235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3187341814803098197371293 1195253180551161824014235)
          ·
            refine ⟨1792879770826742736021353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195253180551161824014235 1792879770826742736021353)
            ·
              refine ⟨1344659828120057052016015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1792879770826742736021353 1344659828120057052016015)
              ·
                refine ⟨2016989742180085578024023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344659828120057052016015 2016989742180085578024023)
                ·
                  refine ⟨3025484613270128367036035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016989742180085578024023 3025484613270128367036035)
                  ·
                    refine ⟨4538226919905192550554053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3025484613270128367036035 4538226919905192550554053)
                    ·
                      refine ⟨850917547482223603228885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4538226919905192550554053 850917547482223603228885)
                      ·
                        rfl

theorem cell23_1657156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_1657156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657156 prefixEnd_1657156 := by exact prefixLift 1657156
  have htrace : WordTrace (prefixWord ++ tailWord_1657156) baseStart_1657156 baseEnd_1657156 := by
    simpa [prefixWord, tailWord_1657156, baseEnd_1657156] using wordTrace_append hprefix tailTrace_1657156
  have hstable : (prefixWord ++ tailWord_1657156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657156).length < 2 ^ (prefixWord ++ tailWord_1657156).sum := by decide
  have hdescent : baseEnd_1657156 < baseStart_1657156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657172 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_1657172 : Nat := 118140960795 + 1657172 * 2 ^ 59
def prefixEnd_1657172 : Nat := 4983230072969 + 3 ^ 40 * 1657172 * 2
def baseEnd_1657172 : Nat := 850925763172695540628811

theorem tailTrace_1657172 : CollatzResearch.WordTrace tailWord_1657172 prefixEnd_1657172 850925763172695540628811 := by
  unfold tailWord_1657172
  simp only [CollatzResearch.WordTrace]
  refine ⟨30221014176178170645070885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40294685568237560860094513 30221014176178170645070885)
  ·
    refine ⟨5666440158033406995950791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30221014176178170645070885 5666440158033406995950791)
    ·
      refine ⟨8499660237050110493926187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5666440158033406995950791 8499660237050110493926187)
      ·
        refine ⟨12749490355575165740889281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8499660237050110493926187 12749490355575165740889281)
        ·
          refine ⟨9562117766681374305666961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12749490355575165740889281 9562117766681374305666961)
          ·
            refine ⟨7171588325011030729250221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9562117766681374305666961 7171588325011030729250221)
            ·
              refine ⟨2689345621879136523468833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7171588325011030729250221 2689345621879136523468833)
              ·
                refine ⟨2017009216409352392601625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689345621879136523468833 2017009216409352392601625)
                ·
                  refine ⟨1512756912307014294451219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2017009216409352392601625 1512756912307014294451219)
                  ·
                    refine ⟨2269135368460521441676829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1512756912307014294451219 2269135368460521441676829)
                    ·
                      refine ⟨850925763172695540628811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2269135368460521441676829 850925763172695540628811)
                      ·
                        rfl

theorem cell23_1657172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_1657172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657172 prefixEnd_1657172 := by exact prefixLift 1657172
  have htrace : WordTrace (prefixWord ++ tailWord_1657172) baseStart_1657172 baseEnd_1657172 := by
    simpa [prefixWord, tailWord_1657172, baseEnd_1657172] using wordTrace_append hprefix tailTrace_1657172
  have hstable : (prefixWord ++ tailWord_1657172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657172).length < 2 ^ (prefixWord ++ tailWord_1657172).sum := by decide
  have hdescent : baseEnd_1657172 < baseStart_1657172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657246 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_1657246 : Nat := 118140960795 + 1657246 * 2 ^ 59
def prefixEnd_1657246 : Nat := 4983230072969 + 3 ^ 40 * 1657246 * 2
def baseEnd_1657246 : Nat := 850963760741128251103471

theorem tailTrace_1657246 : CollatzResearch.WordTrace tailWord_1657246 prefixEnd_1657246 850963760741128251103471 := by
  unfold tailWord_1657246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555590919261031491041949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40296484902725501285557061 7555590919261031491041949)
  ·
    refine ⟨2833346594722886809140731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7555590919261031491041949 2833346594722886809140731)
    ·
      refine ⟨4250019892084330213711097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2833346594722886809140731 4250019892084330213711097)
      ·
        refine ⟨3187514919063247660283323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4250019892084330213711097 3187514919063247660283323)
        ·
          refine ⟨4781272378594871490424985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187514919063247660283323 4781272378594871490424985)
          ·
            refine ⟨3585954283946153617818739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4781272378594871490424985 3585954283946153617818739)
            ·
              refine ⟨5378931425919230426728109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585954283946153617818739 5378931425919230426728109)
              ·
                refine ⟨2017099284719711410023041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5378931425919230426728109 2017099284719711410023041)
                ·
                  refine ⟨1512824463539783557517281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2017099284719711410023041 1512824463539783557517281)
                  ·
                    refine ⟨1134618347654837668137961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1512824463539783557517281 1134618347654837668137961)
                    ·
                      refine ⟨850963760741128251103471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134618347654837668137961 850963760741128251103471)
                      ·
                        rfl

theorem cell23_1657246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_1657246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657246 prefixEnd_1657246 := by exact prefixLift 1657246
  have htrace : WordTrace (prefixWord ++ tailWord_1657246) baseStart_1657246 baseEnd_1657246 := by
    simpa [prefixWord, tailWord_1657246, baseEnd_1657246] using wordTrace_append hprefix tailTrace_1657246
  have hstable : (prefixWord ++ tailWord_1657246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657246).length < 2 ^ (prefixWord ++ tailWord_1657246).sum := by decide
  have hdescent : baseEnd_1657246 < baseStart_1657246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657265 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 2, 5]
def baseStart_1657265 : Nat := 118140960795 + 1657265 * 2 ^ 59
def prefixEnd_1657265 : Nat := 4983230072969 + 3 ^ 40 * 1657265 * 2
def baseEnd_1657265 : Nat := 283657838957854558921961

theorem tailTrace_1657265 : CollatzResearch.WordTrace tailWord_1657265 prefixEnd_1657265 283657838957854558921961 := by
  unfold tailWord_1657265
  simp only [CollatzResearch.WordTrace]
  refine ⟨60445420341019418173277249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40296946894012945448851499 60445420341019418173277249)
  ·
    refine ⟨45334065255764563629957937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60445420341019418173277249 45334065255764563629957937)
    ·
      refine ⟨34000548941823422722468453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45334065255764563629957937 34000548941823422722468453)
      ·
        refine ⟨6375102926591891760462835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34000548941823422722468453 6375102926591891760462835)
        ·
          refine ⟨9562654389887837640694253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6375102926591891760462835 9562654389887837640694253)
          ·
            refine ⟨3585995396207939115260345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9562654389887837640694253 3585995396207939115260345)
            ·
              refine ⟨2689496547155954336445259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3585995396207939115260345 2689496547155954336445259)
              ·
                refine ⟨4034244820733931504667889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689496547155954336445259 4034244820733931504667889)
                ·
                  refine ⟨3025683615550448628500917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4034244820733931504667889 3025683615550448628500917)
                  ·
                    refine ⟨283657838957854558921961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3025683615550448628500917 283657838957854558921961)
                    ·
                      rfl

theorem cell23_1657265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_1657265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657265 prefixEnd_1657265 := by exact prefixLift 1657265
  have htrace : WordTrace (prefixWord ++ tailWord_1657265) baseStart_1657265 baseEnd_1657265 := by
    simpa [prefixWord, tailWord_1657265, baseEnd_1657265] using wordTrace_append hprefix tailTrace_1657265
  have hstable : (prefixWord ++ tailWord_1657265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657265).length < 2 ^ (prefixWord ++ tailWord_1657265).sum := by decide
  have hdescent : baseEnd_1657265 < baseStart_1657265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657322 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_1657322 : Nat := 118140960795 + 1657322 * 2 ^ 59
def prefixEnd_1657322 : Nat := 4983230072969 + 3 ^ 40 * 1657322 * 2
def baseEnd_1657322 : Nat := 851002785270869953753121

theorem tailTrace_1657322 : CollatzResearch.WordTrace tailWord_1657322 prefixEnd_1657322 851002785270869953753121 := by
  unfold tailWord_1657322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15111874825453229227025555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40298332867875277938734813 15111874825453229227025555)
  ·
    refine ⟨22667812238179843840538333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15111874825453229227025555 22667812238179843840538333)
    ·
      refine ⟨8500429589317441440201875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22667812238179843840538333 8500429589317441440201875)
      ·
        refine ⟨12750644383976162160302813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8500429589317441440201875 12750644383976162160302813)
        ·
          refine ⟨4781491643991060810113555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12750644383976162160302813 4781491643991060810113555)
          ·
            refine ⟨7172237465986591215170333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781491643991060810113555 7172237465986591215170333)
            ·
              refine ⟨2689589049744971705688875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7172237465986591215170333 2689589049744971705688875)
              ·
                refine ⟨4034383574617457558533313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689589049744971705688875 4034383574617457558533313)
                ·
                  refine ⟨3025787680963093168899985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4034383574617457558533313 3025787680963093168899985)
                  ·
                    refine ⟨2269340760722319876674989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3025787680963093168899985 2269340760722319876674989)
                    ·
                      refine ⟨851002785270869953753121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2269340760722319876674989 851002785270869953753121)
                      ·
                        rfl

theorem cell23_1657322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_1657322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657322 prefixEnd_1657322 := by exact prefixLift 1657322
  have htrace : WordTrace (prefixWord ++ tailWord_1657322) baseStart_1657322 baseEnd_1657322 := by
    simpa [prefixWord, tailWord_1657322, baseEnd_1657322] using wordTrace_append hprefix tailTrace_1657322
  have hstable : (prefixWord ++ tailWord_1657322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657322).length < 2 ^ (prefixWord ++ tailWord_1657322).sum := by decide
  have hdescent : baseEnd_1657322 < baseStart_1657322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657338 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_1657338 : Nat := 118140960795 + 1657338 * 2 ^ 59
def prefixEnd_1657338 : Nat := 4983230072969 + 3 ^ 40 * 1657338 * 2
def baseEnd_1657338 : Nat := 283670333653780630384349

theorem tailTrace_1657338 : CollatzResearch.WordTrace tailWord_1657338 prefixEnd_1657338 283670333653780630384349 := by
  unfold tailWord_1657338
  simp only [CollatzResearch.WordTrace]
  refine ⟨15112020717438737910171167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40298721913169967760456445 15112020717438737910171167)
  ·
    refine ⟨22668031076158106865256751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15112020717438737910171167 22668031076158106865256751)
    ·
      refine ⟨34002046614237160297885127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22668031076158106865256751 34002046614237160297885127)
      ·
        refine ⟨51003069921355740446827691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34002046614237160297885127 51003069921355740446827691)
        ·
          refine ⟨76504604882033610670241537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51003069921355740446827691 76504604882033610670241537)
          ·
            refine ⟨57378453661525208002681153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76504604882033610670241537 57378453661525208002681153)
            ·
              refine ⟨43033840246143906002010865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57378453661525208002681153 43033840246143906002010865)
              ·
                refine ⟨32275380184607929501508149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43033840246143906002010865 32275380184607929501508149)
                ·
                  refine ⟨3025816892306993390766389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32275380184607929501508149 3025816892306993390766389)
                  ·
                    refine ⟨283670333653780630384349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3025816892306993390766389 283670333653780630384349)
                    ·
                      rfl

theorem cell23_1657338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_1657338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657338 prefixEnd_1657338 := by exact prefixLift 1657338
  have htrace : WordTrace (prefixWord ++ tailWord_1657338) baseStart_1657338 baseEnd_1657338 := by
    simpa [prefixWord, tailWord_1657338, baseEnd_1657338] using wordTrace_append hprefix tailTrace_1657338
  have hstable : (prefixWord ++ tailWord_1657338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657338).length < 2 ^ (prefixWord ++ tailWord_1657338).sum := by decide
  have hdescent : baseEnd_1657338 < baseStart_1657338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657372 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1657372 : Nat := 118140960795 + 1657372 * 2 ^ 59
def prefixEnd_1657372 : Nat := 4983230072969 + 3 ^ 40 * 1657372 * 2
def baseEnd_1657372 : Nat := 283676153101198252709297

theorem tailTrace_1657372 : CollatzResearch.WordTrace tailWord_1657372 prefixEnd_1657372 283676153101198252709297 := by
  unfold tailWord_1657372
  simp only [CollatzResearch.WordTrace]
  refine ⟨30224661475815887723711185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40299548634421183631614913 30224661475815887723711185)
  ·
    refine ⟨22668496106861915792783389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30224661475815887723711185 22668496106861915792783389)
    ·
      refine ⟨8500686040073218422293771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22668496106861915792783389 8500686040073218422293771)
      ·
        refine ⟨12751029060109827633440657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8500686040073218422293771 12751029060109827633440657)
        ·
          refine ⟨9563271795082370725080493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12751029060109827633440657 9563271795082370725080493)
          ·
            refine ⟨3586226923155889021905185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9563271795082370725080493 3586226923155889021905185)
            ·
              refine ⟨2689670192366916766428889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586226923155889021905185 2689670192366916766428889)
              ·
                refine ⟨2017252644275187574821667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689670192366916766428889 2017252644275187574821667)
                ·
                  refine ⟨3025878966412781362232501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017252644275187574821667 3025878966412781362232501)
                  ·
                    refine ⟨283676153101198252709297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3025878966412781362232501 283676153101198252709297)
                    ·
                      rfl

theorem cell23_1657372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1657372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657372 prefixEnd_1657372 := by exact prefixLift 1657372
  have htrace : WordTrace (prefixWord ++ tailWord_1657372) baseStart_1657372 baseEnd_1657372 := by
    simpa [prefixWord, tailWord_1657372, baseEnd_1657372] using wordTrace_append hprefix tailTrace_1657372
  have hstable : (prefixWord ++ tailWord_1657372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657372).length < 2 ^ (prefixWord ++ tailWord_1657372).sum := by decide
  have hdescent : baseEnd_1657372 < baseStart_1657372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657375 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 1, 8, 2]
def baseStart_1657375 : Nat := 118140960795 + 1657375 * 2 ^ 59
def prefixEnd_1657375 : Nat := 4983230072969 + 3 ^ 40 * 1657375 * 2
def baseEnd_1657375 : Nat := 851029999745558246390377

theorem tailTrace_1657375 : CollatzResearch.WordTrace tailWord_1657375 prefixEnd_1657375 851029999745558246390377 := by
  unfold tailWord_1657375
  simp only [CollatzResearch.WordTrace]
  refine ⟨60449432370620906959781579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40299621580413937973187719 60449432370620906959781579)
  ·
    refine ⟨90674148555931360439672369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60449432370620906959781579 90674148555931360439672369)
    ·
      refine ⟨68005611416948520329754277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90674148555931360439672369 68005611416948520329754277)
      ·
        refine ⟨12751052140677847561828927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68005611416948520329754277 12751052140677847561828927)
        ·
          refine ⟨19126578211016771342743391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12751052140677847561828927 19126578211016771342743391)
          ·
            refine ⟨28689867316525157014115087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19126578211016771342743391 28689867316525157014115087)
            ·
              refine ⟨43034800974787735521172631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28689867316525157014115087 43034800974787735521172631)
              ·
                refine ⟨64552201462181603281758947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43034800974787735521172631 64552201462181603281758947)
                ·
                  refine ⟨96828302193272404922638421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64552201462181603281758947 96828302193272404922638421)
                  ·
                    refine ⟨1134706666327410995187169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96828302193272404922638421 1134706666327410995187169)
                    ·
                      refine ⟨851029999745558246390377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134706666327410995187169 851029999745558246390377)
                      ·
                        rfl

theorem cell23_1657375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_1657375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657375 prefixEnd_1657375 := by exact prefixLift 1657375
  have htrace : WordTrace (prefixWord ++ tailWord_1657375) baseStart_1657375 baseEnd_1657375 := by
    simpa [prefixWord, tailWord_1657375, baseEnd_1657375] using wordTrace_append hprefix tailTrace_1657375
  have hstable : (prefixWord ++ tailWord_1657375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657375).length < 2 ^ (prefixWord ++ tailWord_1657375).sum := by decide
  have hdescent : baseEnd_1657375 < baseStart_1657375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657386 : List Nat := [3, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_1657386 : Nat := 118140960795 + 1657386 * 2 ^ 59
def prefixEnd_1657386 : Nat := 4983230072969 + 3 ^ 40 * 1657386 * 2
def baseEnd_1657386 : Nat := 851035648032757703352827

theorem tailTrace_1657386 : CollatzResearch.WordTrace tailWord_1657386 prefixEnd_1657386 851035648032757703352827 := by
  unfold tailWord_1657386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15112458393395263959608003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40299889049054037225621341 15112458393395263959608003)
  ·
    refine ⟨22668687590092895939412005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15112458393395263959608003 22668687590092895939412005)
    ·
      refine ⟨4250378923142417988639751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22668687590092895939412005 4250378923142417988639751)
      ·
        refine ⟨6375568384713626982959627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4250378923142417988639751 6375568384713626982959627)
        ·
          refine ⟨9563352577070440474439441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6375568384713626982959627 9563352577070440474439441)
          ·
            refine ⟨7172514432802830355829581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9563352577070440474439441 7172514432802830355829581)
            ·
              refine ⟨2689692912301061383436093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7172514432802830355829581 2689692912301061383436093)
              ·
                refine ⟨1008634842112898018788535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2689692912301061383436093 1008634842112898018788535)
                ·
                  refine ⟨1512952263169347028182803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008634842112898018788535 1512952263169347028182803)
                  ·
                    refine ⟨2269428394754020542274205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1512952263169347028182803 2269428394754020542274205)
                    ·
                      refine ⟨851035648032757703352827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2269428394754020542274205 851035648032757703352827)
                      ·
                        rfl

theorem cell23_1657386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_1657386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657386 prefixEnd_1657386 := by exact prefixLift 1657386
  have htrace : WordTrace (prefixWord ++ tailWord_1657386) baseStart_1657386 baseEnd_1657386 := by
    simpa [prefixWord, tailWord_1657386, baseEnd_1657386] using wordTrace_append hprefix tailTrace_1657386
  have hstable : (prefixWord ++ tailWord_1657386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657386).length < 2 ^ (prefixWord ++ tailWord_1657386).sum := by decide
  have hdescent : baseEnd_1657386 < baseStart_1657386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657392 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 5, 2, 2]
def baseStart_1657392 : Nat := 118140960795 + 1657392 * 2 ^ 59
def prefixEnd_1657392 : Nat := 4983230072969 + 3 ^ 40 * 1657392 * 2
def baseEnd_1657392 : Nat := 851038728916684679877799

theorem tailTrace_1657392 : CollatzResearch.WordTrace tailWord_1657392 prefixEnd_1657392 851038728916684679877799 := by
  unfold tailWord_1657392
  simp only [CollatzResearch.WordTrace]
  refine ⟨30225026205779659431575215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40300034941039545908766953 30225026205779659431575215)
  ·
    refine ⟨45337539308669489147362823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30225026205779659431575215 45337539308669489147362823)
    ·
      refine ⟨68006308963004233721044235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45337539308669489147362823 68006308963004233721044235)
      ·
        refine ⟨102009463444506350581566353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68006308963004233721044235 102009463444506350581566353)
        ·
          refine ⟨76507097583379762936174765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102009463444506350581566353 76507097583379762936174765)
          ·
            refine ⟨28690161593767411101065537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76507097583379762936174765 28690161593767411101065537)
            ·
              refine ⟨21517621195325558325799153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28690161593767411101065537 21517621195325558325799153)
              ·
                refine ⟨16138215896494168744349365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21517621195325558325799153 16138215896494168744349365)
                ·
                  refine ⟨1512957740296328319782753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16138215896494168744349365 1512957740296328319782753)
                  ·
                    refine ⟨1134718305222246239837065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1512957740296328319782753 1134718305222246239837065)
                    ·
                      refine ⟨851038728916684679877799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134718305222246239837065 851038728916684679877799)
                      ·
                        rfl

theorem cell23_1657392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5, 2, 2].length) (baseStart_1657392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657392 prefixEnd_1657392 := by exact prefixLift 1657392
  have htrace : WordTrace (prefixWord ++ tailWord_1657392) baseStart_1657392 baseEnd_1657392 := by
    simpa [prefixWord, tailWord_1657392, baseEnd_1657392] using wordTrace_append hprefix tailTrace_1657392
  have hstable : (prefixWord ++ tailWord_1657392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657392).length < 2 ^ (prefixWord ++ tailWord_1657392).sum := by decide
  have hdescent : baseEnd_1657392 < baseStart_1657392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657395 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 5]
def baseStart_1657395 : Nat := 118140960795 + 1657395 * 2 ^ 59
def prefixEnd_1657395 : Nat := 4983230072969 + 3 ^ 40 * 1657395 * 2
def baseEnd_1657395 : Nat := 851040269358648168140285

theorem tailTrace_1657395 : CollatzResearch.WordTrace tailWord_1657395 prefixEnd_1657395 851040269358648168140285 := by
  unfold tailWord_1657395
  simp only [CollatzResearch.WordTrace]
  refine ⟨60450161830548450375509639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40300107887032300250339759 60450161830548450375509639)
  ·
    refine ⟨90675242745822675563264459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60450161830548450375509639 90675242745822675563264459)
    ·
      refine ⟨136012864118734013344896689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90675242745822675563264459 136012864118734013344896689)
      ·
        refine ⟨102009648089050510008672517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136012864118734013344896689 102009648089050510008672517)
        ·
          refine ⟨19126809016696970626626097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102009648089050510008672517 19126809016696970626626097)
          ·
            refine ⟨14345106762522727969969573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19126809016696970626626097 14345106762522727969969573)
            ·
              refine ⟨2689707517973011494369295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14345106762522727969969573 2689707517973011494369295)
              ·
                refine ⟨4034561276959517241553943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689707517973011494369295 4034561276959517241553943)
                ·
                  refine ⟨6051841915439275862330915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4034561276959517241553943 6051841915439275862330915)
                  ·
                    refine ⟨9077762873158913793496373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6051841915439275862330915 9077762873158913793496373)
                    ·
                      refine ⟨851040269358648168140285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9077762873158913793496373 851040269358648168140285)
                      ·
                        rfl

theorem cell23_1657395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 5].length) (baseStart_1657395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657395 prefixEnd_1657395 := by exact prefixLift 1657395
  have htrace : WordTrace (prefixWord ++ tailWord_1657395) baseStart_1657395 baseEnd_1657395 := by
    simpa [prefixWord, tailWord_1657395, baseEnd_1657395] using wordTrace_append hprefix tailTrace_1657395
  have hstable : (prefixWord ++ tailWord_1657395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657395).length < 2 ^ (prefixWord ++ tailWord_1657395).sum := by decide
  have hdescent : baseEnd_1657395 < baseStart_1657395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657405 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1657405 : Nat := 118140960795 + 1657405 * 2 ^ 59
def prefixEnd_1657405 : Nat := 4983230072969 + 3 ^ 40 * 1657405 * 2
def baseEnd_1657405 : Nat := 851045404165193129015239

theorem tailTrace_1657405 : CollatzResearch.WordTrace tailWord_1657405 prefixEnd_1657405 851045404165193129015239 := by
  unfold tailWord_1657405
  simp only [CollatzResearch.WordTrace]
  refine ⟨60450526560512222083373669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40300351040341481388915779 60450526560512222083373669)
  ·
    refine ⟨11334473730096041640632563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60450526560512222083373669 11334473730096041640632563)
    ·
      refine ⟨17001710595144062460948845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11334473730096041640632563 17001710595144062460948845)
      ·
        refine ⟨6375641473179023422855817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17001710595144062460948845 6375641473179023422855817)
        ·
          refine ⟨4781731104884267567141863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6375641473179023422855817 4781731104884267567141863)
          ·
            refine ⟨7172596657326401350712795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781731104884267567141863 7172596657326401350712795)
            ·
              refine ⟨10758894985989602026069193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7172596657326401350712795 10758894985989602026069193)
              ·
                refine ⟨8069171239492201519551895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10758894985989602026069193 8069171239492201519551895)
                ·
                  refine ⟨12103756859238302279327843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8069171239492201519551895 12103756859238302279327843)
                  ·
                    refine ⟨18155635288857453418991765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12103756859238302279327843 18155635288857453418991765)
                    ·
                      refine ⟨851045404165193129015239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18155635288857453418991765 851045404165193129015239)
                      ·
                        rfl

theorem cell23_1657405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1657405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657405 prefixEnd_1657405 := by exact prefixLift 1657405
  have htrace : WordTrace (prefixWord ++ tailWord_1657405) baseStart_1657405 baseEnd_1657405 := by
    simpa [prefixWord, tailWord_1657405, baseEnd_1657405] using wordTrace_append hprefix tailTrace_1657405
  have hstable : (prefixWord ++ tailWord_1657405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657405).length < 2 ^ (prefixWord ++ tailWord_1657405).sum := by decide
  have hdescent : baseEnd_1657405 < baseStart_1657405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657415 : List Nat := [1, 1, 4, 1, 4, 2, 2, 8]
def baseStart_1657415 : Nat := 118140960795 + 1657415 * 2 ^ 59
def prefixEnd_1657415 : Nat := 4983230072969 + 3 ^ 40 * 1657415 * 2
def baseEnd_1657415 : Nat := 31520390332286595921859

theorem tailTrace_1657415 : CollatzResearch.WordTrace tailWord_1657415 prefixEnd_1657415 31520390332286595921859 := by
  unfold tailWord_1657415
  simp only [CollatzResearch.WordTrace]
  refine ⟨60450891290475993791237699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40300594193650662527491799 60450891290475993791237699)
  ·
    refine ⟨90676336935713990686856549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60450891290475993791237699 90676336935713990686856549)
    ·
      refine ⟨17001813175446373253785603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90676336935713990686856549 17001813175446373253785603)
      ·
        refine ⟨25502719763169559880678405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17001813175446373253785603 25502719763169559880678405)
        ·
          refine ⟨4781759955594292477627201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25502719763169559880678405 4781759955594292477627201)
          ·
            refine ⟨3586319966695719358220401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4781759955594292477627201 3586319966695719358220401)
            ·
              refine ⟨2689739975021789518665301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586319966695719358220401 2689739975021789518665301)
              ·
                refine ⟨31520390332286595921859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2689739975021789518665301 31520390332286595921859)
                ·
                  rfl

theorem cell23_1657415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 8].length) (baseStart_1657415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657415 prefixEnd_1657415 := by exact prefixLift 1657415
  have htrace : WordTrace (prefixWord ++ tailWord_1657415) baseStart_1657415 baseEnd_1657415 := by
    simpa [prefixWord, tailWord_1657415, baseEnd_1657415] using wordTrace_append hprefix tailTrace_1657415
  have hstable : (prefixWord ++ tailWord_1657415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657415).length < 2 ^ (prefixWord ++ tailWord_1657415).sum := by decide
  have hdescent : baseEnd_1657415 < baseStart_1657415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657465 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1657465 : Nat := 118140960795 + 1657465 * 2 ^ 59
def prefixEnd_1657465 : Nat := 4983230072969 + 3 ^ 40 * 1657465 * 2
def baseEnd_1657465 : Nat := 851076213004462894264963

theorem tailTrace_1657465 : CollatzResearch.WordTrace tailWord_1657465 prefixEnd_1657465 851076213004462894264963 := by
  unfold tailWord_1657465
  simp only [CollatzResearch.WordTrace]
  refine ⟨60452714940294852330557849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40301809960196568220371899 60452714940294852330557849)
  ·
    refine ⟨45339536205221139247918387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60452714940294852330557849 45339536205221139247918387)
    ·
      refine ⟨68009304307831708871877581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45339536205221139247918387 68009304307831708871877581)
      ·
        refine ⟨25503489115436890826954093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68009304307831708871877581 25503489115436890826954093)
        ·
          refine ⟨9563808418288834060107785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25503489115436890826954093 9563808418288834060107785)
          ·
            refine ⟨7172856313716625545080839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9563808418288834060107785 7172856313716625545080839)
            ·
              refine ⟨10759284470574938317621259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7172856313716625545080839 10759284470574938317621259)
              ·
                refine ⟨16138926705862407476431889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10759284470574938317621259 16138926705862407476431889)
                ·
                  refine ⟨12104195029396805607323917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16138926705862407476431889 12104195029396805607323917)
                  ·
                    refine ⟨4539073136023802102746469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12104195029396805607323917 4539073136023802102746469)
                    ·
                      refine ⟨851076213004462894264963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4539073136023802102746469 851076213004462894264963)
                      ·
                        rfl

theorem cell23_1657465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1657465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657465 prefixEnd_1657465 := by exact prefixLift 1657465
  have htrace : WordTrace (prefixWord ++ tailWord_1657465) baseStart_1657465 baseEnd_1657465 := by
    simpa [prefixWord, tailWord_1657465, baseEnd_1657465] using wordTrace_append hprefix tailTrace_1657465
  have hstable : (prefixWord ++ tailWord_1657465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657465).length < 2 ^ (prefixWord ++ tailWord_1657465).sum := by decide
  have hdescent : baseEnd_1657465 < baseStart_1657465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657495 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1657495 : Nat := 118140960795 + 1657495 * 2 ^ 59
def prefixEnd_1657495 : Nat := 4983230072969 + 3 ^ 40 * 1657495 * 2
def baseEnd_1657495 : Nat := 851091617424097776889825

theorem tailTrace_1657495 : CollatzResearch.WordTrace tailWord_1657495 prefixEnd_1657495 851091617424097776889825 := by
  unfold tailWord_1657495
  simp only [CollatzResearch.WordTrace]
  refine ⟨60453809130186167454149939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40302539420124111636099959 60453809130186167454149939)
  ·
    refine ⟨90680713695279251181224909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60453809130186167454149939 90680713695279251181224909)
    ·
      refine ⟨34005267635729719192959341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90680713695279251181224909 34005267635729719192959341)
      ·
        refine ⟨12751975363398644697359753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34005267635729719192959341 12751975363398644697359753)
        ·
          refine ⟨9563981522548983523019815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12751975363398644697359753 9563981522548983523019815)
          ·
            refine ⟨14345972283823475284529723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9563981522548983523019815 14345972283823475284529723)
            ·
              refine ⟨21518958425735212926794585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14345972283823475284529723 21518958425735212926794585)
              ·
                refine ⟨16139218819301409695095939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21518958425735212926794585 16139218819301409695095939)
                ·
                  refine ⟨24208828228952114542643909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16139218819301409695095939 24208828228952114542643909)
                  ·
                    refine ⟨4539155292928521476745733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24208828228952114542643909 4539155292928521476745733)
                    ·
                      refine ⟨851091617424097776889825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4539155292928521476745733 851091617424097776889825)
                      ·
                        rfl

theorem cell23_1657495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1657495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657495 prefixEnd_1657495 := by exact prefixLift 1657495
  have htrace : WordTrace (prefixWord ++ tailWord_1657495) baseStart_1657495 baseEnd_1657495 := by
    simpa [prefixWord, tailWord_1657495, baseEnd_1657495] using wordTrace_append hprefix tailTrace_1657495
  have hstable : (prefixWord ++ tailWord_1657495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657495).length < 2 ^ (prefixWord ++ tailWord_1657495).sum := by decide
  have hdescent : baseEnd_1657495 < baseStart_1657495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657502 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1657502 : Nat := 118140960795 + 1657502 * 2 ^ 59
def prefixEnd_1657502 : Nat := 4983230072969 + 3 ^ 40 * 1657502 * 2
def baseEnd_1657502 : Nat := 851095211788679249502293

theorem tailTrace_1657502 : CollatzResearch.WordTrace tailWord_1657502 prefixEnd_1657502 851095211788679249502293 := by
  unfold tailWord_1657502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7556758055145100956206845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40302709627440538433103173 7556758055145100956206845)
  ·
    refine ⟨2833784270679412858577567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7556758055145100956206845 2833784270679412858577567)
    ·
      refine ⟨4250676406019119287866351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2833784270679412858577567 4250676406019119287866351)
      ·
        refine ⟨6376014609028678931799527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4250676406019119287866351 6376014609028678931799527)
        ·
          refine ⟨9564021913543018397699291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6376014609028678931799527 9564021913543018397699291)
          ·
            refine ⟨14346032870314527596548937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564021913543018397699291 14346032870314527596548937)
            ·
              refine ⟨10759524652735895697411703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14346032870314527596548937 10759524652735895697411703)
              ·
                refine ⟨16139286979103843546117555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10759524652735895697411703 16139286979103843546117555)
                ·
                  refine ⟨24208930468655765319176333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16139286979103843546117555 24208930468655765319176333)
                  ·
                    refine ⟨9078348925745911994691125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24208930468655765319176333 9078348925745911994691125)
                    ·
                      refine ⟨851095211788679249502293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9078348925745911994691125 851095211788679249502293)
                      ·
                        rfl

theorem cell23_1657502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1657502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657502 prefixEnd_1657502 := by exact prefixLift 1657502
  have htrace : WordTrace (prefixWord ++ tailWord_1657502) baseStart_1657502 baseEnd_1657502 := by
    simpa [prefixWord, tailWord_1657502, baseEnd_1657502] using wordTrace_append hprefix tailTrace_1657502
  have hstable : (prefixWord ++ tailWord_1657502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657502).length < 2 ^ (prefixWord ++ tailWord_1657502).sum := by decide
  have hdescent : baseEnd_1657502 < baseStart_1657502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657532 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1657532 : Nat := 118140960795 + 1657532 * 2 ^ 59
def prefixEnd_1657532 : Nat := 4983230072969 + 3 ^ 40 * 1657532 * 2
def baseEnd_1657532 : Nat := 851110616208314132127155

theorem tailTrace_1657532 : CollatzResearch.WordTrace tailWord_1657532 prefixEnd_1657532 851110616208314132127155 := by
  unfold tailWord_1657532
  simp only [CollatzResearch.WordTrace]
  refine ⟨30227579315526061386623425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40303439087368081848831233 30227579315526061386623425)
  ·
    refine ⟨22670684486644546039967569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30227579315526061386623425 22670684486644546039967569)
    ·
      refine ⟨17003013364983409529975677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22670684486644546039967569 17003013364983409529975677)
      ·
        refine ⟨6376130011868778573740879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17003013364983409529975677 6376130011868778573740879)
        ·
          refine ⟨9564195017803167860611319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6376130011868778573740879 9564195017803167860611319)
          ·
            refine ⟨14346292526704751790916979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564195017803167860611319 14346292526704751790916979)
            ·
              refine ⟨21519438790057127686375469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14346292526704751790916979 21519438790057127686375469)
              ·
                refine ⟨8069789546271422882390801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21519438790057127686375469 8069789546271422882390801)
                ·
                  refine ⟨6052342159703567161793101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8069789546271422882390801 6052342159703567161793101)
                  ·
                    refine ⟨2269628309888837685672413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6052342159703567161793101 2269628309888837685672413)
                    ·
                      refine ⟨851110616208314132127155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2269628309888837685672413 851110616208314132127155)
                      ·
                        rfl

theorem cell23_1657532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1657532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657532 prefixEnd_1657532 := by exact prefixLift 1657532
  have htrace : WordTrace (prefixWord ++ tailWord_1657532) baseStart_1657532 baseEnd_1657532 := by
    simpa [prefixWord, tailWord_1657532, baseEnd_1657532] using wordTrace_append hprefix tailTrace_1657532
  have hstable : (prefixWord ++ tailWord_1657532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657532).length < 2 ^ (prefixWord ++ tailWord_1657532).sum := by decide
  have hdescent : baseEnd_1657532 < baseStart_1657532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657533 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 2, 2, 2]
def baseStart_1657533 : Nat := 118140960795 + 1657533 * 2 ^ 59
def prefixEnd_1657533 : Nat := 4983230072969 + 3 ^ 40 * 1657533 * 2
def baseEnd_1657533 : Nat := 851111129688968628214651

theorem tailTrace_1657533 : CollatzResearch.WordTrace tailWord_1657533 prefixEnd_1657533 851111129688968628214651 := by
  unfold tailWord_1657533
  simp only [CollatzResearch.WordTrace]
  refine ⟨60455195104048499944033253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40303463402698999962688835 60455195104048499944033253)
  ·
    refine ⟨11335349082009093739506235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60455195104048499944033253 11335349082009093739506235)
    ·
      refine ⟨17003023623013640609259353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11335349082009093739506235 17003023623013640609259353)
      ·
        refine ⟨12752267717260230456944515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17003023623013640609259353 12752267717260230456944515)
        ·
          refine ⟨19128401575890345685416773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12752267717260230456944515 19128401575890345685416773)
          ·
            refine ⟨3586575295479439816015645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19128401575890345685416773 3586575295479439816015645)
            ·
              refine ⟨1344965735804789931005867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3586575295479439816015645 1344965735804789931005867)
              ·
                refine ⟨2017448603707184896508801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344965735804789931005867 2017448603707184896508801)
                ·
                  refine ⟨1513086452780388672381601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2017448603707184896508801 1513086452780388672381601)
                  ·
                    refine ⟨1134814839585291504286201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1513086452780388672381601 1134814839585291504286201)
                    ·
                      refine ⟨851111129688968628214651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134814839585291504286201 851111129688968628214651)
                      ·
                        rfl

theorem cell23_1657533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_1657533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657533 prefixEnd_1657533 := by exact prefixLift 1657533
  have htrace : WordTrace (prefixWord ++ tailWord_1657533) baseStart_1657533 baseEnd_1657533 := by
    simpa [prefixWord, tailWord_1657533, baseEnd_1657533] using wordTrace_append hprefix tailTrace_1657533
  have hstable : (prefixWord ++ tailWord_1657533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657533).length < 2 ^ (prefixWord ++ tailWord_1657533).sum := by decide
  have hdescent : baseEnd_1657533 < baseStart_1657533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657535 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 1, 7]
def baseStart_1657535 : Nat := 118140960795 + 1657535 * 2 ^ 59
def prefixEnd_1657535 : Nat := 4983230072969 + 3 ^ 40 * 1657535 * 2
def baseEnd_1657535 : Nat := 283704052216759206796547

theorem tailTrace_1657535 : CollatzResearch.WordTrace tailWord_1657535 prefixEnd_1657535 283704052216759206796547 := by
  unfold tailWord_1657535
  simp only [CollatzResearch.WordTrace]
  refine ⟨60455268050041254285606059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40303512033360836190404039 60455268050041254285606059)
  ·
    refine ⟨90682902075061881428409089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60455268050041254285606059 90682902075061881428409089)
    ·
      refine ⟨68012176556296411071306817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90682902075061881428409089 68012176556296411071306817)
      ·
        refine ⟨51009132417222308303480113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68012176556296411071306817 51009132417222308303480113)
        ·
          refine ⟨38256849312916731227610085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51009132417222308303480113 38256849312916731227610085)
          ·
            refine ⟨7173159246171887105176891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38256849312916731227610085 7173159246171887105176891)
            ·
              refine ⟨10759738869257830657765337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173159246171887105176891 10759738869257830657765337)
              ·
                refine ⟨8069804151943372993324003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10759738869257830657765337 8069804151943372993324003)
                ·
                  refine ⟨12104706227915059489986005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8069804151943372993324003 12104706227915059489986005)
                  ·
                    refine ⟨283704052216759206796547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12104706227915059489986005 283704052216759206796547)
                    ·
                      rfl

theorem cell23_1657535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_1657535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657535 prefixEnd_1657535 := by exact prefixLift 1657535
  have htrace : WordTrace (prefixWord ++ tailWord_1657535) baseStart_1657535 baseEnd_1657535 := by
    simpa [prefixWord, tailWord_1657535, baseEnd_1657535] using wordTrace_append hprefix tailTrace_1657535
  have hstable : (prefixWord ++ tailWord_1657535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657535).length < 2 ^ (prefixWord ++ tailWord_1657535).sum := by decide
  have hdescent : baseEnd_1657535 < baseStart_1657535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657572 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_1657572 : Nat := 118140960795 + 1657572 * 2 ^ 59
def prefixEnd_1657572 : Nat := 4983230072969 + 3 ^ 40 * 1657572 * 2
def baseEnd_1657572 : Nat := 851131155434493975626971

theorem tailTrace_1657572 : CollatzResearch.WordTrace tailWord_1657572 prefixEnd_1657572 851131155434493975626971 := by
  unfold tailWord_1657572
  simp only [CollatzResearch.WordTrace]
  refine ⟨30228308775453604802351485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40304411700604806403135313 30228308775453604802351485)
  ·
    refine ⟨11335615790795101800881807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30228308775453604802351485 11335615790795101800881807)
    ·
      refine ⟨17003423686192652701322711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11335615790795101800881807 17003423686192652701322711)
      ·
        refine ⟨25505135529288979051984067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17003423686192652701322711 25505135529288979051984067)
        ·
          refine ⟨38257703293933468577976101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25505135529288979051984067 38257703293933468577976101)
          ·
            refine ⟨7173319367612525358370519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38257703293933468577976101 7173319367612525358370519)
            ·
              refine ⟨10759979051418788037555779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173319367612525358370519 10759979051418788037555779)
              ·
                refine ⟨16139968577128182056333669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10759979051418788037555779 16139968577128182056333669)
                ·
                  refine ⟨3026244108211534135562563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16139968577128182056333669 3026244108211534135562563)
                  ·
                    refine ⟨4539366162317301203343845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3026244108211534135562563 4539366162317301203343845)
                    ·
                      refine ⟨851131155434493975626971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4539366162317301203343845 851131155434493975626971)
                      ·
                        rfl

theorem cell23_1657572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_1657572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657572 prefixEnd_1657572 := by exact prefixLift 1657572
  have htrace : WordTrace (prefixWord ++ tailWord_1657572) baseStart_1657572 baseEnd_1657572 := by
    simpa [prefixWord, tailWord_1657572, baseEnd_1657572] using wordTrace_append hprefix tailTrace_1657572
  have hstable : (prefixWord ++ tailWord_1657572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657572).length < 2 ^ (prefixWord ++ tailWord_1657572).sum := by decide
  have hdescent : baseEnd_1657572 < baseStart_1657572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657592 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 4, 2, 3]
def baseStart_1657592 : Nat := 118140960795 + 1657592 * 2 ^ 59
def prefixEnd_1657592 : Nat := 4983230072969 + 3 ^ 40 * 1657592 * 2
def baseEnd_1657592 : Nat := 851141425047583897376879

theorem tailTrace_1657592 : CollatzResearch.WordTrace tailWord_1657592 prefixEnd_1657592 851141425047583897376879 := by
  unfold tailWord_1657592
  simp only [CollatzResearch.WordTrace]
  refine ⟨30228673505417376510215515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40304898007223168680287353 30228673505417376510215515)
  ·
    refine ⟨45343010258126064765323273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30228673505417376510215515 45343010258126064765323273)
    ·
      refine ⟨34007257693594548573992455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45343010258126064765323273 34007257693594548573992455)
      ·
        refine ⟨51010886540391822860988683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34007257693594548573992455 51010886540391822860988683)
        ·
          refine ⟨76516329810587734291483025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51010886540391822860988683 76516329810587734291483025)
          ·
            refine ⟨57387247357940800718612269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76516329810587734291483025 57387247357940800718612269)
            ·
              refine ⟨21520217759227800269479601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57387247357940800718612269 21520217759227800269479601)
              ·
                refine ⟨16140163319420850202109701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21520217759227800269479601 16140163319420850202109701)
                ·
                  refine ⟨3026280622391409412895569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16140163319420850202109701 3026280622391409412895569)
                  ·
                    refine ⟨2269710466793557059671677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3026280622391409412895569 2269710466793557059671677)
                    ·
                      refine ⟨851141425047583897376879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2269710466793557059671677 851141425047583897376879)
                      ·
                        rfl

theorem cell23_1657592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_1657592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657592 prefixEnd_1657592 := by exact prefixLift 1657592
  have htrace : WordTrace (prefixWord ++ tailWord_1657592) baseStart_1657592 baseEnd_1657592 := by
    simpa [prefixWord, tailWord_1657592, baseEnd_1657592] using wordTrace_append hprefix tailTrace_1657592
  have hstable : (prefixWord ++ tailWord_1657592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657592).length < 2 ^ (prefixWord ++ tailWord_1657592).sum := by decide
  have hdescent : baseEnd_1657592 < baseStart_1657592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657649 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 1, 5, 2]
def baseStart_1657649 : Nat := 118140960795 + 1657649 * 2 ^ 59
def prefixEnd_1657649 : Nat := 4983230072969 + 3 ^ 40 * 1657649 * 2
def baseEnd_1657649 : Nat := 851170693444890174364117

theorem tailTrace_1657649 : CollatzResearch.WordTrace tailWord_1657649 prefixEnd_1657649 851170693444890174364117 := by
  unfold tailWord_1657649
  simp only [CollatzResearch.WordTrace]
  refine ⟨60459425971628251755256001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40306283981085501170170667 60459425971628251755256001)
  ·
    refine ⟨45344569478721188816442001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60459425971628251755256001 45344569478721188816442001)
    ·
      refine ⟨34008427109040891612331501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45344569478721188816442001 34008427109040891612331501)
      ·
        refine ⟨12753160165890334354624313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34008427109040891612331501 12753160165890334354624313)
        ·
          refine ⟨9564870124417750765968235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12753160165890334354624313 9564870124417750765968235)
          ·
            refine ⟨14347305186626626148952353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564870124417750765968235 14347305186626626148952353)
            ·
              refine ⟨10760478889969969611714265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14347305186626626148952353 10760478889969969611714265)
              ·
                refine ⟨8070359167477477208785699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10760478889969969611714265 8070359167477477208785699)
                ·
                  refine ⟨12105538751216215813178549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8070359167477477208785699 12105538751216215813178549)
                  ·
                    refine ⟨1134894257926520232485489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12105538751216215813178549 1134894257926520232485489)
                    ·
                      refine ⟨851170693444890174364117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134894257926520232485489 851170693444890174364117)
                      ·
                        rfl

theorem cell23_1657649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_1657649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657649 prefixEnd_1657649 := by exact prefixLift 1657649
  have htrace : WordTrace (prefixWord ++ tailWord_1657649) baseStart_1657649 baseEnd_1657649 := by
    simpa [prefixWord, tailWord_1657649, baseEnd_1657649] using wordTrace_append hprefix tailTrace_1657649
  have hstable : (prefixWord ++ tailWord_1657649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657649).length < 2 ^ (prefixWord ++ tailWord_1657649).sum := by decide
  have hdescent : baseEnd_1657649 < baseStart_1657649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657672 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 1, 6]
def baseStart_1657672 : Nat := 118140960795 + 1657672 * 2 ^ 59
def prefixEnd_1657672 : Nat := 4983230072969 + 3 ^ 40 * 1657672 * 2
def baseEnd_1657672 : Nat := 283727501166647861458837

theorem tailTrace_1657672 : CollatzResearch.WordTrace tailWord_1657672 prefixEnd_1657672 283727501166647861458837 := by
  unfold tailWord_1657672
  simp only [CollatzResearch.WordTrace]
  refine ⟨30230132425272463341671635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40306843233696617788895513 30230132425272463341671635)
  ·
    refine ⟨45345198637908695012507453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30230132425272463341671635 45345198637908695012507453)
    ·
      refine ⟨17004449489215760629690295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45345198637908695012507453 17004449489215760629690295)
      ·
        refine ⟨25506674233823640944535443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17004449489215760629690295 25506674233823640944535443)
        ·
          refine ⟨38260011350735461416803165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25506674233823640944535443 38260011350735461416803165)
          ·
            refine ⟨14347504256525798031301187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38260011350735461416803165 14347504256525798031301187)
            ·
              refine ⟨21521256384788697046951781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14347504256525798031301187 21521256384788697046951781)
              ·
                refine ⟨4035235572147880696303459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21521256384788697046951781 4035235572147880696303459)
                ·
                  refine ⟨6052853358221821044455189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035235572147880696303459 6052853358221821044455189)
                  ·
                    refine ⟨283727501166647861458837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6052853358221821044455189 283727501166647861458837)
                    ·
                      rfl

theorem cell23_1657672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_1657672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657672 prefixEnd_1657672 := by exact prefixLift 1657672
  have htrace : WordTrace (prefixWord ++ tailWord_1657672) baseStart_1657672 baseEnd_1657672 := by
    simpa [prefixWord, tailWord_1657672, baseEnd_1657672] using wordTrace_append hprefix tailTrace_1657672
  have hstable : (prefixWord ++ tailWord_1657672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657672).length < 2 ^ (prefixWord ++ tailWord_1657672).sum := by decide
  have hdescent : baseEnd_1657672 < baseStart_1657672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657673 : List Nat := [1, 2, 1, 1, 2, 6, 2, 3, 1, 1, 3]
def baseStart_1657673 : Nat := 118140960795 + 1657673 * 2 ^ 59
def prefixEnd_1657673 : Nat := 4983230072969 + 3 ^ 40 * 1657673 * 2
def baseEnd_1657673 : Nat := 851183016980598080464007

theorem tailTrace_1657673 : CollatzResearch.WordTrace tailWord_1657673 prefixEnd_1657673 851183016980598080464007 := by
  unfold tailWord_1657673
  simp only [CollatzResearch.WordTrace]
  refine ⟨60460301323541303854129673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40306867549027535902753115 60460301323541303854129673)
  ·
    refine ⟨45345225992655977890597255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60460301323541303854129673 45345225992655977890597255)
    ·
      refine ⟨68017838988983966835895883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45345225992655977890597255 68017838988983966835895883)
      ·
        refine ⟨102026758483475950253843825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68017838988983966835895883 102026758483475950253843825)
        ·
          refine ⟨76520068862606962690382869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102026758483475950253843825 76520068862606962690382869)
          ·
            refine ⟨3586878227934701376111697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76520068862606962690382869 3586878227934701376111697)
            ·
              refine ⟨2690158670951026032083773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586878227934701376111697 2690158670951026032083773)
              ·
                refine ⟨1008809501606634762031415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2690158670951026032083773 1008809501606634762031415)
                ·
                  refine ⟨1513214252409952143047123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008809501606634762031415 1513214252409952143047123)
                  ·
                    refine ⟨2269821378614928214570685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1513214252409952143047123 2269821378614928214570685)
                    ·
                      refine ⟨851183016980598080464007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2269821378614928214570685 851183016980598080464007)
                      ·
                        rfl

theorem cell23_1657673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 1, 1, 3].length) (baseStart_1657673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657673 prefixEnd_1657673 := by exact prefixLift 1657673
  have htrace : WordTrace (prefixWord ++ tailWord_1657673) baseStart_1657673 baseEnd_1657673 := by
    simpa [prefixWord, tailWord_1657673, baseEnd_1657673] using wordTrace_append hprefix tailTrace_1657673
  have hstable : (prefixWord ++ tailWord_1657673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657673).length < 2 ^ (prefixWord ++ tailWord_1657673).sum := by decide
  have hdescent : baseEnd_1657673 < baseStart_1657673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657676 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 1, 5]
def baseStart_1657676 : Nat := 118140960795 + 1657676 * 2 ^ 59
def prefixEnd_1657676 : Nat := 4983230072969 + 3 ^ 40 * 1657676 * 2
def baseEnd_1657676 : Nat := 283728185807520522908831

theorem tailTrace_1657676 : CollatzResearch.WordTrace tailWord_1657676 prefixEnd_1657676 283728185807520522908831 := by
  unfold tailWord_1657676
  simp only [CollatzResearch.WordTrace]
  refine ⟨30230205371265217683244441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40306940495020290244325921 30230205371265217683244441)
  ·
    refine ⟨22672654028448913262433331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30230205371265217683244441 22672654028448913262433331)
    ·
      refine ⟨34008981042673369893649997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22672654028448913262433331 34008981042673369893649997)
      ·
        refine ⟨12753367891002513710118749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34008981042673369893649997 12753367891002513710118749)
        ·
          refine ⟨4782512959125942641294531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12753367891002513710118749 4782512959125942641294531)
          ·
            refine ⟨7173769438688913961941797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782512959125942641294531 7173769438688913961941797)
            ·
              refine ⟨1345081769754171367864087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7173769438688913961941797 1345081769754171367864087)
              ·
                refine ⟨2017622654631257051796131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345081769754171367864087 2017622654631257051796131)
                ·
                  refine ⟨3026433981946885577694197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017622654631257051796131 3026433981946885577694197)
                  ·
                    refine ⟨283728185807520522908831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3026433981946885577694197 283728185807520522908831)
                    ·
                      rfl

theorem cell23_1657676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_1657676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657676 prefixEnd_1657676 := by exact prefixLift 1657676
  have htrace : WordTrace (prefixWord ++ tailWord_1657676) baseStart_1657676 baseEnd_1657676 := by
    simpa [prefixWord, tailWord_1657676, baseEnd_1657676] using wordTrace_append hprefix tailTrace_1657676
  have hstable : (prefixWord ++ tailWord_1657676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657676).length < 2 ^ (prefixWord ++ tailWord_1657676).sum := by decide
  have hdescent : baseEnd_1657676 < baseStart_1657676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657689 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 4, 4]
def baseStart_1657689 : Nat := 118140960795 + 1657689 * 2 ^ 59
def prefixEnd_1657689 : Nat := 4983230072969 + 3 ^ 40 * 1657689 * 2
def baseEnd_1657689 : Nat := 283730410890356672621311

theorem tailTrace_1657689 : CollatzResearch.WordTrace tailWord_1657689 prefixEnd_1657689 283730410890356672621311 := by
  unfold tailWord_1657689
  simp only [CollatzResearch.WordTrace]
  refine ⟨60460884891483338586712121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40307256594322225724474747 60460884891483338586712121)
  ·
    refine ⟨45345663668612503940034091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60460884891483338586712121 45345663668612503940034091)
    ·
      refine ⟨68018495502918755910051137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45345663668612503940034091 68018495502918755910051137)
      ·
        refine ⟨51013871627189066932538353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68018495502918755910051137 51013871627189066932538353)
        ·
          refine ⟨38260403720391800199403765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51013871627189066932538353 38260403720391800199403765)
          ·
            refine ⟨3586912848786731268694103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38260403720391800199403765 3586912848786731268694103)
            ·
              refine ⟨5380369273180096903041155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586912848786731268694103 5380369273180096903041155)
              ·
                refine ⟨8070553909770145354561733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5380369273180096903041155 8070553909770145354561733)
                ·
                  refine ⟨1513228858081902253980325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8070553909770145354561733 1513228858081902253980325)
                  ·
                    refine ⟨283730410890356672621311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1513228858081902253980325 283730410890356672621311)
                    ·
                      rfl

theorem cell23_1657689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 4].length) (baseStart_1657689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657689 prefixEnd_1657689 := by exact prefixLift 1657689
  have htrace : WordTrace (prefixWord ++ tailWord_1657689) baseStart_1657689 baseEnd_1657689 := by
    simpa [prefixWord, tailWord_1657689, baseEnd_1657689] using wordTrace_append hprefix tailTrace_1657689
  have hstable : (prefixWord ++ tailWord_1657689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657689).length < 2 ^ (prefixWord ++ tailWord_1657689).sum := by decide
  have hdescent : baseEnd_1657689 < baseStart_1657689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657699 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1657699 : Nat := 118140960795 + 1657699 * 2 ^ 59
def prefixEnd_1657699 : Nat := 4983230072969 + 3 ^ 40 * 1657699 * 2
def baseEnd_1657699 : Nat := 851196367477614978738887

theorem tailTrace_1657699 : CollatzResearch.WordTrace tailWord_1657699 prefixEnd_1657699 851196367477614978738887 := by
  unfold tailWord_1657699
  simp only [CollatzResearch.WordTrace]
  refine ⟨60461249621447110294576151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40307499747631406863050767 60461249621447110294576151)
  ·
    refine ⟨90691874432170665441864227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60461249621447110294576151 90691874432170665441864227)
    ·
      refine ⟨136037811648255998162796341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90691874432170665441864227 136037811648255998162796341)
      ·
        refine ⟨12753544842023999827762157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136037811648255998162796341 12753544842023999827762157)
        ·
          refine ⟨4782579315758999935410809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12753544842023999827762157 4782579315758999935410809)
          ·
            refine ⟨3586934486819249951558107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4782579315758999935410809 3586934486819249951558107)
            ·
              refine ⟨5380401730228874927337161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586934486819249951558107 5380401730228874927337161)
              ·
                refine ⟨4035301297671656195502871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5380401730228874927337161 4035301297671656195502871)
                ·
                  refine ⟨6052951946507484293254307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035301297671656195502871 6052951946507484293254307)
                  ·
                    refine ⟨9079427919761226439881461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6052951946507484293254307 9079427919761226439881461)
                    ·
                      refine ⟨851196367477614978738887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9079427919761226439881461 851196367477614978738887)
                      ·
                        rfl

theorem cell23_1657699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1657699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657699 prefixEnd_1657699 := by exact prefixLift 1657699
  have htrace : WordTrace (prefixWord ++ tailWord_1657699) baseStart_1657699 baseEnd_1657699 := by
    simpa [prefixWord, tailWord_1657699, baseEnd_1657699] using wordTrace_append hprefix tailTrace_1657699
  have hstable : (prefixWord ++ tailWord_1657699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657699).length < 2 ^ (prefixWord ++ tailWord_1657699).sum := by decide
  have hdescent : baseEnd_1657699 < baseStart_1657699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657732 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1657732 : Nat := 118140960795 + 1657732 * 2 ^ 59
def prefixEnd_1657732 : Nat := 4983230072969 + 3 ^ 40 * 1657732 * 2
def baseEnd_1657732 : Nat := 283737770779737783208745

theorem tailTrace_1657732 : CollatzResearch.WordTrace tailWord_1657732 prefixEnd_1657732 283737770779737783208745 := by
  unfold tailWord_1657732
  simp only [CollatzResearch.WordTrace]
  refine ⟨30231226615163778465263725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40308302153551704620351633 30231226615163778465263725)
  ·
    refine ⟨11336709980686416924473897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30231226615163778465263725 11336709980686416924473897)
    ·
      refine ⟨8502532485514812693355423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11336709980686416924473897 8502532485514812693355423)
      ·
        refine ⟨12753798728272219040033135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8502532485514812693355423 12753798728272219040033135)
        ·
          refine ⟨19130698092408328560049703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12753798728272219040033135 19130698092408328560049703)
          ·
            refine ⟨28696047138612492840074555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19130698092408328560049703 28696047138612492840074555)
            ·
              refine ⟨43044070707918739260111833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28696047138612492840074555 43044070707918739260111833)
              ·
                refine ⟨32283053030939054445083875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43044070707918739260111833 32283053030939054445083875)
                ·
                  refine ⟨48424579546408581667625813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32283053030939054445083875 48424579546408581667625813)
                  ·
                    refine ⟨283737770779737783208745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 48424579546408581667625813 283737770779737783208745)
                    ·
                      rfl

theorem cell23_1657732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1657732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657732 prefixEnd_1657732 := by exact prefixLift 1657732
  have htrace : WordTrace (prefixWord ++ tailWord_1657732) baseStart_1657732 baseEnd_1657732 := by
    simpa [prefixWord, tailWord_1657732, baseEnd_1657732] using wordTrace_append hprefix tailTrace_1657732
  have hstable : (prefixWord ++ tailWord_1657732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657732).length < 2 ^ (prefixWord ++ tailWord_1657732).sum := by decide
  have hdescent : baseEnd_1657732 < baseStart_1657732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657763 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 2, 1, 3]
def baseStart_1657763 : Nat := 118140960795 + 1657763 * 2 ^ 59
def prefixEnd_1657763 : Nat := 4983230072969 + 3 ^ 40 * 1657763 * 2
def baseEnd_1657763 : Nat := 851229230239502728338593

theorem tailTrace_1657763 : CollatzResearch.WordTrace tailWord_1657763 prefixEnd_1657763 851229230239502728338593 := by
  unfold tailWord_1657763
  simp only [CollatzResearch.WordTrace]
  refine ⟨60463583893215249224905943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40309055928810166149937295 60463583893215249224905943)
  ·
    refine ⟨90695375839822873837358915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60463583893215249224905943 90695375839822873837358915)
    ·
      refine ⟨136043063759734310756038373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90695375839822873837358915 136043063759734310756038373)
      ·
        refine ⟨25508074454950183266757195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136043063759734310756038373 25508074454950183266757195)
        ·
          refine ⟨38262111682425274900135793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25508074454950183266757195 38262111682425274900135793)
          ·
            refine ⟨28696583761818956175101845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38262111682425274900135793 28696583761818956175101845)
            ·
              refine ⟨1345152363835263570707899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28696583761818956175101845 1345152363835263570707899)
              ·
                refine ⟨2017728545752895356061849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345152363835263570707899 2017728545752895356061849)
                ·
                  refine ⟨1513296409314671517046387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2017728545752895356061849 1513296409314671517046387)
                  ·
                    refine ⟨2269944613972007275569581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1513296409314671517046387 2269944613972007275569581)
                    ·
                      refine ⟨851229230239502728338593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2269944613972007275569581 851229230239502728338593)
                      ·
                        rfl

theorem cell23_1657763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_1657763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657763 prefixEnd_1657763 := by exact prefixLift 1657763
  have htrace : WordTrace (prefixWord ++ tailWord_1657763) baseStart_1657763 baseEnd_1657763 := by
    simpa [prefixWord, tailWord_1657763, baseEnd_1657763] using wordTrace_append hprefix tailTrace_1657763
  have hstable : (prefixWord ++ tailWord_1657763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657763).length < 2 ^ (prefixWord ++ tailWord_1657763).sum := by decide
  have hdescent : baseEnd_1657763 < baseStart_1657763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657772 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_1657772 : Nat := 118140960795 + 1657772 * 2 ^ 59
def prefixEnd_1657772 : Nat := 4983230072969 + 3 ^ 40 * 1657772 * 2
def baseEnd_1657772 : Nat := 851233851565393193126051

theorem tailTrace_1657772 : CollatzResearch.WordTrace tailWord_1657772 prefixEnd_1657772 851233851565393193126051 := by
  unfold tailWord_1657772
  simp only [CollatzResearch.WordTrace]
  refine ⟨30231956075091321880991785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40309274766788429174655713 30231956075091321880991785)
  ·
    refine ⟨22673967056318491410743839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30231956075091321880991785 22673967056318491410743839)
    ·
      refine ⟨34010950584477737116115759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22673967056318491410743839 34010950584477737116115759)
      ·
        refine ⟨51016425876716605674173639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34010950584477737116115759 51016425876716605674173639)
        ·
          refine ⟨76524638815074908511260459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51016425876716605674173639 76524638815074908511260459)
          ·
            refine ⟨114786958222612362766890689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76524638815074908511260459 114786958222612362766890689)
            ·
              refine ⟨86090218666959272075168017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114786958222612362766890689 86090218666959272075168017)
              ·
                refine ⟨64567664000219454056376013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86090218666959272075168017 64567664000219454056376013)
                ·
                  refine ⟨24212874000082295271141005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64567664000219454056376013 24212874000082295271141005)
                  ·
                    refine ⟨9079827750030860726677877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24212874000082295271141005 9079827750030860726677877)
                    ·
                      refine ⟨851233851565393193126051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9079827750030860726677877 851233851565393193126051)
                      ·
                        rfl

theorem cell23_1657772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_1657772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657772 prefixEnd_1657772 := by exact prefixLift 1657772
  have htrace : WordTrace (prefixWord ++ tailWord_1657772) baseStart_1657772 baseEnd_1657772 := by
    simpa [prefixWord, tailWord_1657772, baseEnd_1657772] using wordTrace_append hprefix tailTrace_1657772
  have hstable : (prefixWord ++ tailWord_1657772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657772).length < 2 ^ (prefixWord ++ tailWord_1657772).sum := by decide
  have hdescent : baseEnd_1657772 < baseStart_1657772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657786 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2]
def baseStart_1657786 : Nat := 118140960795 + 1657786 * 2 ^ 59
def prefixEnd_1657786 : Nat := 4983230072969 + 3 ^ 40 * 1657786 * 2
def baseEnd_1657786 : Nat := 851241040294556138350987

theorem tailTrace_1657786 : CollatzResearch.WordTrace tailWord_1657786 prefixEnd_1657786 851241040294556138350987 := by
  unfold tailWord_1657786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15116105693032981038248303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40309615181421282768662141 15116105693032981038248303)
  ·
    refine ⟨22674158539549471557372455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15116105693032981038248303 22674158539549471557372455)
    ·
      refine ⟨34011237809324207336058683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22674158539549471557372455 34011237809324207336058683)
      ·
        refine ⟨51016856713986311004088025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34011237809324207336058683 51016856713986311004088025)
        ·
          refine ⟨38262642535489733253066019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51016856713986311004088025 38262642535489733253066019)
          ·
            refine ⟨57393963803234599879599029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38262642535489733253066019 57393963803234599879599029)
            ·
              refine ⟨5380684106553243738712409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57393963803234599879599029 5380684106553243738712409)
              ·
                refine ⟨4035513079914932804034307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5380684106553243738712409 4035513079914932804034307)
                ·
                  refine ⟨6053269619872399206051461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035513079914932804034307 6053269619872399206051461)
                  ·
                    refine ⟨1134988053726074851134649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6053269619872399206051461 1134988053726074851134649)
                    ·
                      refine ⟨851241040294556138350987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134988053726074851134649 851241040294556138350987)
                      ·
                        rfl

theorem cell23_1657786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2].length) (baseStart_1657786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657786 prefixEnd_1657786 := by exact prefixLift 1657786
  have htrace : WordTrace (prefixWord ++ tailWord_1657786) baseStart_1657786 baseEnd_1657786 := by
    simpa [prefixWord, tailWord_1657786, baseEnd_1657786] using wordTrace_append hprefix tailTrace_1657786
  have hstable : (prefixWord ++ tailWord_1657786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657786).length < 2 ^ (prefixWord ++ tailWord_1657786).sum := by decide
  have hdescent : baseEnd_1657786 < baseStart_1657786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657790 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_1657790 : Nat := 118140960795 + 1657790 * 2 ^ 59
def prefixEnd_1657790 : Nat := 4983230072969 + 3 ^ 40 * 1657790 * 2
def baseEnd_1657790 : Nat := 851243094217174122700969

theorem tailTrace_1657790 : CollatzResearch.WordTrace tailWord_1657790 prefixEnd_1657790 851243094217174122700969 := by
  unfold tailWord_1657790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7558071083014679104517353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40309712442744955224092549 7558071083014679104517353)
  ·
    refine ⟨5668553312261009328388015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7558071083014679104517353 5668553312261009328388015)
    ·
      refine ⟨8502829968391513992582023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5668553312261009328388015 8502829968391513992582023)
      ·
        refine ⟨12754244952587270988873035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8502829968391513992582023 12754244952587270988873035)
        ·
          refine ⟨19131367428880906483309553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12754244952587270988873035 19131367428880906483309553)
          ·
            refine ⟨14348525571660679862482165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19131367428880906483309553 14348525571660679862482165)
            ·
              refine ⟨1345174272343188737107703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14348525571660679862482165 1345174272343188737107703)
              ·
                refine ⟨2017761408514783105661555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345174272343188737107703 2017761408514783105661555)
                ·
                  refine ⟨3026642112772174658492333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017761408514783105661555 3026642112772174658492333)
                  ·
                    refine ⟨1134990792289565496934625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3026642112772174658492333 1134990792289565496934625)
                    ·
                      refine ⟨851243094217174122700969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134990792289565496934625 851243094217174122700969)
                      ·
                        rfl

theorem cell23_1657790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_1657790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657790 prefixEnd_1657790 := by exact prefixLift 1657790
  have htrace : WordTrace (prefixWord ++ tailWord_1657790) baseStart_1657790 baseEnd_1657790 := by
    simpa [prefixWord, tailWord_1657790, baseEnd_1657790] using wordTrace_append hprefix tailTrace_1657790
  have hstable : (prefixWord ++ tailWord_1657790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657790).length < 2 ^ (prefixWord ++ tailWord_1657790).sum := by decide
  have hdescent : baseEnd_1657790 < baseStart_1657790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657798 : List Nat := [6, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_1657798 : Nat := 118140960795 + 1657798 * 2 ^ 59
def prefixEnd_1657798 : Nat := 4983230072969 + 3 ^ 40 * 1657798 * 2
def baseEnd_1657798 : Nat := 851247202062410091400933

theorem tailTrace_1657798 : CollatzResearch.WordTrace tailWord_1657798 prefixEnd_1657798 851247202062410091400933 := by
  unfold tailWord_1657798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889526889002764068825939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40309906965392300134953365 1889526889002764068825939)
  ·
    refine ⟨2834290333504146103238909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1889526889002764068825939 2834290333504146103238909)
    ·
      refine ⟨1062858875064054788714591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2834290333504146103238909 1062858875064054788714591)
      ·
        refine ⟨1594288312596082183071887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062858875064054788714591 1594288312596082183071887)
        ·
          refine ⟨2391432468894123274607831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594288312596082183071887 2391432468894123274607831)
          ·
            refine ⟨3587148703341184911911747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391432468894123274607831 3587148703341184911911747)
            ·
              refine ⟨5380723055011777367867621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587148703341184911911747 5380723055011777367867621)
              ·
                refine ⟨1008885572814708256475179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5380723055011777367867621 1008885572814708256475179)
                ·
                  refine ⟨1513328359222062384712769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008885572814708256475179 1513328359222062384712769)
                  ·
                    refine ⟨1134996269416546788534577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1513328359222062384712769 1134996269416546788534577)
                    ·
                      refine ⟨851247202062410091400933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134996269416546788534577 851247202062410091400933)
                      ·
                        rfl

theorem cell23_1657798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_1657798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657798 prefixEnd_1657798 := by exact prefixLift 1657798
  have htrace : WordTrace (prefixWord ++ tailWord_1657798) baseStart_1657798 baseEnd_1657798 := by
    simpa [prefixWord, tailWord_1657798, baseEnd_1657798] using wordTrace_append hprefix tailTrace_1657798
  have hstable : (prefixWord ++ tailWord_1657798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657798).length < 2 ^ (prefixWord ++ tailWord_1657798).sum := by decide
  have hdescent : baseEnd_1657798 < baseStart_1657798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657803 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 2, 2, 2]
def baseStart_1657803 : Nat := 118140960795 + 1657803 * 2 ^ 59
def prefixEnd_1657803 : Nat := 4983230072969 + 3 ^ 40 * 1657803 * 2
def baseEnd_1657803 : Nat := 851249769465682571838409

theorem tailTrace_1657803 : CollatzResearch.WordTrace tailWord_1657803 prefixEnd_1657803 851249769465682571838409 := by
  unfold tailWord_1657803
  simp only [CollatzResearch.WordTrace]
  refine ⟨60465042813070336056362063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40310028542046890704241375 60465042813070336056362063)
  ·
    refine ⟨90697564219605504084543095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60465042813070336056362063 90697564219605504084543095)
    ·
      refine ⟨136046346329408256126814643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90697564219605504084543095 136046346329408256126814643)
      ·
        refine ⟨204069519494112384190221965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136046346329408256126814643 204069519494112384190221965)
        ·
          refine ⟨76526069810292144071333237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204069519494112384190221965 76526069810292144071333237)
          ·
            refine ⟨7174319044714888506687491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76526069810292144071333237 7174319044714888506687491)
            ·
              refine ⟨10761478567072332760031237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7174319044714888506687491 10761478567072332760031237)
              ·
                refine ⟨2017777231326062392505857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10761478567072332760031237 2017777231326062392505857)
                ·
                  refine ⟨1513332923494546794379393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2017777231326062392505857 1513332923494546794379393)
                  ·
                    refine ⟨1134999692620910095784545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1513332923494546794379393 1134999692620910095784545)
                    ·
                      refine ⟨851249769465682571838409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1134999692620910095784545 851249769465682571838409)
                      ·
                        rfl

theorem cell23_1657803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 2, 2].length) (baseStart_1657803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657803 prefixEnd_1657803 := by exact prefixLift 1657803
  have htrace : WordTrace (prefixWord ++ tailWord_1657803) baseStart_1657803 baseEnd_1657803 := by
    simpa [prefixWord, tailWord_1657803, baseEnd_1657803] using wordTrace_append hprefix tailTrace_1657803
  have hstable : (prefixWord ++ tailWord_1657803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657803).length < 2 ^ (prefixWord ++ tailWord_1657803).sum := by decide
  have hdescent : baseEnd_1657803 < baseStart_1657803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657826 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 9]
def baseStart_1657826 : Nat := 118140960795 + 1657826 * 2 ^ 59
def prefixEnd_1657826 : Nat := 4983230072969 + 3 ^ 40 * 1657826 * 2
def baseEnd_1657826 : Nat := 94584619946748442427867

theorem tailTrace_1657826 : CollatzResearch.WordTrace tailWord_1657826 prefixEnd_1657826 94584619946748442427867 := by
  unfold tailWord_1657826
  simp only [CollatzResearch.WordTrace]
  refine ⟨15116470422996752746112333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40310587794658007322966221 15116470422996752746112333)
  ·
    refine ⟨5668676408623782279792125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15116470422996752746112333 5668676408623782279792125)
    ·
      refine ⟨2125753653233918354922047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5668676408623782279792125 2125753653233918354922047)
      ·
        refine ⟨3188630479850877532383071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2125753653233918354922047 3188630479850877532383071)
        ·
          refine ⟨4782945719776316298574607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188630479850877532383071 4782945719776316298574607)
          ·
            refine ⟨7174418579664474447861911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782945719776316298574607 7174418579664474447861911)
            ·
              refine ⟨10761627869496711671792867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7174418579664474447861911 10761627869496711671792867)
              ·
                refine ⟨16142441804245067507689301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10761627869496711671792867 16142441804245067507689301)
                ·
                  refine ⟨94584619946748442427867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16142441804245067507689301 94584619946748442427867)
                  ·
                    rfl

theorem cell23_1657826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_1657826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657826 prefixEnd_1657826 := by exact prefixLift 1657826
  have htrace : WordTrace (prefixWord ++ tailWord_1657826) baseStart_1657826 baseEnd_1657826 := by
    simpa [prefixWord, tailWord_1657826, baseEnd_1657826] using wordTrace_append hprefix tailTrace_1657826
  have hstable : (prefixWord ++ tailWord_1657826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657826).length < 2 ^ (prefixWord ++ tailWord_1657826).sum := by decide
  have hdescent : baseEnd_1657826 < baseStart_1657826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657839 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 1, 7]
def baseStart_1657839 : Nat := 118140960795 + 1657839 * 2 ^ 59
def prefixEnd_1657839 : Nat := 4983230072969 + 3 ^ 40 * 1657839 * 2
def baseEnd_1657839 : Nat := 283756084923081476996081

theorem tailTrace_1657839 : CollatzResearch.WordTrace tailWord_1657839 prefixEnd_1657839 283756084923081476996081 := by
  unfold tailWord_1657839
  simp only [CollatzResearch.WordTrace]
  refine ⟨60466355840939914204672571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40310903893959942803115047 60466355840939914204672571)
  ·
    refine ⟨90699533761409871307008857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60466355840939914204672571 90699533761409871307008857)
    ·
      refine ⟨68024650321057403480256643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90699533761409871307008857 68024650321057403480256643)
      ·
        refine ⟨102036975481586105220384965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68024650321057403480256643 102036975481586105220384965)
        ·
          refine ⟨19131932902797394728822181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102036975481586105220384965 19131932902797394728822181)
          ·
            refine ⟨3587237419274511511654159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19131932902797394728822181 3587237419274511511654159)
            ·
              refine ⟨5380856128911767267481239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587237419274511511654159 5380856128911767267481239)
              ·
                refine ⟨8071284193367650901221859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5380856128911767267481239 8071284193367650901221859)
                ·
                  refine ⟨12106926290051476351832789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8071284193367650901221859 12106926290051476351832789)
                  ·
                    refine ⟨283756084923081476996081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12106926290051476351832789 283756084923081476996081)
                    ·
                      rfl

theorem cell23_1657839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_1657839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657839 prefixEnd_1657839 := by exact prefixLift 1657839
  have htrace : WordTrace (prefixWord ++ tailWord_1657839) baseStart_1657839 baseEnd_1657839 := by
    simpa [prefixWord, tailWord_1657839, baseEnd_1657839] using wordTrace_append hprefix tailTrace_1657839
  have hstable : (prefixWord ++ tailWord_1657839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657839).length < 2 ^ (prefixWord ++ tailWord_1657839).sum := by decide
  have hdescent : baseEnd_1657839 < baseStart_1657839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657854 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1657854 : Nat := 118140960795 + 1657854 * 2 ^ 59
def prefixEnd_1657854 : Nat := 4983230072969 + 3 ^ 40 * 1657854 * 2
def baseEnd_1657854 : Nat := 851275956979061872300675

theorem tailTrace_1657854 : CollatzResearch.WordTrace tailWord_1657854 prefixEnd_1657854 851275956979061872300675 := by
  unfold tailWord_1657854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7558362866985696470808577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40311268623923714510979077 7558362866985696470808577)
  ·
    refine ⟨5668772150239272353106433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7558362866985696470808577 5668772150239272353106433)
    ·
      refine ⟨4251579112679454264829825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5668772150239272353106433 4251579112679454264829825)
      ·
        refine ⟨3188684334509590698622369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4251579112679454264829825 3188684334509590698622369)
        ·
          refine ⟨2391513250882193023966777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3188684334509590698622369 2391513250882193023966777)
          ·
            refine ⟨1793634938161644767975083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391513250882193023966777 1793634938161644767975083)
            ·
              refine ⟨2690452407242467151962625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793634938161644767975083 2690452407242467151962625)
              ·
                refine ⟨2017839305431850363971969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690452407242467151962625 2017839305431850363971969)
                ·
                  refine ⟨1513379479073887772978977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2017839305431850363971969 1513379479073887772978977)
                  ·
                    refine ⟨1135034609305415829734233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1513379479073887772978977 1135034609305415829734233)
                    ·
                      refine ⟨851275956979061872300675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135034609305415829734233 851275956979061872300675)
                      ·
                        rfl

theorem cell23_1657854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1657854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657854 prefixEnd_1657854 := by exact prefixLift 1657854
  have htrace : WordTrace (prefixWord ++ tailWord_1657854) baseStart_1657854 baseEnd_1657854 := by
    simpa [prefixWord, tailWord_1657854, baseEnd_1657854] using wordTrace_append hprefix tailTrace_1657854
  have hstable : (prefixWord ++ tailWord_1657854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657854).length < 2 ^ (prefixWord ++ tailWord_1657854).sum := by decide
  have hdescent : baseEnd_1657854 < baseStart_1657854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657913 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1657913 : Nat := 118140960795 + 1657913 * 2 ^ 59
def prefixEnd_1657913 : Nat := 4983230072969 + 3 ^ 40 * 1657913 * 2
def baseEnd_1657913 : Nat := 851306252337677141462903

theorem tailTrace_1657913 : CollatzResearch.WordTrace tailWord_1657913 prefixEnd_1657913 851306252337677141462903 := by
  unfold tailWord_1657913
  simp only [CollatzResearch.WordTrace]
  refine ⟨60469054842671824842866393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40312703228447883228577595 60469054842671824842866393)
  ·
    refine ⟨45351791132003868632149795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60469054842671824842866393 45351791132003868632149795)
    ·
      refine ⟨68027686698005802948224693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45351791132003868632149795 68027686698005802948224693)
      ·
        refine ⟨6377595627938044026396065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68027686698005802948224693 6377595627938044026396065)
        ·
          refine ⟨4783196720953533019797049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6377595627938044026396065 4783196720953533019797049)
          ·
            refine ⟨3587397540715149764847787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4783196720953533019797049 3587397540715149764847787)
            ·
              refine ⟨5381096311072724647271681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587397540715149764847787 5381096311072724647271681)
              ·
                refine ⟨4035822233304543485453761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5381096311072724647271681 4035822233304543485453761)
                ·
                  refine ⟨3026866674978407614090321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4035822233304543485453761 3026866674978407614090321)
                  ·
                    refine ⟨2270150006233805710567741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3026866674978407614090321 2270150006233805710567741)
                    ·
                      refine ⟨851306252337677141462903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2270150006233805710567741 851306252337677141462903)
                      ·
                        rfl

theorem cell23_1657913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1657913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657913 prefixEnd_1657913 := by exact prefixLift 1657913
  have htrace : WordTrace (prefixWord ++ tailWord_1657913) baseStart_1657913 baseEnd_1657913 := by
    simpa [prefixWord, tailWord_1657913, baseEnd_1657913] using wordTrace_append hprefix tailTrace_1657913
  have hstable : (prefixWord ++ tailWord_1657913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657913).length < 2 ^ (prefixWord ++ tailWord_1657913).sum := by decide
  have hdescent : baseEnd_1657913 < baseStart_1657913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657920 : List Nat := [2, 1, 1, 2, 2, 3, 5, 2, 1, 4]
def baseStart_1657920 : Nat := 118140960795 + 1657920 * 2 ^ 59
def prefixEnd_1657920 : Nat := 4983230072969 + 3 ^ 40 * 1657920 * 2
def baseEnd_1657920 : Nat := 283769948900752871358457

theorem tailTrace_1657920 : CollatzResearch.WordTrace tailWord_1657920 prefixEnd_1657920 283769948900752871358457 := by
  unfold tailWord_1657920
  simp only [CollatzResearch.WordTrace]
  refine ⟨30234655076823232519185607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40312873435764310025580809 30234655076823232519185607)
  ·
    refine ⟨45351982615234848778778411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30234655076823232519185607 45351982615234848778778411)
    ·
      refine ⟨68027973922852273168167617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45351982615234848778778411 68027973922852273168167617)
      ·
        refine ⟨51020980442139204876125713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68027973922852273168167617 51020980442139204876125713)
        ·
          refine ⟨38265735331604403657094285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51020980442139204876125713 38265735331604403657094285)
          ·
            refine ⟨14349650749351651371410357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38265735331604403657094285 14349650749351651371410357)
            ·
              refine ⟨1345279757751717316069721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14349650749351651371410357 1345279757751717316069721)
              ·
                refine ⟨1008959818313787987052291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1345279757751717316069721 1008959818313787987052291)
                ·
                  refine ⟨1513439727470681980578437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008959818313787987052291 1513439727470681980578437)
                  ·
                    refine ⟨283769948900752871358457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1513439727470681980578437 283769948900752871358457)
                    ·
                      rfl

theorem cell23_1657920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 1, 4].length) (baseStart_1657920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657920 prefixEnd_1657920 := by exact prefixLift 1657920
  have htrace : WordTrace (prefixWord ++ tailWord_1657920) baseStart_1657920 baseEnd_1657920 := by
    simpa [prefixWord, tailWord_1657920, baseEnd_1657920] using wordTrace_append hprefix tailTrace_1657920
  have hstable : (prefixWord ++ tailWord_1657920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657920).length < 2 ^ (prefixWord ++ tailWord_1657920).sum := by decide
  have hdescent : baseEnd_1657920 < baseStart_1657920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657933 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 6]
def baseStart_1657933 : Nat := 118140960795 + 1657933 * 2 ^ 59
def prefixEnd_1657933 : Nat := 4983230072969 + 3 ^ 40 * 1657933 * 2
def baseEnd_1657933 : Nat := 94590724661196340356979

theorem tailTrace_1657933 : CollatzResearch.WordTrace tailWord_1657933 prefixEnd_1657933 94590724661196340356979 := by
  unfold tailWord_1657933
  simp only [CollatzResearch.WordTrace]
  refine ⟨60469784302599368258594453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40313189535066245505729635 60469784302599368258594453)
  ·
    refine ⟨2834521139184345387121615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60469784302599368258594453 2834521139184345387121615)
    ·
      refine ⟨4251781708776518080682423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2834521139184345387121615 4251781708776518080682423)
      ·
        refine ⟨6377672563164777121023635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4251781708776518080682423 6377672563164777121023635)
        ·
          refine ⟨9566508844747165681535453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6377672563164777121023635 9566508844747165681535453)
          ·
            refine ⟨3587440816780187130575795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9566508844747165681535453 3587440816780187130575795)
            ·
              refine ⟨5381161225170280695863693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587440816780187130575795 5381161225170280695863693)
              ·
                refine ⟨2017935459438855260948885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5381161225170280695863693 2017935459438855260948885)
                ·
                  refine ⟨94590724661196340356979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2017935459438855260948885 94590724661196340356979)
                  ·
                    rfl

theorem cell23_1657933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_1657933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657933 prefixEnd_1657933 := by exact prefixLift 1657933
  have htrace : WordTrace (prefixWord ++ tailWord_1657933) baseStart_1657933 baseEnd_1657933 := by
    simpa [prefixWord, tailWord_1657933, baseEnd_1657933] using wordTrace_append hprefix tailTrace_1657933
  have hstable : (prefixWord ++ tailWord_1657933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657933).length < 2 ^ (prefixWord ++ tailWord_1657933).sum := by decide
  have hdescent : baseEnd_1657933 < baseStart_1657933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657936 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 3, 5, 2]
def baseStart_1657936 : Nat := 118140960795 + 1657936 * 2 ^ 59
def prefixEnd_1657936 : Nat := 4983230072969 + 3 ^ 40 * 1657936 * 2
def baseEnd_1657936 : Nat := 851318062392730551475297

theorem tailTrace_1657936 : CollatzResearch.WordTrace tailWord_1657936 prefixEnd_1657936 851318062392730551475297 := by
  unfold tailWord_1657936
  simp only [CollatzResearch.WordTrace]
  refine ⟨30234946860794249885476831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40313262481058999847302441 30234946860794249885476831)
  ·
    refine ⟨45352420291191374828215247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30234946860794249885476831 45352420291191374828215247)
    ·
      refine ⟨68028630436787062242322871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45352420291191374828215247 68028630436787062242322871)
      ·
        refine ⟨102042945655180593363484307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68028630436787062242322871 102042945655180593363484307)
        ·
          refine ⟨153064418482770890045226461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102042945655180593363484307 153064418482770890045226461)
          ·
            refine ⟨57399156931039083766959923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153064418482770890045226461 57399156931039083766959923)
            ·
              refine ⟨86098735396558625650439885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57399156931039083766959923 86098735396558625650439885)
              ·
                refine ⟨32287025773709484618914957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86098735396558625650439885 32287025773709484618914957)
                ·
                  refine ⟨12107634665141056732093109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32287025773709484618914957 12107634665141056732093109)
                  ·
                    refine ⟨1135090749856974068633729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12107634665141056732093109 1135090749856974068633729)
                    ·
                      refine ⟨851318062392730551475297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135090749856974068633729 851318062392730551475297)
                      ·
                        rfl

theorem cell23_1657936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 5, 2].length) (baseStart_1657936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657936 prefixEnd_1657936 := by exact prefixLift 1657936
  have htrace : WordTrace (prefixWord ++ tailWord_1657936) baseStart_1657936 baseEnd_1657936 := by
    simpa [prefixWord, tailWord_1657936, baseEnd_1657936] using wordTrace_append hprefix tailTrace_1657936
  have hstable : (prefixWord ++ tailWord_1657936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657936).length < 2 ^ (prefixWord ++ tailWord_1657936).sum := by decide
  have hdescent : baseEnd_1657936 < baseStart_1657936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657946 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 1, 5]
def baseStart_1657946 : Nat := 118140960795 + 1657946 * 2 ^ 59
def prefixEnd_1657946 : Nat := 4983230072969 + 3 ^ 40 * 1657946 * 2
def baseEnd_1657946 : Nat := 283774399066425170783417

theorem tailTrace_1657946 : CollatzResearch.WordTrace tailWord_1657946 prefixEnd_1657946 283774399066425170783417 := by
  unfold tailWord_1657946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15117564612888067869704423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40313505634368180985878461 15117564612888067869704423)
  ·
    refine ⟨22676346919332101804556635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15117564612888067869704423 22676346919332101804556635)
    ·
      refine ⟨34014520378998152706834953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22676346919332101804556635 34014520378998152706834953)
      ·
        refine ⟨25510890284248614530126215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34014520378998152706834953 25510890284248614530126215)
        ·
          refine ⟨38266335426372921795189323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25510890284248614530126215 38266335426372921795189323)
          ·
            refine ⟨57399503139559382692783985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38266335426372921795189323 57399503139559382692783985)
            ·
              refine ⟨43049627354669537019587989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57399503139559382692783985 43049627354669537019587989)
              ·
                refine ⟨2017951282250134547793187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43049627354669537019587989 2017951282250134547793187)
                ·
                  refine ⟨3026926923375201821689781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017951282250134547793187 3026926923375201821689781)
                  ·
                    refine ⟨283774399066425170783417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3026926923375201821689781 283774399066425170783417)
                    ·
                      rfl

theorem cell23_1657946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_1657946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657946 prefixEnd_1657946 := by exact prefixLift 1657946
  have htrace : WordTrace (prefixWord ++ tailWord_1657946) baseStart_1657946 baseEnd_1657946 := by
    simpa [prefixWord, tailWord_1657946, baseEnd_1657946] using wordTrace_append hprefix tailTrace_1657946
  have hstable : (prefixWord ++ tailWord_1657946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657946).length < 2 ^ (prefixWord ++ tailWord_1657946).sum := by decide
  have hdescent : baseEnd_1657946 < baseStart_1657946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657953 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 2, 3, 2]
def baseStart_1657953 : Nat := 118140960795 + 1657953 * 2 ^ 59
def prefixEnd_1657953 : Nat := 4983230072969 + 3 ^ 40 * 1657953 * 2
def baseEnd_1657953 : Nat := 851326791563856984962719

theorem tailTrace_1657953 : CollatzResearch.WordTrace tailWord_1657953 prefixEnd_1657953 851326791563856984962719 := by
  unfold tailWord_1657953
  simp only [CollatzResearch.WordTrace]
  refine ⟨60470513762526911674322513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40313675841684607782881675 60470513762526911674322513)
  ·
    refine ⟨45352885321895183755741885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60470513762526911674322513 45352885321895183755741885)
    ·
      refine ⟨17007331995710693908403207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45352885321895183755741885 17007331995710693908403207)
      ·
        refine ⟨25510997993566040862604811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17007331995710693908403207 25510997993566040862604811)
        ·
          refine ⟨38266496990349061293907217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25510997993566040862604811 38266496990349061293907217)
          ·
            refine ⟨28699872742761795970430413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38266496990349061293907217 28699872742761795970430413)
            ·
              refine ⟨10762452278535673488911405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28699872742761795970430413 10762452278535673488911405)
              ·
                refine ⟨4035919604450877558341777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10762452278535673488911405 4035919604450877558341777)
                ·
                  refine ⟨3026939703338158168756333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4035919604450877558341777 3026939703338158168756333)
                  ·
                    refine ⟨1135102388751809313283625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3026939703338158168756333 1135102388751809313283625)
                    ·
                      refine ⟨851326791563856984962719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135102388751809313283625 851326791563856984962719)
                      ·
                        rfl

theorem cell23_1657953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_1657953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657953 prefixEnd_1657953 := by exact prefixLift 1657953
  have htrace : WordTrace (prefixWord ++ tailWord_1657953) baseStart_1657953 baseEnd_1657953 := by
    simpa [prefixWord, tailWord_1657953, baseEnd_1657953] using wordTrace_append hprefix tailTrace_1657953
  have hstable : (prefixWord ++ tailWord_1657953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657953).length < 2 ^ (prefixWord ++ tailWord_1657953).sum := by decide
  have hdescent : baseEnd_1657953 < baseStart_1657953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657976 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 4, 4]
def baseStart_1657976 : Nat := 118140960795 + 1657976 * 2 ^ 59
def prefixEnd_1657976 : Nat := 4983230072969 + 3 ^ 40 * 1657976 * 2
def baseEnd_1657976 : Nat := 283779533872970131658371

theorem tailTrace_1657976 : CollatzResearch.WordTrace tailWord_1657976 prefixEnd_1657976 283779533872970131658371 := by
  unfold tailWord_1657976
  simp only [CollatzResearch.WordTrace]
  refine ⟨30235676320721793301204891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40314235094295724401606521 30235676320721793301204891)
  ·
    refine ⟨45353514481082689951807337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30235676320721793301204891 45353514481082689951807337)
    ·
      refine ⟨34015135860812017463855503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45353514481082689951807337 34015135860812017463855503)
      ·
        refine ⟨51022703791218026195783255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34015135860812017463855503 51022703791218026195783255)
        ·
          refine ⟨76534055686827039293674883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51022703791218026195783255 76534055686827039293674883)
          ·
            refine ⟨114801083530240558940512325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76534055686827039293674883 114801083530240558940512325)
            ·
              refine ⟨21525203161920104801346061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114801083530240558940512325 21525203161920104801346061)
              ·
                refine ⟨8071951185720039300504773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21525203161920104801346061 8071951185720039300504773)
                ·
                  refine ⟨1513490847322507368844645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8071951185720039300504773 1513490847322507368844645)
                  ·
                    refine ⟨283779533872970131658371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1513490847322507368844645 283779533872970131658371)
                    ·
                      rfl

theorem cell23_1657976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_1657976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657976 prefixEnd_1657976 := by exact prefixLift 1657976
  have htrace : WordTrace (prefixWord ++ tailWord_1657976) baseStart_1657976 baseEnd_1657976 := by
    simpa [prefixWord, tailWord_1657976, baseEnd_1657976] using wordTrace_append hprefix tailTrace_1657976
  have hstable : (prefixWord ++ tailWord_1657976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657976).length < 2 ^ (prefixWord ++ tailWord_1657976).sum := by decide
  have hdescent : baseEnd_1657976 < baseStart_1657976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657977 : List Nat := [1, 2, 1, 3, 5, 1, 1, 4, 1, 1, 3]
def baseStart_1657977 : Nat := 118140960795 + 1657977 * 2 ^ 59
def prefixEnd_1657977 : Nat := 4983230072969 + 3 ^ 40 * 1657977 * 2
def baseEnd_1657977 : Nat := 851339115099564891062609

theorem tailTrace_1657977 : CollatzResearch.WordTrace tailWord_1657977 prefixEnd_1657977 851339115099564891062609 := by
  unfold tailWord_1657977
  simp only [CollatzResearch.WordTrace]
  refine ⟨60471389114439963773196185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40314259409626642515464123 60471389114439963773196185)
  ·
    refine ⟨45353541835829972829897139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60471389114439963773196185 45353541835829972829897139)
    ·
      refine ⟨68030312753744959244845709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45353541835829972829897139 68030312753744959244845709)
      ·
        refine ⟨25511367282654359716817141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68030312753744959244845709 25511367282654359716817141)
        ·
          refine ⟨2391690682748846223451607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25511367282654359716817141 2391690682748846223451607)
          ·
            refine ⟨3587536024123269335177411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391690682748846223451607 3587536024123269335177411)
            ·
              refine ⟨5381304036184904002766117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587536024123269335177411 5381304036184904002766117)
              ·
                refine ⟨1008994506784669500518647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5381304036184904002766117 1008994506784669500518647)
                ·
                  refine ⟨1513491760177004250777971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008994506784669500518647 1513491760177004250777971)
                  ·
                    refine ⟨2270237640265506376166957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1513491760177004250777971 2270237640265506376166957)
                    ·
                      refine ⟨851339115099564891062609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2270237640265506376166957 851339115099564891062609)
                      ·
                        rfl

theorem cell23_1657977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_1657977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657977 prefixEnd_1657977 := by exact prefixLift 1657977
  have htrace : WordTrace (prefixWord ++ tailWord_1657977) baseStart_1657977 baseEnd_1657977 := by
    simpa [prefixWord, tailWord_1657977, baseEnd_1657977] using wordTrace_append hprefix tailTrace_1657977
  have hstable : (prefixWord ++ tailWord_1657977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657977).length < 2 ^ (prefixWord ++ tailWord_1657977).sum := by decide
  have hdescent : baseEnd_1657977 < baseStart_1657977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657979 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 6]
def baseStart_1657979 : Nat := 118140960795 + 1657979 * 2 ^ 59
def prefixEnd_1657979 : Nat := 4983230072969 + 3 ^ 40 * 1657979 * 2
def baseEnd_1657979 : Nat := 851340142060873883237599

theorem tailTrace_1657979 : CollatzResearch.WordTrace tailWord_1657979 prefixEnd_1657979 851340142060873883237599 := by
  unfold tailWord_1657979
  simp only [CollatzResearch.WordTrace]
  refine ⟨60471462060432718114768991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40314308040288478743179327 60471462060432718114768991)
  ·
    refine ⟨90707193090649077172153487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60471462060432718114768991 90707193090649077172153487)
    ·
      refine ⟨136060789635973615758230231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90707193090649077172153487 136060789635973615758230231)
      ·
        refine ⟨204091184453960423637345347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136060789635973615758230231 204091184453960423637345347)
        ·
          refine ⟨306136776680940635456018021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204091184453960423637345347 306136776680940635456018021)
          ·
            refine ⟨57400645627676369148003379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306136776680940635456018021 57400645627676369148003379)
            ·
              refine ⟨86100968441514553722005069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57400645627676369148003379 86100968441514553722005069)
              ·
                refine ⟨32287863165567957645751901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86100968441514553722005069 32287863165567957645751901)
                ·
                  refine ⟨12107948687087984117156963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32287863165567957645751901 12107948687087984117156963)
                  ·
                    refine ⟨18161923030631976175735445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12107948687087984117156963 18161923030631976175735445)
                    ·
                      refine ⟨851340142060873883237599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18161923030631976175735445 851340142060873883237599)
                      ·
                        rfl

theorem cell23_1657979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_1657979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657979 prefixEnd_1657979 := by exact prefixLift 1657979
  have htrace : WordTrace (prefixWord ++ tailWord_1657979) baseStart_1657979 baseEnd_1657979 := by
    simpa [prefixWord, tailWord_1657979, baseEnd_1657979] using wordTrace_append hprefix tailTrace_1657979
  have hstable : (prefixWord ++ tailWord_1657979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657979).length < 2 ^ (prefixWord ++ tailWord_1657979).sum := by decide
  have hdescent : baseEnd_1657979 < baseStart_1657979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657983 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 9, 2, 2]
def baseStart_1657983 : Nat := 118140960795 + 1657983 * 2 ^ 59
def prefixEnd_1657983 : Nat := 4983230072969 + 3 ^ 40 * 1657983 * 2
def baseEnd_1657983 : Nat := 851342195983491867587581

theorem tailTrace_1657983 : CollatzResearch.WordTrace tailWord_1657983 prefixEnd_1657983 851342195983491867587581 := by
  unfold tailWord_1657983
  simp only [CollatzResearch.WordTrace]
  refine ⟨60471607952418226797914603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40314405301612151198609735 60471607952418226797914603)
  ·
    refine ⟨90707411928627340196871905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60471607952418226797914603 90707411928627340196871905)
    ·
      refine ⟨68030558946470505147653929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90707411928627340196871905 68030558946470505147653929)
      ·
        refine ⟨51022919209852878860740447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68030558946470505147653929 51022919209852878860740447)
        ·
          refine ⟨76534378814779318291110671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51022919209852878860740447 76534378814779318291110671)
          ·
            refine ⟨114801568222168977436666007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76534378814779318291110671 114801568222168977436666007)
            ·
              refine ⟨172202352333253466154999011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114801568222168977436666007 172202352333253466154999011)
              ·
                refine ⟨258303528499880199232498517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172202352333253466154999011 258303528499880199232498517)
                ·
                  refine ⟨1513497237303985542377921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 258303528499880199232498517 1513497237303985542377921)
                  ·
                    refine ⟨1135122927977989156783441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1513497237303985542377921 1135122927977989156783441)
                    ·
                      refine ⟨851342195983491867587581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135122927977989156783441 851342195983491867587581)
                      ·
                        rfl

theorem cell23_1657983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 2, 2].length) (baseStart_1657983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657983 prefixEnd_1657983 := by exact prefixLift 1657983
  have htrace : WordTrace (prefixWord ++ tailWord_1657983) baseStart_1657983 baseEnd_1657983 := by
    simpa [prefixWord, tailWord_1657983, baseEnd_1657983] using wordTrace_append hprefix tailTrace_1657983
  have hstable : (prefixWord ++ tailWord_1657983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657983).length < 2 ^ (prefixWord ++ tailWord_1657983).sum := by decide
  have hdescent : baseEnd_1657983 < baseStart_1657983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657993 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 2, 4]
def baseStart_1657993 : Nat := 118140960795 + 1657993 * 2 ^ 59
def prefixEnd_1657993 : Nat := 4983230072969 + 3 ^ 40 * 1657993 * 2
def baseEnd_1657993 : Nat := 283782443596678942820845

theorem tailTrace_1657993 : CollatzResearch.WordTrace tailWord_1657993 prefixEnd_1657993 283782443596678942820845 := by
  unfold tailWord_1657993
  simp only [CollatzResearch.WordTrace]
  refine ⟨60471972682381998505778633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40314648454921332337185755 60471972682381998505778633)
  ·
    refine ⟨45353979511786498879333975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60471972682381998505778633 45353979511786498879333975)
    ·
      refine ⟨68030969267679748319000963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45353979511786498879333975 68030969267679748319000963)
      ·
        refine ⟨102046453901519622478501445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68030969267679748319000963 102046453901519622478501445)
        ·
          refine ⟨19133710106534929214719021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102046453901519622478501445 19133710106534929214719021)
          ·
            refine ⟨7175141289950598455519633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19133710106534929214719021 7175141289950598455519633)
            ·
              refine ⟨5381355967462948841639725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7175141289950598455519633 5381355967462948841639725)
              ·
                refine ⟨2018008487798605815614897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5381355967462948841639725 2018008487798605815614897)
                ·
                  refine ⟨1513506365848954361711173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2018008487798605815614897 1513506365848954361711173)
                  ·
                    refine ⟨283782443596678942820845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1513506365848954361711173 283782443596678942820845)
                    ·
                      rfl

theorem cell23_1657993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 4].length) (baseStart_1657993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1657993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1657993 prefixEnd_1657993 := by exact prefixLift 1657993
  have htrace : WordTrace (prefixWord ++ tailWord_1657993) baseStart_1657993 baseEnd_1657993 := by
    simpa [prefixWord, tailWord_1657993, baseEnd_1657993] using wordTrace_append hprefix tailTrace_1657993
  have hstable : (prefixWord ++ tailWord_1657993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657993).length < 2 ^ (prefixWord ++ tailWord_1657993).sum := by decide
  have hdescent : baseEnd_1657993 < baseStart_1657993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658020 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_1658020 : Nat := 118140960795 + 1658020 * 2 ^ 59
def prefixEnd_1658020 : Nat := 4983230072969 + 3 ^ 40 * 1658020 * 2
def baseEnd_1658020 : Nat := 851361194767708222824911

theorem tailTrace_1658020 : CollatzResearch.WordTrace tailWord_1658020 prefixEnd_1658020 851361194767708222824911 := by
  unfold tailWord_1658020
  simp only [CollatzResearch.WordTrace]
  refine ⟨30236478726642091058505757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40315304968856121411341009 30236478726642091058505757)
  ·
    refine ⟨11338679522490784146939659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30236478726642091058505757 11338679522490784146939659)
    ·
      refine ⟨17008019283736176220409489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11338679522490784146939659 17008019283736176220409489)
      ·
        refine ⟨12756014462802132165307117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17008019283736176220409489 12756014462802132165307117)
        ·
          refine ⟨4783505423550799561990169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12756014462802132165307117 4783505423550799561990169)
          ·
            refine ⟨3587629067663099671492627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4783505423550799561990169 3587629067663099671492627)
            ·
              refine ⟨5381443601494649507238941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587629067663099671492627 5381443601494649507238941)
              ·
                refine ⟨2018041350560493565214603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5381443601494649507238941 2018041350560493565214603)
                ·
                  refine ⟨3027062025840740347821905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018041350560493565214603 3027062025840740347821905)
                  ·
                    refine ⟨2270296519380555260866429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3027062025840740347821905 2270296519380555260866429)
                    ·
                      refine ⟨851361194767708222824911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2270296519380555260866429 851361194767708222824911)
                      ·
                        rfl

theorem cell23_1658020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_1658020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658020 prefixEnd_1658020 := by exact prefixLift 1658020
  have htrace : WordTrace (prefixWord ++ tailWord_1658020) baseStart_1658020 baseEnd_1658020 := by
    simpa [prefixWord, tailWord_1658020, baseEnd_1658020] using wordTrace_append hprefix tailTrace_1658020
  have hstable : (prefixWord ++ tailWord_1658020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658020).length < 2 ^ (prefixWord ++ tailWord_1658020).sum := by decide
  have hdescent : baseEnd_1658020 < baseStart_1658020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658043 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 3, 3, 2]
def baseStart_1658043 : Nat := 118140960795 + 1658043 * 2 ^ 59
def prefixEnd_1658043 : Nat := 4983230072969 + 3 ^ 40 * 1658043 * 2
def baseEnd_1658043 : Nat := 851373004822761632837305

theorem tailTrace_1658043 : CollatzResearch.WordTrace tailWord_1658043 prefixEnd_1658043 851373004822761632837305 := by
  unfold tailWord_1658043
  simp only [CollatzResearch.WordTrace]
  refine ⟨60473796332200857045098783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40315864221467238030065855 60473796332200857045098783)
  ·
    refine ⟨90710694498301285567648175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60473796332200857045098783 90710694498301285567648175)
    ·
      refine ⟨136066041747451928351472263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90710694498301285567648175 136066041747451928351472263)
      ·
        refine ⟨204099062621177892527208395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136066041747451928351472263 204099062621177892527208395)
        ·
          refine ⟨306148593931766838790812593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204099062621177892527208395 306148593931766838790812593)
          ·
            refine ⟨229611445448825129093109445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306148593931766838790812593 229611445448825129093109445)
            ·
              refine ⟨43052146021654711704958021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229611445448825129093109445 43052146021654711704958021)
              ·
                refine ⟨8072277379060258444679629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43052146021654711704958021 8072277379060258444679629)
                ·
                  refine ⟨3027104017147596916754861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8072277379060258444679629 3027104017147596916754861)
                  ·
                    refine ⟨1135164006430348843783073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3027104017147596916754861 1135164006430348843783073)
                    ·
                      refine ⟨851373004822761632837305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135164006430348843783073 851373004822761632837305)
                      ·
                        rfl

theorem cell23_1658043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 3, 2].length) (baseStart_1658043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658043 prefixEnd_1658043 := by exact prefixLift 1658043
  have htrace : WordTrace (prefixWord ++ tailWord_1658043) baseStart_1658043 baseEnd_1658043 := by
    simpa [prefixWord, tailWord_1658043, baseEnd_1658043] using wordTrace_append hprefix tailTrace_1658043
  have hstable : (prefixWord ++ tailWord_1658043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658043).length < 2 ^ (prefixWord ++ tailWord_1658043).sum := by decide
  have hdescent : baseEnd_1658043 < baseStart_1658043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658056 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_1658056 : Nat := 118140960795 + 1658056 * 2 ^ 59
def prefixEnd_1658056 : Nat := 4983230072969 + 3 ^ 40 * 1658056 * 2
def baseEnd_1658056 : Nat := 851379680071270081974745

theorem tailTrace_1658056 : CollatzResearch.WordTrace tailWord_1658056 prefixEnd_1658056 851379680071270081974745 := by
  unfold tailWord_1658056
  simp only [CollatzResearch.WordTrace]
  refine ⟨30237135240576880132661011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40316180320769173510214681 30237135240576880132661011)
  ·
    refine ⟨45355702860865320198991517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30237135240576880132661011 45355702860865320198991517)
    ·
      refine ⟨17008388572824495074621819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45355702860865320198991517 17008388572824495074621819)
      ·
        refine ⟨25512582859236742611932729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17008388572824495074621819 25512582859236742611932729)
        ·
          refine ⟨19134437144427556958949547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25512582859236742611932729 19134437144427556958949547)
          ·
            refine ⟨28701655716641335438424321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19134437144427556958949547 28701655716641335438424321)
            ·
              refine ⟨21526241787481001578818241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28701655716641335438424321 21526241787481001578818241)
              ·
                refine ⟨16144681340610751184113681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21526241787481001578818241 16144681340610751184113681)
                ·
                  refine ⟨12108511005458063388085261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16144681340610751184113681 12108511005458063388085261)
                  ·
                    refine ⟨4540691627046773770531973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12108511005458063388085261 4540691627046773770531973)
                    ·
                      refine ⟨851379680071270081974745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4540691627046773770531973 851379680071270081974745)
                      ·
                        rfl

theorem cell23_1658056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_1658056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658056 prefixEnd_1658056 := by exact prefixLift 1658056
  have htrace : WordTrace (prefixWord ++ tailWord_1658056) baseStart_1658056 baseEnd_1658056 := by
    simpa [prefixWord, tailWord_1658056, baseEnd_1658056] using wordTrace_append hprefix tailTrace_1658056
  have hstable : (prefixWord ++ tailWord_1658056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658056).length < 2 ^ (prefixWord ++ tailWord_1658056).sum := by decide
  have hdescent : baseEnd_1658056 < baseStart_1658056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658068 : List Nat := [2, 4, 1, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1658068 : Nat := 118140960795 + 1658068 * 2 ^ 59
def prefixEnd_1658068 : Nat := 4983230072969 + 3 ^ 40 * 1658068 * 2
def baseEnd_1658068 : Nat := 851385841839124035024691

theorem tailTrace_1658068 : CollatzResearch.WordTrace tailWord_1658068 prefixEnd_1658068 851385841839124035024691 := by
  unfold tailWord_1658068
  simp only [CollatzResearch.WordTrace]
  refine ⟨30237354078555143157379429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40316472104740190876505905 30237354078555143157379429)
  ·
    refine ⟨5669503889729089342008643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30237354078555143157379429 5669503889729089342008643)
    ·
      refine ⟨8504255834593634013012965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5669503889729089342008643 8504255834593634013012965)
      ·
        refine ⟨1594547968986306377439931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8504255834593634013012965 1594547968986306377439931)
        ·
          refine ⟨2391821953479459566159897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594547968986306377439931 2391821953479459566159897)
          ·
            refine ⟨1793866465109594674619923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391821953479459566159897 1793866465109594674619923)
            ·
              refine ⟨2690799697664392011929885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793866465109594674619923 2690799697664392011929885)
              ·
                refine ⟨1009049886624147004473707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2690799697664392011929885 1009049886624147004473707)
                ·
                  refine ⟨1513574829936220506710561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009049886624147004473707 1513574829936220506710561)
                  ·
                    refine ⟨1135181122452165380032921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1513574829936220506710561 1135181122452165380032921)
                    ·
                      refine ⟨851385841839124035024691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135181122452165380032921 851385841839124035024691)
                      ·
                        rfl

theorem cell23_1658068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1658068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658068 prefixEnd_1658068 := by exact prefixLift 1658068
  have htrace : WordTrace (prefixWord ++ tailWord_1658068) baseStart_1658068 baseEnd_1658068 := by
    simpa [prefixWord, tailWord_1658068, baseEnd_1658068] using wordTrace_append hprefix tailTrace_1658068
  have hstable : (prefixWord ++ tailWord_1658068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658068).length < 2 ^ (prefixWord ++ tailWord_1658068).sum := by decide
  have hdescent : baseEnd_1658068 < baseStart_1658068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658073 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 3, 4, 2]
def baseStart_1658073 : Nat := 118140960795 + 1658073 * 2 ^ 59
def prefixEnd_1658073 : Nat := 4983230072969 + 3 ^ 40 * 1658073 * 2
def baseEnd_1658073 : Nat := 851388409242396515462167

theorem tailTrace_1658073 : CollatzResearch.WordTrace tailWord_1658073 prefixEnd_1658073 851388409242396515462167 := by
  unfold tailWord_1658073
  simp only [CollatzResearch.WordTrace]
  refine ⟨60474890522092172168690873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40316593681394781445793915 60474890522092172168690873)
  ·
    refine ⟨45356167891569129126518155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60474890522092172168690873 45356167891569129126518155)
    ·
      refine ⟨68034251837353693689777233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45356167891569129126518155 68034251837353693689777233)
      ·
        refine ⟨51025688878015270267332925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68034251837353693689777233 51025688878015270267332925)
        ·
          refine ⟨19134633329255726350249847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51025688878015270267332925 19134633329255726350249847)
          ·
            refine ⟨28701949993883589525374771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19134633329255726350249847 28701949993883589525374771)
            ·
              refine ⟨43052924990825384288062157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28701949993883589525374771 43052924990825384288062157)
              ·
                refine ⟨16144846871559519108023309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43052924990825384288062157 16144846871559519108023309)
                ·
                  refine ⟨6054317576834819665508741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16144846871559519108023309 6054317576834819665508741)
                  ·
                    refine ⟨1135184545656528687282889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6054317576834819665508741 1135184545656528687282889)
                    ·
                      refine ⟨851388409242396515462167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135184545656528687282889 851388409242396515462167)
                      ·
                        rfl

theorem cell23_1658073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 4, 2].length) (baseStart_1658073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658073 prefixEnd_1658073 := by exact prefixLift 1658073
  have htrace : WordTrace (prefixWord ++ tailWord_1658073) baseStart_1658073 baseEnd_1658073 := by
    simpa [prefixWord, tailWord_1658073, baseEnd_1658073] using wordTrace_append hprefix tailTrace_1658073
  have hstable : (prefixWord ++ tailWord_1658073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658073).length < 2 ^ (prefixWord ++ tailWord_1658073).sum := by decide
  have hdescent : baseEnd_1658073 < baseStart_1658073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658147 : List Nat := [1, 1, 1, 4, 2, 5, 2, 2, 5]
def baseStart_1658147 : Nat := 118140960795 + 1658147 * 2 ^ 59
def prefixEnd_1658147 : Nat := 4983230072969 + 3 ^ 40 * 1658147 * 2
def baseEnd_1658147 : Nat := 94602934090092136215203

theorem tailTrace_1658147 : CollatzResearch.WordTrace tailWord_1658147 prefixEnd_1658147 94602934090092136215203 := by
  unfold tailWord_1658147
  simp only [CollatzResearch.WordTrace]
  refine ⟨60477589523824082806884695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40318393015882721871256463 60477589523824082806884695)
  ·
    refine ⟨90716384285736124210327043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60477589523824082806884695 90716384285736124210327043)
    ·
      refine ⟨136074576428604186315490565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90716384285736124210327043 136074576428604186315490565)
      ·
        refine ⟨25513983080363284934154481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136074576428604186315490565 25513983080363284934154481)
        ·
          refine ⟨19135487310272463700615861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25513983080363284934154481 19135487310272463700615861)
          ·
            refine ⟨1793951935338043471932737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19135487310272463700615861 1793951935338043471932737)
            ·
              refine ⟨1345463951503532603949553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793951935338043471932737 1345463951503532603949553)
              ·
                refine ⟨1009097963627649452962165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1345463951503532603949553 1009097963627649452962165)
                ·
                  refine ⟨94602934090092136215203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1009097963627649452962165 94602934090092136215203)
                  ·
                    rfl

theorem cell23_1658147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 5].length) (baseStart_1658147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658147 prefixEnd_1658147 := by exact prefixLift 1658147
  have htrace : WordTrace (prefixWord ++ tailWord_1658147) baseStart_1658147 baseEnd_1658147 := by
    simpa [prefixWord, tailWord_1658147, baseEnd_1658147] using wordTrace_append hprefix tailTrace_1658147
  have hstable : (prefixWord ++ tailWord_1658147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658147).length < 2 ^ (prefixWord ++ tailWord_1658147).sum := by decide
  have hdescent : baseEnd_1658147 < baseStart_1658147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658156 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_1658156 : Nat := 118140960795 + 1658156 * 2 ^ 59
def prefixEnd_1658156 : Nat := 4983230072969 + 3 ^ 40 * 1658156 * 2
def baseEnd_1658156 : Nat := 283810342712239896908095

theorem tailTrace_1658156 : CollatzResearch.WordTrace tailWord_1658156 prefixEnd_1658156 283810342712239896908095 := by
  unfold tailWord_1658156
  simp only [CollatzResearch.WordTrace]
  refine ⟨30238958890395738671981161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40318611853860984895974881 30238958890395738671981161)
  ·
    refine ⟨22679219167796804003985871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30238958890395738671981161 22679219167796804003985871)
    ·
      refine ⟨34018828751695206005978807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22679219167796804003985871 34018828751695206005978807)
      ·
        refine ⟨51028243127542809008968211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34018828751695206005978807 51028243127542809008968211)
        ·
          refine ⟨76542364691314213513452317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51028243127542809008968211 76542364691314213513452317)
          ·
            refine ⟨28703386759242830067544619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76542364691314213513452317 28703386759242830067544619)
            ·
              refine ⟨43055080138864245101316929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28703386759242830067544619 43055080138864245101316929)
              ·
                refine ⟨32291310104148183825987697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43055080138864245101316929 32291310104148183825987697)
                ·
                  refine ⟨24218482578111137869490773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32291310104148183825987697 24218482578111137869490773)
                  ·
                    refine ⟨283810342712239896908095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24218482578111137869490773 283810342712239896908095)
                    ·
                      rfl

theorem cell23_1658156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_1658156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658156 prefixEnd_1658156 := by exact prefixLift 1658156
  have htrace : WordTrace (prefixWord ++ tailWord_1658156) baseStart_1658156 baseEnd_1658156 := by
    simpa [prefixWord, tailWord_1658156, baseEnd_1658156] using wordTrace_append hprefix tailTrace_1658156
  have hstable : (prefixWord ++ tailWord_1658156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658156).length < 2 ^ (prefixWord ++ tailWord_1658156).sum := by decide
  have hdescent : baseEnd_1658156 < baseStart_1658156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658157 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1658157 : Nat := 118140960795 + 1658157 * 2 ^ 59
def prefixEnd_1658157 : Nat := 4983230072969 + 3 ^ 40 * 1658157 * 2
def baseEnd_1658157 : Nat := 851431541617374186811781

theorem tailTrace_1658157 : CollatzResearch.WordTrace tailWord_1658157 prefixEnd_1658157 851431541617374186811781 := by
  unfold tailWord_1658157
  simp only [CollatzResearch.WordTrace]
  refine ⟨60477954253787854514748725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40318636169191903009832483 60477954253787854514748725)
  ·
    refine ⟨5669808211292611360757693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60477954253787854514748725 5669808211292611360757693)
    ·
      refine ⟨2126178079234729260284135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5669808211292611360757693 2126178079234729260284135)
      ·
        refine ⟨3189267118852093890426203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126178079234729260284135 3189267118852093890426203)
        ·
          refine ⟨4783900678278140835639305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3189267118852093890426203 4783900678278140835639305)
          ·
            refine ⟨3587925508708605626729479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4783900678278140835639305 3587925508708605626729479)
            ·
              refine ⟨5381888263062908440094219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587925508708605626729479 5381888263062908440094219)
              ·
                refine ⟨8072832394594362660141329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381888263062908440094219 8072832394594362660141329)
                ·
                  refine ⟨6054624295945771995105997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8072832394594362660141329 6054624295945771995105997)
                  ·
                    refine ⟨2270484110979664498164749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6054624295945771995105997 2270484110979664498164749)
                    ·
                      refine ⟨851431541617374186811781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2270484110979664498164749 851431541617374186811781)
                      ·
                        rfl

theorem cell23_1658157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1658157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658157 prefixEnd_1658157 := by exact prefixLift 1658157
  have htrace : WordTrace (prefixWord ++ tailWord_1658157) baseStart_1658157 baseEnd_1658157 := by
    simpa [prefixWord, tailWord_1658157, baseEnd_1658157] using wordTrace_append hprefix tailTrace_1658157
  have hstable : (prefixWord ++ tailWord_1658157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658157).length < 2 ^ (prefixWord ++ tailWord_1658157).sum := by decide
  have hdescent : baseEnd_1658157 < baseStart_1658157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658177 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1658177 : Nat := 118140960795 + 1658177 * 2 ^ 59
def prefixEnd_1658177 : Nat := 4983230072969 + 3 ^ 40 * 1658177 * 2
def baseEnd_1658177 : Nat := 283813937076821369520563

theorem tailTrace_1658177 : CollatzResearch.WordTrace tailWord_1658177 prefixEnd_1658177 283813937076821369520563 := by
  unfold tailWord_1658177
  simp only [CollatzResearch.WordTrace]
  refine ⟨60478683713715397930476785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40319122475810265286984523 60478683713715397930476785)
  ·
    refine ⟨45359012785286548447857589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60478683713715397930476785 45359012785286548447857589)
    ·
      refine ⟨4252407448620613916986649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45359012785286548447857589 4252407448620613916986649)
      ·
        refine ⟨3189305586465460437739987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4252407448620613916986649 3189305586465460437739987)
        ·
          refine ⟨4783958379698190656609981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3189305586465460437739987 4783958379698190656609981)
          ·
            refine ⟨1793984392386821496228743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4783958379698190656609981 1793984392386821496228743)
            ·
              refine ⟨2690976588580232244343115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793984392386821496228743 2690976588580232244343115)
              ·
                refine ⟨4036464882870348366514673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2690976588580232244343115 4036464882870348366514673)
                ·
                  refine ⟨3027348662152761274886005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4036464882870348366514673 3027348662152761274886005)
                  ·
                    refine ⟨283813937076821369520563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3027348662152761274886005 283813937076821369520563)
                    ·
                      rfl

theorem cell23_1658177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1658177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658177 prefixEnd_1658177 := by exact prefixLift 1658177
  have htrace : WordTrace (prefixWord ++ tailWord_1658177) baseStart_1658177 baseEnd_1658177 := by
    simpa [prefixWord, tailWord_1658177, baseEnd_1658177] using wordTrace_append hprefix tailTrace_1658177
  have hstable : (prefixWord ++ tailWord_1658177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658177).length < 2 ^ (prefixWord ++ tailWord_1658177).sum := by decide
  have hdescent : baseEnd_1658177 < baseStart_1658177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658233 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 3, 5]
def baseStart_1658233 : Nat := 118140960795 + 1658233 * 2 ^ 59
def prefixEnd_1658233 : Nat := 4983230072969 + 3 ^ 40 * 1658233 * 2
def baseEnd_1658233 : Nat := 283823522049038629820477

theorem tailTrace_1658233 : CollatzResearch.WordTrace tailWord_1658233 prefixEnd_1658233 283823522049038629820477 := by
  unfold tailWord_1658233
  simp only [CollatzResearch.WordTrace]
  refine ⟨60480726201512519494515353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40320484134341679663010235 60480726201512519494515353)
  ·
    refine ⟨45360544651134389620886515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60480726201512519494515353 45360544651134389620886515)
    ·
      refine ⟨68040816976701584431329773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45360544651134389620886515 68040816976701584431329773)
      ·
        refine ⟨25515306366263094161748665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68040816976701584431329773 25515306366263094161748665)
        ·
          refine ⟨19136479774697320621311499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25515306366263094161748665 19136479774697320621311499)
          ·
            refine ⟨28704719662045980931967249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19136479774697320621311499 28704719662045980931967249)
            ·
              refine ⟨21528539746534485698975437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28704719662045980931967249 21528539746534485698975437)
              ·
                refine ⟨8073202404950432137115789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21528539746534485698975437 8073202404950432137115789)
                ·
                  refine ⟨3027450901856412051418421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8073202404950432137115789 3027450901856412051418421)
                  ·
                    refine ⟨283823522049038629820477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3027450901856412051418421 283823522049038629820477)
                    ·
                      rfl

theorem cell23_1658233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_1658233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658233 prefixEnd_1658233 := by exact prefixLift 1658233
  have htrace : WordTrace (prefixWord ++ tailWord_1658233) baseStart_1658233 baseEnd_1658233 := by
    simpa [prefixWord, tailWord_1658233, baseEnd_1658233] using wordTrace_append hprefix tailTrace_1658233
  have hstable : (prefixWord ++ tailWord_1658233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658233).length < 2 ^ (prefixWord ++ tailWord_1658233).sum := by decide
  have hdescent : baseEnd_1658233 < baseStart_1658233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658240 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 6, 3, 2]
def baseStart_1658240 : Nat := 118140960795 + 1658240 * 2 ^ 59
def prefixEnd_1658240 : Nat := 4983230072969 + 3 ^ 40 * 1658240 * 2
def baseEnd_1658240 : Nat := 851474160511697362073899

theorem tailTrace_1658240 : CollatzResearch.WordTrace tailWord_1658240 prefixEnd_1658240 851474160511697362073899 := by
  unfold tailWord_1658240
  simp only [CollatzResearch.WordTrace]
  refine ⟨30240490756243579845010087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40320654341658106460013449 30240490756243579845010087)
  ·
    refine ⟨45360736134365369767515131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30240490756243579845010087 45360736134365369767515131)
    ·
      refine ⟨68041104201548054651272697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45360736134365369767515131 68041104201548054651272697)
      ·
        refine ⟨51030828151161040988454523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68041104201548054651272697 51030828151161040988454523)
        ·
          refine ⟨76546242226741561482681785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51030828151161040988454523 76546242226741561482681785)
          ·
            refine ⟨57409681670056171112011339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76546242226741561482681785 57409681670056171112011339)
            ·
              refine ⟨86114522505084256668017009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57409681670056171112011339 86114522505084256668017009)
              ·
                refine ⟨64585891878813192501012757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86114522505084256668017009 64585891878813192501012757)
                ·
                  refine ⟨3027463681819368398484973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64585891878813192501012757 3027463681819368398484973)
                  ·
                    refine ⟨1135298880682263149431865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3027463681819368398484973 1135298880682263149431865)
                    ·
                      refine ⟨851474160511697362073899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135298880682263149431865 851474160511697362073899)
                      ·
                        rfl

theorem cell23_1658240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 3, 2].length) (baseStart_1658240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658240 prefixEnd_1658240 := by exact prefixLift 1658240
  have htrace : WordTrace (prefixWord ++ tailWord_1658240) baseStart_1658240 baseEnd_1658240 := by
    simpa [prefixWord, tailWord_1658240, baseEnd_1658240] using wordTrace_append hprefix tailTrace_1658240
  have hstable : (prefixWord ++ tailWord_1658240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658240).length < 2 ^ (prefixWord ++ tailWord_1658240).sum := by decide
  have hdescent : baseEnd_1658240 < baseStart_1658240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658241 : List Nat := [1, 2, 4, 3, 2, 2, 1, 3, 1, 4]
def baseStart_1658241 : Nat := 118140960795 + 1658241 * 2 ^ 59
def prefixEnd_1658241 : Nat := 4983230072969 + 3 ^ 40 * 1658241 * 2
def baseEnd_1658241 : Nat := 283824891330783952720465

theorem tailTrace_1658241 : CollatzResearch.WordTrace tailWord_1658241 prefixEnd_1658241 283824891330783952720465 := by
  unfold tailWord_1658241
  simp only [CollatzResearch.WordTrace]
  refine ⟨60481017985483536860806577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40320678656989024573871051 60481017985483536860806577)
  ·
    refine ⟨45360763489112652645604933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60481017985483536860806577 45360763489112652645604933)
    ·
      refine ⟨8505143154208622371050925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45360763489112652645604933 8505143154208622371050925)
      ·
        refine ⟨3189428682828233389144097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8505143154208622371050925 3189428682828233389144097)
        ·
          refine ⟨2392071512121175041858073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3189428682828233389144097 2392071512121175041858073)
          ·
            refine ⟨1794053634090881281393555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2392071512121175041858073 1794053634090881281393555)
            ·
              refine ⟨2691080451136321922090333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794053634090881281393555 2691080451136321922090333)
              ·
                refine ⟨1009155169176120720783875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2691080451136321922090333 1009155169176120720783875)
                ·
                  refine ⟨1513732753764181081175813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009155169176120720783875 1513732753764181081175813)
                  ·
                    refine ⟨283824891330783952720465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1513732753764181081175813 283824891330783952720465)
                    ·
                      rfl

theorem cell23_1658241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_1658241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658241 prefixEnd_1658241 := by exact prefixLift 1658241
  have htrace : WordTrace (prefixWord ++ tailWord_1658241) baseStart_1658241 baseEnd_1658241 := by
    simpa [prefixWord, tailWord_1658241, baseEnd_1658241] using wordTrace_append hprefix tailTrace_1658241
  have hstable : (prefixWord ++ tailWord_1658241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658241).length < 2 ^ (prefixWord ++ tailWord_1658241).sum := by decide
  have hdescent : baseEnd_1658241 < baseStart_1658241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658258 : List Nat := [3, 2, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_1658258 : Nat := 118140960795 + 1658258 * 2 ^ 59
def prefixEnd_1658258 : Nat := 4983230072969 + 3 ^ 40 * 1658258 * 2
def baseEnd_1658258 : Nat := 283827801054492763882939

theorem tailTrace_1658258 : CollatzResearch.WordTrace tailWord_1658258 prefixEnd_1658258 283827801054492763882939 := by
  unfold tailWord_1658258
  simp only [CollatzResearch.WordTrace]
  refine ⟨15120409506605487191043857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40321092017614632509450285 15120409506605487191043857)
  ·
    refine ⟨11340307129954115393282893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15120409506605487191043857 11340307129954115393282893)
    ·
      refine ⟨4252615173732793272481085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11340307129954115393282893 4252615173732793272481085)
      ·
        refine ⟨1594730690149797477180407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4252615173732793272481085 1594730690149797477180407)
        ·
          refine ⟨2392096035224696215770611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594730690149797477180407 2392096035224696215770611)
          ·
            refine ⟨3588144052837044323655917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392096035224696215770611 3588144052837044323655917)
            ·
              refine ⟨1345554019813891621370969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3588144052837044323655917 1345554019813891621370969)
              ·
                refine ⟨1009165514860418716028227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1345554019813891621370969 1009165514860418716028227)
                ·
                  refine ⟨1513748272290628074042341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009165514860418716028227 1513748272290628074042341)
                  ·
                    refine ⟨283827801054492763882939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1513748272290628074042341 283827801054492763882939)
                    ·
                      rfl

theorem cell23_1658258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_1658258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658258 prefixEnd_1658258 := by exact prefixLift 1658258
  have htrace : WordTrace (prefixWord ++ tailWord_1658258) baseStart_1658258 baseEnd_1658258 := by
    simpa [prefixWord, tailWord_1658258, baseEnd_1658258] using wordTrace_append hprefix tailTrace_1658258
  have hstable : (prefixWord ++ tailWord_1658258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658258).length < 2 ^ (prefixWord ++ tailWord_1658258).sum := by decide
  have hdescent : baseEnd_1658258 < baseStart_1658258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658287 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 3, 2, 2]
def baseStart_1658287 : Nat := 118140960795 + 1658287 * 2 ^ 59
def prefixEnd_1658287 : Nat := 4983230072969 + 3 ^ 40 * 1658287 * 2
def baseEnd_1658287 : Nat := 851498294102458678186183

theorem tailTrace_1658287 : CollatzResearch.WordTrace tailWord_1658287 prefixEnd_1658287 851498294102458678186183 := by
  unfold tailWord_1658287
  simp only [CollatzResearch.WordTrace]
  refine ⟨60482695743316886716981115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40321797162211257811320743 60482695743316886716981115)
  ·
    refine ⟨90724043614975330075471673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60482695743316886716981115 90724043614975330075471673)
    ·
      refine ⟨68043032711231497556603755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90724043614975330075471673 68043032711231497556603755)
      ·
        refine ⟨102064549066847246334905633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68043032711231497556603755 102064549066847246334905633)
        ·
          refine ⟨76548411800135434751179225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102064549066847246334905633 76548411800135434751179225)
          ·
            refine ⟨57411308850101576063384419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76548411800135434751179225 57411308850101576063384419)
            ·
              refine ⟨86116963275152364095076629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57411308850101576063384419 86116963275152364095076629)
              ·
                refine ⟨4036732653522767066956717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86116963275152364095076629 4036732653522767066956717)
                ·
                  refine ⟨1513774745071037650108769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4036732653522767066956717 1513774745071037650108769)
                  ·
                    refine ⟨1135331058803278237581577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1513774745071037650108769 1135331058803278237581577)
                    ·
                      refine ⟨851498294102458678186183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135331058803278237581577 851498294102458678186183)
                      ·
                        rfl

theorem cell23_1658287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 2, 2].length) (baseStart_1658287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658287 prefixEnd_1658287 := by exact prefixLift 1658287
  have htrace : WordTrace (prefixWord ++ tailWord_1658287) baseStart_1658287 baseEnd_1658287 := by
    simpa [prefixWord, tailWord_1658287, baseEnd_1658287] using wordTrace_append hprefix tailTrace_1658287
  have hstable : (prefixWord ++ tailWord_1658287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658287).length < 2 ^ (prefixWord ++ tailWord_1658287).sum := by decide
  have hdescent : baseEnd_1658287 < baseStart_1658287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658337 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_1658337 : Nat := 118140960795 + 1658337 * 2 ^ 59
def prefixEnd_1658337 : Nat := 4983230072969 + 3 ^ 40 * 1658337 * 2
def baseEnd_1658337 : Nat := 851523968135183482560953

theorem tailTrace_1658337 : CollatzResearch.WordTrace tailWord_1658337 prefixEnd_1658337 851523968135183482560953 := by
  unfold tailWord_1658337
  simp only [CollatzResearch.WordTrace]
  refine ⟨60484519393135745256301265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40323012928757163504200843 60484519393135745256301265)
  ·
    refine ⟨45363389544851808942225949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60484519393135745256301265 45363389544851808942225949)
    ·
      refine ⟨17011271079319428353334731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45363389544851808942225949 17011271079319428353334731)
      ·
        refine ⟨25516906618979142530002097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17011271079319428353334731 25516906618979142530002097)
        ·
          refine ⟨19137679964234356897501573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25516906618979142530002097 19137679964234356897501573)
          ·
            refine ⟨3588314993293941918281545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19137679964234356897501573 3588314993293941918281545)
            ·
              refine ⟨2691236244970456438711159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3588314993293941918281545 2691236244970456438711159)
              ·
                refine ⟨4036854367455684658066739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691236244970456438711159 4036854367455684658066739)
                ·
                  refine ⟨6055281551183526987100109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4036854367455684658066739 6055281551183526987100109)
                  ·
                    refine ⟨2270730581693822620162541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6055281551183526987100109 2270730581693822620162541)
                    ·
                      refine ⟨851523968135183482560953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2270730581693822620162541 851523968135183482560953)
                      ·
                        rfl

theorem cell23_1658337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_1658337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658337 prefixEnd_1658337 := by exact prefixLift 1658337
  have htrace : WordTrace (prefixWord ++ tailWord_1658337) baseStart_1658337 baseEnd_1658337 := by
    simpa [prefixWord, tailWord_1658337, baseEnd_1658337] using wordTrace_append hprefix tailTrace_1658337
  have hstable : (prefixWord ++ tailWord_1658337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658337).length < 2 ^ (prefixWord ++ tailWord_1658337).sum := by decide
  have hdescent : baseEnd_1658337 < baseStart_1658337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658350 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_1658350 : Nat := 118140960795 + 1658350 * 2 ^ 59
def prefixEnd_1658350 : Nat := 4983230072969 + 3 ^ 40 * 1658350 * 2
def baseEnd_1658350 : Nat := 851530643383691931698393

theorem tailTrace_1658350 : CollatzResearch.WordTrace tailWord_1658350 prefixEnd_1658350 851530643383691931698393 := by
  unfold tailWord_1658350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7560624192761081059565563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40323329028059098984349669 7560624192761081059565563)
  ·
    refine ⟨11340936289141621589348345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7560624192761081059565563 11340936289141621589348345)
    ·
      refine ⟨8505702216856216192011259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11340936289141621589348345 8505702216856216192011259)
      ·
        refine ⟨12758553325284324288016889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8505702216856216192011259 12758553325284324288016889)
        ·
          refine ⟨9568914993963243216012667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12758553325284324288016889 9568914993963243216012667)
          ·
            refine ⟨14353372490944864824019001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9568914993963243216012667 14353372490944864824019001)
            ·
              refine ⟨10765029368208648618014251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14353372490944864824019001 10765029368208648618014251)
              ·
                refine ⟨16147544052312972927021377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10765029368208648618014251 16147544052312972927021377)
                ·
                  refine ⟨12110658039234729695266033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16147544052312972927021377 12110658039234729695266033)
                  ·
                    refine ⟨9082993529426047271449525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12110658039234729695266033 9082993529426047271449525)
                    ·
                      refine ⟨851530643383691931698393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9082993529426047271449525 851530643383691931698393)
                      ·
                        rfl

theorem cell23_1658350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_1658350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658350 prefixEnd_1658350 := by exact prefixLift 1658350
  have htrace : WordTrace (prefixWord ++ tailWord_1658350) baseStart_1658350 baseEnd_1658350 := by
    simpa [prefixWord, tailWord_1658350, baseEnd_1658350] using wordTrace_append hprefix tailTrace_1658350
  have hstable : (prefixWord ++ tailWord_1658350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658350).length < 2 ^ (prefixWord ++ tailWord_1658350).sum := by decide
  have hdescent : baseEnd_1658350 < baseStart_1658350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658388 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_1658388 : Nat := 118140960795 + 1658388 * 2 ^ 59
def prefixEnd_1658388 : Nat := 4983230072969 + 3 ^ 40 * 1658388 * 2
def baseEnd_1658388 : Nat := 851550155648562783023219

theorem tailTrace_1658388 : CollatzResearch.WordTrace tailWord_1658388 prefixEnd_1658388 851550155648562783023219 := by
  unfold tailWord_1658388
  simp only [CollatzResearch.WordTrace]
  refine ⟨30243189757975490483203909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40324253010633987310938545 30243189757975490483203909)
  ·
    refine ⟨5670598079620404465600733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30243189757975490483203909 5670598079620404465600733)
    ·
      refine ⟨2126474279857651674600275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5670598079620404465600733 2126474279857651674600275)
      ·
        refine ⟨3189711419786477511900413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126474279857651674600275 3189711419786477511900413)
        ·
          refine ⟨1196141782419929066962655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3189711419786477511900413 1196141782419929066962655)
          ·
            refine ⟨1794212673629893600443983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196141782419929066962655 1794212673629893600443983)
            ·
              refine ⟨2691319010444840400665975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794212673629893600443983 2691319010444840400665975)
              ·
                refine ⟨4036978515667260600998963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691319010444840400665975 4036978515667260600998963)
                ·
                  refine ⟨6055467773500890901498445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4036978515667260600998963 6055467773500890901498445)
                  ·
                    refine ⟨2270800415062834088061917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6055467773500890901498445 2270800415062834088061917)
                    ·
                      refine ⟨851550155648562783023219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2270800415062834088061917 851550155648562783023219)
                      ·
                        rfl

theorem cell23_1658388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_1658388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658388 prefixEnd_1658388 := by exact prefixLift 1658388
  have htrace : WordTrace (prefixWord ++ tailWord_1658388) baseStart_1658388 baseEnd_1658388 := by
    simpa [prefixWord, tailWord_1658388, baseEnd_1658388] using wordTrace_append hprefix tailTrace_1658388
  have hstable : (prefixWord ++ tailWord_1658388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658388).length < 2 ^ (prefixWord ++ tailWord_1658388).sum := by decide
  have hdescent : baseEnd_1658388 < baseStart_1658388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658437 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 2, 5, 2]
def baseStart_1658437 : Nat := 118140960795 + 1658437 * 2 ^ 59
def prefixEnd_1658437 : Nat := 4983230072969 + 3 ^ 40 * 1658437 * 2
def baseEnd_1658437 : Nat := 851575316200633091310493

theorem tailTrace_1658437 : CollatzResearch.WordTrace tailWord_1658437 prefixEnd_1658437 851575316200633091310493 := by
  unfold tailWord_1658437
  simp only [CollatzResearch.WordTrace]
  refine ⟨60488166692773462334941565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40325444461848974889961043 60488166692773462334941565)
  ·
    refine ⟨22683062509790048375603087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60488166692773462334941565 22683062509790048375603087)
    ·
      refine ⟨34024593764685072563404631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22683062509790048375603087 34024593764685072563404631)
      ·
        refine ⟨51036890647027608845106947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34024593764685072563404631 51036890647027608845106947)
        ·
          refine ⟨76555335970541413267660421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51036890647027608845106947 76555335970541413267660421)
          ·
            refine ⟨14354125494476514987686329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76555335970541413267660421 14354125494476514987686329)
            ·
              refine ⟨10765594120857386240764747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14354125494476514987686329 10765594120857386240764747)
              ·
                refine ⟨16148391181286079361147121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10765594120857386240764747 16148391181286079361147121)
                ·
                  refine ⟨12111293385964559520860341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16148391181286079361147121 12111293385964559520860341)
                  ·
                    refine ⟨1135433754934177455080657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12111293385964559520860341 1135433754934177455080657)
                    ·
                      refine ⟨851575316200633091310493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135433754934177455080657 851575316200633091310493)
                      ·
                        rfl

theorem cell23_1658437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 5, 2].length) (baseStart_1658437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658437 prefixEnd_1658437 := by exact prefixLift 1658437
  have htrace : WordTrace (prefixWord ++ tailWord_1658437) baseStart_1658437 baseEnd_1658437 := by
    simpa [prefixWord, tailWord_1658437, baseEnd_1658437] using wordTrace_append hprefix tailTrace_1658437
  have hstable : (prefixWord ++ tailWord_1658437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658437).length < 2 ^ (prefixWord ++ tailWord_1658437).sum := by decide
  have hdescent : baseEnd_1658437 < baseStart_1658437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658467 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1658467 : Nat := 118140960795 + 1658467 * 2 ^ 59
def prefixEnd_1658467 : Nat := 4983230072969 + 3 ^ 40 * 1658467 * 2
def baseEnd_1658467 : Nat := 851590720620267973935355

theorem tailTrace_1658467 : CollatzResearch.WordTrace tailWord_1658467 prefixEnd_1658467 851590720620267973935355 := by
  unfold tailWord_1658467
  simp only [CollatzResearch.WordTrace]
  refine ⟨60489260882664777458533655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40326173921776518305689103 60489260882664777458533655)
  ·
    refine ⟨90733891323997166187800483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60489260882664777458533655 90733891323997166187800483)
    ·
      refine ⟨136100836985995749281700725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90733891323997166187800483 136100836985995749281700725)
      ·
        refine ⟨12759453467437101495159443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136100836985995749281700725 12759453467437101495159443)
        ·
          refine ⟨19139180201155652242739165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12759453467437101495159443 19139180201155652242739165)
          ·
            refine ⟨7177192575433369591027187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19139180201155652242739165 7177192575433369591027187)
            ·
              refine ⟨10765788863150054386540781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7177192575433369591027187 10765788863150054386540781)
              ·
                refine ⟨4037170823681270394952793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10765788863150054386540781 4037170823681270394952793)
                ·
                  refine ⟨3027878117760952796214595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4037170823681270394952793 3027878117760952796214595)
                  ·
                    refine ⟨4541817176641429194321893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3027878117760952796214595 4541817176641429194321893)
                    ·
                      refine ⟨851590720620267973935355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4541817176641429194321893 851590720620267973935355)
                      ·
                        rfl

theorem cell23_1658467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1658467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658467 prefixEnd_1658467 := by exact prefixLift 1658467
  have htrace : WordTrace (prefixWord ++ tailWord_1658467) baseStart_1658467 baseEnd_1658467 := by
    simpa [prefixWord, tailWord_1658467, baseEnd_1658467] using wordTrace_append hprefix tailTrace_1658467
  have hstable : (prefixWord ++ tailWord_1658467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658467).length < 2 ^ (prefixWord ++ tailWord_1658467).sum := by decide
  have hdescent : baseEnd_1658467 < baseStart_1658467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658544 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 2, 3, 2]
def baseStart_1658544 : Nat := 118140960795 + 1658544 * 2 ^ 59
def prefixEnd_1658544 : Nat := 4983230072969 + 3 ^ 40 * 1658544 * 2
def baseEnd_1658544 : Nat := 851630258630664172672501

theorem tailTrace_1658544 : CollatzResearch.WordTrace tailWord_1658544 prefixEnd_1658544 851630258630664172672501 := by
  unfold tailWord_1658544
  simp only [CollatzResearch.WordTrace]
  refine ⟨30246034651692909804543343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40328046202257213072724457 30246034651692909804543343)
  ·
    refine ⟨45369051977539364706815015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30246034651692909804543343 45369051977539364706815015)
    ·
      refine ⟨68053577966309047060222523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45369051977539364706815015 68053577966309047060222523)
      ·
        refine ⟨102080366949463570590333785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68053577966309047060222523 102080366949463570590333785)
        ·
          refine ⟨76560275212097677942750339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102080366949463570590333785 76560275212097677942750339)
          ·
            refine ⟨114840412818146516914125509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76560275212097677942750339 114840412818146516914125509)
            ·
              refine ⟨21532577403402471921398533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114840412818146516914125509 21532577403402471921398533)
              ·
                refine ⟨4037358263137963485262225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21532577403402471921398533 4037358263137963485262225)
                ·
                  refine ⟨3028018697353472613946669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4037358263137963485262225 3028018697353472613946669)
                  ·
                    refine ⟨1135507011507552230230001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028018697353472613946669 1135507011507552230230001)
                    ·
                      refine ⟨851630258630664172672501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135507011507552230230001 851630258630664172672501)
                      ·
                        rfl

theorem cell23_1658544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 3, 2].length) (baseStart_1658544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658544 prefixEnd_1658544 := by exact prefixLift 1658544
  have htrace : WordTrace (prefixWord ++ tailWord_1658544) baseStart_1658544 baseEnd_1658544 := by
    simpa [prefixWord, tailWord_1658544, baseEnd_1658544] using wordTrace_append hprefix tailTrace_1658544
  have hstable : (prefixWord ++ tailWord_1658544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658544).length < 2 ^ (prefixWord ++ tailWord_1658544).sum := by decide
  have hdescent : baseEnd_1658544 < baseStart_1658544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658551 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 3, 1, 3]
def baseStart_1658551 : Nat := 118140960795 + 1658551 * 2 ^ 59
def prefixEnd_1658551 : Nat := 4983230072969 + 3 ^ 40 * 1658551 * 2
def baseEnd_1658551 : Nat := 851633852995245645284969

theorem tailTrace_1658551 : CollatzResearch.WordTrace tailWord_1658551 prefixEnd_1658551 851633852995245645284969 := by
  unfold tailWord_1658551
  simp only [CollatzResearch.WordTrace]
  refine ⟨60492324614360459804591507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40328216409573639869727671 60492324614360459804591507)
  ·
    refine ⟨90738486921540689706887261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60492324614360459804591507 90738486921540689706887261)
    ·
      refine ⟨34026932595577758640082723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90738486921540689706887261 34026932595577758640082723)
      ·
        refine ⟨51040398893366637960124085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34026932595577758640082723 51040398893366637960124085)
        ·
          refine ⟨4785037396253122308761633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51040398893366637960124085 4785037396253122308761633)
          ·
            refine ⟨3588778047189841731571225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4785037396253122308761633 3588778047189841731571225)
            ·
              refine ⟨2691583535392381298678419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3588778047189841731571225 2691583535392381298678419)
              ·
                refine ⟨4037375303088571948017629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691583535392381298678419 4037375303088571948017629)
                ·
                  refine ⟨1514015738658214480506611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4037375303088571948017629 1514015738658214480506611)
                  ·
                    refine ⟨2271023607987321720759917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1514015738658214480506611 2271023607987321720759917)
                    ·
                      refine ⟨851633852995245645284969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2271023607987321720759917 851633852995245645284969)
                      ·
                        rfl

theorem cell23_1658551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_1658551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658551 prefixEnd_1658551 := by exact prefixLift 1658551
  have htrace : WordTrace (prefixWord ++ tailWord_1658551) baseStart_1658551 baseEnd_1658551 := by
    simpa [prefixWord, tailWord_1658551, baseEnd_1658551] using wordTrace_append hprefix tailTrace_1658551
  have hstable : (prefixWord ++ tailWord_1658551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658551).length < 2 ^ (prefixWord ++ tailWord_1658551).sum := by decide
  have hdescent : baseEnd_1658551 < baseStart_1658551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658574 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2]
def baseStart_1658574 : Nat := 118140960795 + 1658574 * 2 ^ 59
def prefixEnd_1658574 : Nat := 4983230072969 + 3 ^ 40 * 1658574 * 2
def baseEnd_1658574 : Nat := 851645663050299055297363

theorem tailTrace_1658574 : CollatzResearch.WordTrace tailWord_1658574 prefixEnd_1658574 851645663050299055297363 := by
  unfold tailWord_1658574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7561645436659641841584847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40328775662184756488452517 7561645436659641841584847)
  ·
    refine ⟨11342468154989462762377271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7561645436659641841584847 11342468154989462762377271)
    ·
      refine ⟨17013702232484194143565907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11342468154989462762377271 17013702232484194143565907)
      ·
        refine ⟨25520553348726291215348861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17013702232484194143565907 25520553348726291215348861)
        ·
          refine ⟨9570207505772359205755823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25520553348726291215348861 9570207505772359205755823)
          ·
            refine ⟨14355311258658538808633735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9570207505772359205755823 14355311258658538808633735)
            ·
              refine ⟨21532966887987808212950603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14355311258658538808633735 21532966887987808212950603)
              ·
                refine ⟨32299450331981712319425905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21532966887987808212950603 32299450331981712319425905)
                ·
                  refine ⟨24224587748986284239569429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32299450331981712319425905 24224587748986284239569429)
                  ·
                    refine ⟨1135527550733732073729817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24224587748986284239569429 1135527550733732073729817)
                    ·
                      refine ⟨851645663050299055297363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135527550733732073729817 851645663050299055297363)
                      ·
                        rfl

theorem cell23_1658574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_1658574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658574 prefixEnd_1658574 := by exact prefixLift 1658574
  have htrace : WordTrace (prefixWord ++ tailWord_1658574) baseStart_1658574 baseEnd_1658574 := by
    simpa [prefixWord, tailWord_1658574, baseEnd_1658574] using wordTrace_append hprefix tailTrace_1658574
  have hstable : (prefixWord ++ tailWord_1658574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658574).length < 2 ^ (prefixWord ++ tailWord_1658574).sum := by decide
  have hdescent : baseEnd_1658574 < baseStart_1658574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658614 : List Nat := [5, 1, 1, 1, 1, 4, 2, 8]
def baseStart_1658614 : Nat := 118140960795 + 1658614 * 2 ^ 59
def prefixEnd_1658614 : Nat := 4983230072969 + 3 ^ 40 * 1658614 * 2
def baseEnd_1658614 : Nat := 31543192676906625881377

theorem tailTrace_1658614 : CollatzResearch.WordTrace tailWord_1658614 prefixEnd_1658614 31543192676906625881377 := by
  unfold tailWord_1658614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3780913900820763847758431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40329748275421481042756597 3780913900820763847758431)
  ·
    refine ⟨5671370851231145771637647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3780913900820763847758431 5671370851231145771637647)
    ·
      refine ⟨8507056276846718657456471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5671370851231145771637647 8507056276846718657456471)
      ·
        refine ⟨12760584415270077986184707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8507056276846718657456471 12760584415270077986184707)
        ·
          refine ⟨19140876622905116979277061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12760584415270077986184707 19140876622905116979277061)
          ·
            refine ⟨3588914366794709433614449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19140876622905116979277061 3588914366794709433614449)
            ·
              refine ⟨2691685775096032075210837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3588914366794709433614449 2691685775096032075210837)
              ·
                refine ⟨31543192676906625881377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2691685775096032075210837 31543192676906625881377)
                ·
                  rfl

theorem cell23_1658614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_1658614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658614 prefixEnd_1658614 := by exact prefixLift 1658614
  have htrace : WordTrace (prefixWord ++ tailWord_1658614) baseStart_1658614 baseEnd_1658614 := by
    simpa [prefixWord, tailWord_1658614, baseEnd_1658614] using wordTrace_append hprefix tailTrace_1658614
  have hstable : (prefixWord ++ tailWord_1658614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658614).length < 2 ^ (prefixWord ++ tailWord_1658614).sum := by decide
  have hdescent : baseEnd_1658614 < baseStart_1658614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658628 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1658628 : Nat := 118140960795 + 1658628 * 2 ^ 59
def prefixEnd_1658628 : Nat := 4983230072969 + 3 ^ 40 * 1658628 * 2
def baseEnd_1658628 : Nat := 851673391005641844022115

theorem tailTrace_1658628 : CollatzResearch.WordTrace tailWord_1658628 prefixEnd_1658628 851673391005641844022115 := by
  unfold tailWord_1658628
  simp only [CollatzResearch.WordTrace]
  refine ⟨30247566517540750977572269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40330088690054334636763025 30247566517540750977572269)
  ·
    refine ⟨11342837444077781616589601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30247566517540750977572269 11342837444077781616589601)
    ·
      refine ⟨8507128083058336212442201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11342837444077781616589601 8507128083058336212442201)
      ·
        refine ⟨6380346062293752159331651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8507128083058336212442201 6380346062293752159331651)
        ·
          refine ⟨9570519093440628238997477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6380346062293752159331651 9570519093440628238997477)
          ·
            refine ⟨1794472330020117794812027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9570519093440628238997477 1794472330020117794812027)
            ·
              refine ⟨2691708495030176692218041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794472330020117794812027 2691708495030176692218041)
              ·
                refine ⟨2018781371272632519163531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2691708495030176692218041 2018781371272632519163531)
                ·
                  refine ⟨3028172056908948778745297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018781371272632519163531 3028172056908948778745297)
                  ·
                    refine ⟨2271129042681711584058973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3028172056908948778745297 2271129042681711584058973)
                    ·
                      refine ⟨851673391005641844022115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2271129042681711584058973 851673391005641844022115)
                      ·
                        rfl

theorem cell23_1658628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1658628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658628 prefixEnd_1658628 := by exact prefixLift 1658628
  have htrace : WordTrace (prefixWord ++ tailWord_1658628) baseStart_1658628 baseEnd_1658628 := by
    simpa [prefixWord, tailWord_1658628, baseEnd_1658628] using wordTrace_append hprefix tailTrace_1658628
  have hstable : (prefixWord ++ tailWord_1658628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658628).length < 2 ^ (prefixWord ++ tailWord_1658628).sum := by decide
  have hdescent : baseEnd_1658628 < baseStart_1658628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658658 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_1658658 : Nat := 118140960795 + 1658658 * 2 ^ 59
def prefixEnd_1658658 : Nat := 4983230072969 + 3 ^ 40 * 1658658 * 2
def baseEnd_1658658 : Nat := 851688795425276726646977

theorem tailTrace_1658658 : CollatzResearch.WordTrace tailWord_1658658 prefixEnd_1658658 851688795425276726646977 := by
  unfold tailWord_1658658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15124056806243204269684157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40330818149981878052491085 15124056806243204269684157)
  ·
    refine ⟨5671521302341201601131559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15124056806243204269684157 5671521302341201601131559)
    ·
      refine ⟨8507281953511802401697339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5671521302341201601131559 8507281953511802401697339)
      ·
        refine ⟨12760922930267703602546009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8507281953511802401697339 12760922930267703602546009)
        ·
          refine ⟨9570692197700777701909507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12760922930267703602546009 9570692197700777701909507)
          ·
            refine ⟨14356038296551166552864261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9570692197700777701909507 14356038296551166552864261)
            ·
              refine ⟨2691757180603343728662049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14356038296551166552864261 2691757180603343728662049)
              ·
                refine ⟨2018817885452507796496537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2691757180603343728662049 2018817885452507796496537)
                ·
                  refine ⟨1514113414089380847372403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2018817885452507796496537 1514113414089380847372403)
                  ·
                    refine ⟨2271170121134071271058605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1514113414089380847372403 2271170121134071271058605)
                    ·
                      refine ⟨851688795425276726646977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2271170121134071271058605 851688795425276726646977)
                      ·
                        rfl

theorem cell23_1658658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_1658658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658658 prefixEnd_1658658 := by exact prefixLift 1658658
  have htrace : WordTrace (prefixWord ++ tailWord_1658658) baseStart_1658658 baseEnd_1658658 := by
    simpa [prefixWord, tailWord_1658658, baseEnd_1658658] using wordTrace_append hprefix tailTrace_1658658
  have hstable : (prefixWord ++ tailWord_1658658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658658).length < 2 ^ (prefixWord ++ tailWord_1658658).sum := by decide
  have hdescent : baseEnd_1658658 < baseStart_1658658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658664 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1658664 : Nat := 118140960795 + 1658664 * 2 ^ 59
def prefixEnd_1658664 : Nat := 4983230072969 + 3 ^ 40 * 1658664 * 2
def baseEnd_1658664 : Nat := 851691876309203703171949

theorem tailTrace_1658664 : CollatzResearch.WordTrace tailWord_1658664 prefixEnd_1658664 851691876309203703171949 := by
  unfold tailWord_1658664
  simp only [CollatzResearch.WordTrace]
  refine ⟨30248223031475540051727523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40330964041967386735636697 30248223031475540051727523)
  ·
    refine ⟨45372334547213310077591285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30248223031475540051727523 45372334547213310077591285)
    ·
      refine ⟨4253656363801247819774183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45372334547213310077591285 4253656363801247819774183)
      ·
        refine ⟨6380484545701871729661275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4253656363801247819774183 6380484545701871729661275)
        ·
          refine ⟨9570726818552807594491913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6380484545701871729661275 9570726818552807594491913)
          ·
            refine ⟨7178045113914605695868935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9570726818552807594491913 7178045113914605695868935)
            ·
              refine ⟨10767067670871908543803403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7178045113914605695868935 10767067670871908543803403)
              ·
                refine ⟨16150601506307862815705105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10767067670871908543803403 16150601506307862815705105)
                ·
                  refine ⟨12112951129730897111778829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16150601506307862815705105 12112951129730897111778829)
                  ·
                    refine ⟨4542356673649086416917061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12112951129730897111778829 4542356673649086416917061)
                    ·
                      refine ⟨851691876309203703171949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4542356673649086416917061 851691876309203703171949)
                      ·
                        rfl

theorem cell23_1658664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1658664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658664 prefixEnd_1658664 := by exact prefixLift 1658664
  have htrace : WordTrace (prefixWord ++ tailWord_1658664) baseStart_1658664 baseEnd_1658664 := by
    simpa [prefixWord, tailWord_1658664, baseEnd_1658664] using wordTrace_append hprefix tailTrace_1658664
  have hstable : (prefixWord ++ tailWord_1658664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658664).length < 2 ^ (prefixWord ++ tailWord_1658664).sum := by decide
  have hdescent : baseEnd_1658664 < baseStart_1658664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658674 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_1658674 : Nat := 118140960795 + 1658674 * 2 ^ 59
def prefixEnd_1658674 : Nat := 4983230072969 + 3 ^ 40 * 1658674 * 2
def baseEnd_1658674 : Nat := 283899003705249554682301

theorem tailTrace_1658674 : CollatzResearch.WordTrace tailWord_1658674 prefixEnd_1658674 283899003705249554682301 := by
  unfold tailWord_1658674
  simp only [CollatzResearch.WordTrace]
  refine ⟨15124202698228712952829769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40331207195276567874212717 15124202698228712952829769)
  ·
    refine ⟨11343152023671534714622327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15124202698228712952829769 11343152023671534714622327)
    ·
      refine ⟨17014728035507302071933491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11343152023671534714622327 17014728035507302071933491)
      ·
        refine ⟨25522092053260953107900237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17014728035507302071933491 25522092053260953107900237)
        ·
          refine ⟨9570784519972857415462589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25522092053260953107900237 9570784519972857415462589)
          ·
            refine ⟨3589044194989821530798471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9570784519972857415462589 3589044194989821530798471)
            ·
              refine ⟨5383566292484732296197707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589044194989821530798471 5383566292484732296197707)
              ·
                refine ⟨8075349438727098444296561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383566292484732296197707 8075349438727098444296561)
                ·
                  refine ⟨6056512079045323833222421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8075349438727098444296561 6056512079045323833222421)
                  ·
                    refine ⟨283899003705249554682301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6056512079045323833222421 283899003705249554682301)
                    ·
                      rfl

theorem cell23_1658674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_1658674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658674 prefixEnd_1658674 := by exact prefixLift 1658674
  have htrace : WordTrace (prefixWord ++ tailWord_1658674) baseStart_1658674 baseEnd_1658674 := by
    simpa [prefixWord, tailWord_1658674, baseEnd_1658674] using wordTrace_append hprefix tailTrace_1658674
  have hstable : (prefixWord ++ tailWord_1658674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658674).length < 2 ^ (prefixWord ++ tailWord_1658674).sum := by decide
  have hdescent : baseEnd_1658674 < baseStart_1658674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658714 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3]
def baseStart_1658714 : Nat := 118140960795 + 1658714 * 2 ^ 59
def prefixEnd_1658714 : Nat := 4983230072969 + 3 ^ 40 * 1658714 * 2
def baseEnd_1658714 : Nat := 851717550341928507546719

theorem tailTrace_1658714 : CollatzResearch.WordTrace tailWord_1658714 prefixEnd_1658714 851717550341928507546719 := by
  unfold tailWord_1658714
  simp only [CollatzResearch.WordTrace]
  refine ⟨15124567428192484660693799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40332179808513292428516797 15124567428192484660693799)
  ·
    refine ⟨22686851142288726991040699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15124567428192484660693799 22686851142288726991040699)
    ·
      refine ⟨34030276713433090486561049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22686851142288726991040699 34030276713433090486561049)
      ·
        refine ⟨25522707535074817864920787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34030276713433090486561049 25522707535074817864920787)
        ·
          refine ⟨38284061302612226797381181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25522707535074817864920787 38284061302612226797381181)
          ·
            refine ⟨14356522988479585049017943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38284061302612226797381181 14356522988479585049017943)
            ·
              refine ⟨21534784482719377573526915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14356522988479585049017943 21534784482719377573526915)
              ·
                refine ⟨32302176724079066360290373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21534784482719377573526915 32302176724079066360290373)
                ·
                  refine ⟨6056658135764824942554445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32302176724079066360290373 6056658135764824942554445)
                  ·
                    refine ⟨2271246800911809353457917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6056658135764824942554445 2271246800911809353457917)
                    ·
                      refine ⟨851717550341928507546719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2271246800911809353457917 851717550341928507546719)
                      ·
                        rfl

theorem cell23_1658714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_1658714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658714 prefixEnd_1658714 := by exact prefixLift 1658714
  have htrace : WordTrace (prefixWord ++ tailWord_1658714) baseStart_1658714 baseEnd_1658714 := by
    simpa [prefixWord, tailWord_1658714, baseEnd_1658714] using wordTrace_append hprefix tailTrace_1658714
  have hstable : (prefixWord ++ tailWord_1658714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658714).length < 2 ^ (prefixWord ++ tailWord_1658714).sum := by decide
  have hdescent : baseEnd_1658714 < baseStart_1658714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658747 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 1, 10]
def baseStart_1658747 : Nat := 118140960795 + 1658747 * 2 ^ 59
def prefixEnd_1658747 : Nat := 4983230072969 + 3 ^ 40 * 1658747 * 2
def baseEnd_1658747 : Nat := 283911498401175626144689

theorem tailTrace_1658747 : CollatzResearch.WordTrace tailWord_1658747 prefixEnd_1658747 283911498401175626144689 := by
  unfold tailWord_1658747
  simp only [CollatzResearch.WordTrace]
  refine ⟨60499473321650385278726495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40332982214433590185817663 60499473321650385278726495)
  ·
    refine ⟨90749209982475577918089743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60499473321650385278726495 90749209982475577918089743)
    ·
      refine ⟨136123814973713366877134615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90749209982475577918089743 136123814973713366877134615)
      ·
        refine ⟨204185722460570050315701923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136123814973713366877134615 204185722460570050315701923)
        ·
          refine ⟨306278583690855075473552885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204185722460570050315701923 306278583690855075473552885)
          ·
            refine ⟨28713617221017663325645583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 306278583690855075473552885 28713617221017663325645583)
            ·
              refine ⟨43070425831526494988468375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28713617221017663325645583 43070425831526494988468375)
              ·
                refine ⟨64605638747289742482702563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43070425831526494988468375 64605638747289742482702563)
                ·
                  refine ⟨96908458120934613724053845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64605638747289742482702563 96908458120934613724053845)
                  ·
                    refine ⟨283911498401175626144689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 96908458120934613724053845 283911498401175626144689)
                    ·
                      rfl

theorem cell23_1658747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 10].length) (baseStart_1658747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658747 prefixEnd_1658747 := by exact prefixLift 1658747
  have htrace : WordTrace (prefixWord ++ tailWord_1658747) baseStart_1658747 baseEnd_1658747 := by
    simpa [prefixWord, tailWord_1658747, baseEnd_1658747] using wordTrace_append hprefix tailTrace_1658747
  have hstable : (prefixWord ++ tailWord_1658747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658747).length < 2 ^ (prefixWord ++ tailWord_1658747).sum := by decide
  have hdescent : baseEnd_1658747 < baseStart_1658747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658821 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 7, 1, 3]
def baseStart_1658821 : Nat := 118140960795 + 1658821 * 2 ^ 59
def prefixEnd_1658821 : Nat := 4983230072969 + 3 ^ 40 * 1658821 * 2
def baseEnd_1658821 : Nat := 851772492771959588908727

theorem tailTrace_1658821 : CollatzResearch.WordTrace tailWord_1658821 prefixEnd_1658821 851772492771959588908727 := by
  unfold tailWord_1658821
  simp only [CollatzResearch.WordTrace]
  refine ⟨60502172323382295916920317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40334781548921530611280211 60502172323382295916920317)
  ·
    refine ⟨22688314621268360968845119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60502172323382295916920317 22688314621268360968845119)
    ·
      refine ⟨34032471931902541453267679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22688314621268360968845119 34032471931902541453267679)
      ·
        refine ⟨51048707897853812179901519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34032471931902541453267679 51048707897853812179901519)
        ·
          refine ⟨76573061846780718269852279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51048707897853812179901519 76573061846780718269852279)
          ·
            refine ⟨114859592770171077404778419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76573061846780718269852279 114859592770171077404778419)
            ·
              refine ⟨172289389155256616107167629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114859592770171077404778419 172289389155256616107167629)
              ·
                refine ⟨64608520933221231040187861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172289389155256616107167629 64608520933221231040187861)
                ·
                  refine ⟨1514262209372372602504403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 64608520933221231040187861 1514262209372372602504403)
                  ·
                    refine ⟨2271393314058558903756605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1514262209372372602504403 2271393314058558903756605)
                    ·
                      refine ⟨851772492771959588908727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2271393314058558903756605 851772492771959588908727)
                      ·
                        rfl

theorem cell23_1658821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_1658821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658821 prefixEnd_1658821 := by exact prefixLift 1658821
  have htrace : WordTrace (prefixWord ++ tailWord_1658821) baseStart_1658821 baseEnd_1658821 := by
    simpa [prefixWord, tailWord_1658821, baseEnd_1658821] using wordTrace_append hprefix tailTrace_1658821
  have hstable : (prefixWord ++ tailWord_1658821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658821).length < 2 ^ (prefixWord ++ tailWord_1658821).sum := by decide
  have hdescent : baseEnd_1658821 < baseStart_1658821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658855 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1658855 : Nat := 118140960795 + 1658855 * 2 ^ 59
def prefixEnd_1658855 : Nat := 4983230072969 + 3 ^ 40 * 1658855 * 2
def baseEnd_1658855 : Nat := 851789951114212455883571

theorem tailTrace_1658855 : CollatzResearch.WordTrace tailWord_1658855 prefixEnd_1658855 851789951114212455883571 := by
  unfold tailWord_1658855
  simp only [CollatzResearch.WordTrace]
  refine ⟨60503412405259119723658019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40335608270172746482438679 60503412405259119723658019)
  ·
    refine ⟨90755118607888679585487029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60503412405259119723658019 90755118607888679585487029)
    ·
      refine ⟨8508292369489563711139409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90755118607888679585487029 8508292369489563711139409)
      ·
        refine ⟨6381219277117172783354557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8508292369489563711139409 6381219277117172783354557)
        ·
          refine ⟨2392957228918939793757959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6381219277117172783354557 2392957228918939793757959)
          ·
            refine ⟨3589435843378409690636939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392957228918939793757959 3589435843378409690636939)
            ·
              refine ⟨5384153765067614535955409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589435843378409690636939 5384153765067614535955409)
              ·
                refine ⟨4038115323800710901966557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5384153765067614535955409 4038115323800710901966557)
                ·
                  refine ⟨1514293246425266588237459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4038115323800710901966557 1514293246425266588237459)
                  ·
                    refine ⟨2271439869637899882356189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1514293246425266588237459 2271439869637899882356189)
                    ·
                      refine ⟨851789951114212455883571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2271439869637899882356189 851789951114212455883571)
                      ·
                        rfl

theorem cell23_1658855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1658855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658855 prefixEnd_1658855 := by exact prefixLift 1658855
  have htrace : WordTrace (prefixWord ++ tailWord_1658855) baseStart_1658855 baseEnd_1658855 := by
    simpa [prefixWord, tailWord_1658855, baseEnd_1658855] using wordTrace_append hprefix tailTrace_1658855
  have hstable : (prefixWord ++ tailWord_1658855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658855).length < 2 ^ (prefixWord ++ tailWord_1658855).sum := by decide
  have hdescent : baseEnd_1658855 < baseStart_1658855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658874 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_1658874 : Nat := 118140960795 + 1658874 * 2 ^ 59
def prefixEnd_1658874 : Nat := 4983230072969 + 3 ^ 40 * 1658874 * 2
def baseEnd_1658874 : Nat := 851799707246647881545983

theorem tailTrace_1658874 : CollatzResearch.WordTrace tailWord_1658874 prefixEnd_1658874 851799707246647881545983 := by
  unfold tailWord_1658874
  simp only [CollatzResearch.WordTrace]
  refine ⟨15126026348047571492149919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40336070261460190645733117 15126026348047571492149919)
  ·
    refine ⟨22689039522071357238224879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15126026348047571492149919 22689039522071357238224879)
    ·
      refine ⟨34033559283107035857337319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22689039522071357238224879 34033559283107035857337319)
      ·
        refine ⟨51050338924660553786005979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34033559283107035857337319 51050338924660553786005979)
        ·
          refine ⟨76575508386990830679008969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51050338924660553786005979 76575508386990830679008969)
          ·
            refine ⟨57431631290243123009256727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76575508386990830679008969 57431631290243123009256727)
            ·
              refine ⟨86147446935364684513885091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57431631290243123009256727 86147446935364684513885091)
              ·
                refine ⟨129221170403047026770827637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86147446935364684513885091 129221170403047026770827637)
                ·
                  refine ⟨12114484725285658759765091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129221170403047026770827637 12114484725285658759765091)
                  ·
                    refine ⟨18171727087928488139647637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12114484725285658759765091 18171727087928488139647637)
                    ·
                      refine ⟨851799707246647881545983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18171727087928488139647637 851799707246647881545983)
                      ·
                        rfl

theorem cell23_1658874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_1658874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658874 prefixEnd_1658874 := by exact prefixLift 1658874
  have htrace : WordTrace (prefixWord ++ tailWord_1658874) baseStart_1658874 baseEnd_1658874 := by
    simpa [prefixWord, tailWord_1658874, baseEnd_1658874] using wordTrace_append hprefix tailTrace_1658874
  have hstable : (prefixWord ++ tailWord_1658874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658874).length < 2 ^ (prefixWord ++ tailWord_1658874).sum := by decide
  have hdescent : baseEnd_1658874 < baseStart_1658874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658881 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1658881 : Nat := 118140960795 + 1658881 * 2 ^ 59
def prefixEnd_1658881 : Nat := 4983230072969 + 3 ^ 40 * 1658881 * 2
def baseEnd_1658881 : Nat := 851803301611229354158451

theorem tailTrace_1658881 : CollatzResearch.WordTrace tailWord_1658881 prefixEnd_1658881 851803301611229354158451 := by
  unfold tailWord_1658881
  simp only [CollatzResearch.WordTrace]
  refine ⟨60504360703164926164104497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40336240468776617442736331 60504360703164926164104497)
  ·
    refine ⟨45378270527373694623078373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60504360703164926164104497 45378270527373694623078373)
    ·
      refine ⟨8508425723882567741827195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45378270527373694623078373 8508425723882567741827195)
      ·
        refine ⟨12762638585823851612740793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8508425723882567741827195 12762638585823851612740793)
        ·
          refine ⟨9571978939367888709555595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12762638585823851612740793 9571978939367888709555595)
          ·
            refine ⟨14357968409051833064333393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9571978939367888709555595 14357968409051833064333393)
            ·
              refine ⟨10768476306788874798250045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14357968409051833064333393 10768476306788874798250045)
              ·
                refine ⟨4038178615045828049343767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10768476306788874798250045 4038178615045828049343767)
                ·
                  refine ⟨6057267922568742074015651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4038178615045828049343767 6057267922568742074015651)
                  ·
                    refine ⟨9085901883853113111023477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6057267922568742074015651 9085901883853113111023477)
                    ·
                      refine ⟨851803301611229354158451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9085901883853113111023477 851803301611229354158451)
                      ·
                        rfl

theorem cell23_1658881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1658881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658881 prefixEnd_1658881 := by exact prefixLift 1658881
  have htrace : WordTrace (prefixWord ++ tailWord_1658881) baseStart_1658881 baseEnd_1658881 := by
    simpa [prefixWord, tailWord_1658881, baseEnd_1658881] using wordTrace_append hprefix tailTrace_1658881
  have hstable : (prefixWord ++ tailWord_1658881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658881).length < 2 ^ (prefixWord ++ tailWord_1658881).sum := by decide
  have hdescent : baseEnd_1658881 < baseStart_1658881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658908 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_1658908 : Nat := 118140960795 + 1658908 * 2 ^ 59
def prefixEnd_1658908 : Nat := 4983230072969 + 3 ^ 40 * 1658908 * 2
def baseEnd_1658908 : Nat := 851817165588900748520827

theorem tailTrace_1658908 : CollatzResearch.WordTrace tailWord_1658908 prefixEnd_1658908 851817165588900748520827 := by
  unfold tailWord_1658908
  simp only [CollatzResearch.WordTrace]
  refine ⟨30252672737033554887668689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40336896982711406516891585 30252672737033554887668689)
  ·
    refine ⟨22689504552775166165751517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30252672737033554887668689 22689504552775166165751517)
    ·
      refine ⟨8508564207290687312156819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22689504552775166165751517 8508564207290687312156819)
      ·
        refine ⟨12762846310936030968235229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8508564207290687312156819 12762846310936030968235229)
        ·
          refine ⟨4786067366601011613088211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12762846310936030968235229 4786067366601011613088211)
          ·
            refine ⟨7179101049901517419632317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786067366601011613088211 7179101049901517419632317)
            ·
              refine ⟨2692162893713069032362119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7179101049901517419632317 2692162893713069032362119)
              ·
                refine ⟨4038244340569603548543179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692162893713069032362119 4038244340569603548543179)
                ·
                  refine ⟨6057366510854405322814769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4038244340569603548543179 6057366510854405322814769)
                  ·
                    refine ⟨4543024883140803992111077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6057366510854405322814769 4543024883140803992111077)
                    ·
                      refine ⟨851817165588900748520827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4543024883140803992111077 851817165588900748520827)
                      ·
                        rfl

theorem cell23_1658908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_1658908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658908 prefixEnd_1658908 := by exact prefixLift 1658908
  have htrace : WordTrace (prefixWord ++ tailWord_1658908) baseStart_1658908 baseEnd_1658908 := by
    simpa [prefixWord, tailWord_1658908, baseEnd_1658908] using wordTrace_append hprefix tailTrace_1658908
  have hstable : (prefixWord ++ tailWord_1658908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658908).length < 2 ^ (prefixWord ++ tailWord_1658908).sum := by decide
  have hdescent : baseEnd_1658908 < baseStart_1658908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658928 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 4, 1, 3]
def baseStart_1658928 : Nat := 118140960795 + 1658928 * 2 ^ 59
def prefixEnd_1658928 : Nat := 4983230072969 + 3 ^ 40 * 1658928 * 2
def baseEnd_1658928 : Nat := 851827435201990670270735

theorem tailTrace_1658928 : CollatzResearch.WordTrace tailWord_1658928 prefixEnd_1658928 851827435201990670270735 := by
  unfold tailWord_1658928
  simp only [CollatzResearch.WordTrace]
  refine ⟨30253037466997326595532719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40337383289329768794043625 30253037466997326595532719)
  ·
    refine ⟨45379556200495989893299079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30253037466997326595532719 45379556200495989893299079)
    ·
      refine ⟨68069334300743984839948619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45379556200495989893299079 68069334300743984839948619)
      ·
        refine ⟨102104001451115977259922929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68069334300743984839948619 102104001451115977259922929)
        ·
          refine ⟨76578001088336982944942197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102104001451115977259922929 76578001088336982944942197)
          ·
            refine ⟨7179187602031592151088331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76578001088336982944942197 7179187602031592151088331)
            ·
              refine ⟨10768781403047388226632497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7179187602031592151088331 10768781403047388226632497)
              ·
                refine ⟨8076586052285541169974373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10768781403047388226632497 8076586052285541169974373)
                ·
                  refine ⟨1514359884803538969370195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8076586052285541169974373 1514359884803538969370195)
                  ·
                    refine ⟨2271539827205308454055293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1514359884803538969370195 2271539827205308454055293)
                    ·
                      refine ⟨851827435201990670270735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2271539827205308454055293 851827435201990670270735)
                      ·
                        rfl

theorem cell23_1658928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4, 1, 3].length) (baseStart_1658928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658928 prefixEnd_1658928 := by exact prefixLift 1658928
  have htrace : WordTrace (prefixWord ++ tailWord_1658928) baseStart_1658928 baseEnd_1658928 := by
    simpa [prefixWord, tailWord_1658928, baseEnd_1658928] using wordTrace_append hprefix tailTrace_1658928
  have hstable : (prefixWord ++ tailWord_1658928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658928).length < 2 ^ (prefixWord ++ tailWord_1658928).sum := by decide
  have hdescent : baseEnd_1658928 < baseStart_1658928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658929 : List Nat := [1, 2, 2, 3, 1, 5, 1, 3, 1, 2, 2]
def baseStart_1658929 : Nat := 118140960795 + 1658929 * 2 ^ 59
def prefixEnd_1658929 : Nat := 4983230072969 + 3 ^ 40 * 1658929 * 2
def baseEnd_1658929 : Nat := 851827948682645166358231

theorem tailTrace_1658929 : CollatzResearch.WordTrace tailWord_1658929 prefixEnd_1658929 851827948682645166358231 := by
  unfold tailWord_1658929
  simp only [CollatzResearch.WordTrace]
  refine ⟨60506111406991030361851841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40337407604660686907901227 60506111406991030361851841)
  ·
    refine ⟨45379583555243272771388881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60506111406991030361851841 45379583555243272771388881)
    ·
      refine ⟨34034687666432454578541661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45379583555243272771388881 34034687666432454578541661)
      ·
        refine ⟨12763007874912170466953123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34034687666432454578541661 12763007874912170466953123)
        ·
          refine ⟨19144511812368255700429685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12763007874912170466953123 19144511812368255700429685)
          ·
            refine ⟨1794797982409523971915283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19144511812368255700429685 1794797982409523971915283)
            ·
              refine ⟨2692196973614285957872925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794797982409523971915283 2692196973614285957872925)
              ·
                refine ⟨1009573865105357234202347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2692196973614285957872925 1009573865105357234202347)
                ·
                  refine ⟨1514360797658035851303521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009573865105357234202347 1514360797658035851303521)
                  ·
                    refine ⟨1135770598243526888477641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1514360797658035851303521 1135770598243526888477641)
                    ·
                      refine ⟨851827948682645166358231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135770598243526888477641 851827948682645166358231)
                      ·
                        rfl

theorem cell23_1658929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_1658929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658929 prefixEnd_1658929 := by exact prefixLift 1658929
  have htrace : WordTrace (prefixWord ++ tailWord_1658929) baseStart_1658929 baseEnd_1658929 := by
    simpa [prefixWord, tailWord_1658929, baseEnd_1658929] using wordTrace_append hprefix tailTrace_1658929
  have hstable : (prefixWord ++ tailWord_1658929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658929).length < 2 ^ (prefixWord ++ tailWord_1658929).sum := by decide
  have hdescent : baseEnd_1658929 < baseStart_1658929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658938 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2]
def baseStart_1658938 : Nat := 118140960795 + 1658938 * 2 ^ 59
def prefixEnd_1658938 : Nat := 4983230072969 + 3 ^ 40 * 1658938 * 2
def baseEnd_1658938 : Nat := 851832570008535631145689

theorem tailTrace_1658938 : CollatzResearch.WordTrace tailWord_1658938 prefixEnd_1658938 851832570008535631145689 := by
  unfold tailWord_1658938
  simp only [CollatzResearch.WordTrace]
  refine ⟨15126609915989606224732367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40337626442638949932619645 15126609915989606224732367)
  ·
    refine ⟨22689914873984409337098551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15126609915989606224732367 22689914873984409337098551)
    ·
      refine ⟨34034872310976614005647827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22689914873984409337098551 34034872310976614005647827)
      ·
        refine ⟨51052308466464921008471741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34034872310976614005647827 51052308466464921008471741)
        ·
          refine ⟨19144615674924345378176903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51052308466464921008471741 19144615674924345378176903)
          ·
            refine ⟨28716923512386518067265355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19144615674924345378176903 28716923512386518067265355)
            ·
              refine ⟨43075385268579777100898033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28716923512386518067265355 43075385268579777100898033)
              ·
                refine ⟨32306538951434832825673525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43075385268579777100898033 32306538951434832825673525)
                ·
                  refine ⟨3028738026697015577406893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32306538951434832825673525 3028738026697015577406893)
                  ·
                    refine ⟨1135776760011380841527585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028738026697015577406893 1135776760011380841527585)
                    ·
                      refine ⟨851832570008535631145689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135776760011380841527585 851832570008535631145689)
                      ·
                        rfl

theorem cell23_1658938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2].length) (baseStart_1658938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658938 prefixEnd_1658938 := by exact prefixLift 1658938
  have htrace : WordTrace (prefixWord ++ tailWord_1658938) baseStart_1658938 baseEnd_1658938 := by
    simpa [prefixWord, tailWord_1658938, baseEnd_1658938] using wordTrace_append hprefix tailTrace_1658938
  have hstable : (prefixWord ++ tailWord_1658938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658938).length < 2 ^ (prefixWord ++ tailWord_1658938).sum := by decide
  have hdescent : baseEnd_1658938 < baseStart_1658938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658941 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1658941 : Nat := 118140960795 + 1658941 * 2 ^ 59
def prefixEnd_1658941 : Nat := 4983230072969 + 3 ^ 40 * 1658941 * 2
def baseEnd_1658941 : Nat := 851834110450499119408175

theorem tailTrace_1658941 : CollatzResearch.WordTrace tailWord_1658941 prefixEnd_1658941 851834110450499119408175 := by
  unfold tailWord_1658941
  simp only [CollatzResearch.WordTrace]
  refine ⟨60506549082947556411288677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40337699388631704274192451 60506549082947556411288677)
  ·
    refine ⟨11344977953052666827116627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60506549082947556411288677 11344977953052666827116627)
    ·
      refine ⟨17017466929579000240674941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11344977953052666827116627 17017466929579000240674941)
      ·
        refine ⟨6381550098592125090253103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17017466929579000240674941 6381550098592125090253103)
        ·
          refine ⟨9572325147888187635379655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6381550098592125090253103 9572325147888187635379655)
          ·
            refine ⟨14358487721832281453069483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9572325147888187635379655 14358487721832281453069483)
            ·
              refine ⟨21537731582748422179604225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14358487721832281453069483 21537731582748422179604225)
              ·
                refine ⟨16153298687061316634703169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21537731582748422179604225 16153298687061316634703169)
                ·
                  refine ⟨12114974015295987476027377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16153298687061316634703169 12114974015295987476027377)
                  ·
                    refine ⟨9086230511471990607020533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12114974015295987476027377 9086230511471990607020533)
                    ·
                      refine ⟨851834110450499119408175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9086230511471990607020533 851834110450499119408175)
                      ·
                        rfl

theorem cell23_1658941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1658941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658941 prefixEnd_1658941 := by exact prefixLift 1658941
  have htrace : WordTrace (prefixWord ++ tailWord_1658941) baseStart_1658941 baseEnd_1658941 := by
    simpa [prefixWord, tailWord_1658941, baseEnd_1658941] using wordTrace_append hprefix tailTrace_1658941
  have hstable : (prefixWord ++ tailWord_1658941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658941).length < 2 ^ (prefixWord ++ tailWord_1658941).sum := by decide
  have hdescent : baseEnd_1658941 < baseStart_1658941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658945 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1658945 : Nat := 118140960795 + 1658945 * 2 ^ 59
def prefixEnd_1658945 : Nat := 4983230072969 + 3 ^ 40 * 1658945 * 2
def baseEnd_1658945 : Nat := 851836164373117103758157

theorem tailTrace_1658945 : CollatzResearch.WordTrace tailWord_1658945 prefixEnd_1658945 851836164373117103758157 := by
  unfold tailWord_1658945
  simp only [CollatzResearch.WordTrace]
  refine ⟨60506694974933065094434289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40337796649955376729622859 60506694974933065094434289)
  ·
    refine ⟨45380021231199798820825717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60506694974933065094434289 45380021231199798820825717)
    ·
      refine ⟨4254376990424981139452411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45380021231199798820825717 4254376990424981139452411)
      ·
        refine ⟨6381565485637471709178617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254376990424981139452411 6381565485637471709178617)
        ·
          refine ⟨4786174114228103781883963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6381565485637471709178617 4786174114228103781883963)
          ·
            refine ⟨7179261171342155672825945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786174114228103781883963 7179261171342155672825945)
            ·
              refine ⟨5384445878506616754619459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7179261171342155672825945 5384445878506616754619459)
              ·
                refine ⟨8076668817759925131929189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5384445878506616754619459 8076668817759925131929189)
                ·
                  refine ⟨1514375403329985962236723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8076668817759925131929189 1514375403329985962236723)
                  ·
                    refine ⟨2271563104994978943355085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1514375403329985962236723 2271563104994978943355085)
                    ·
                      refine ⟨851836164373117103758157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2271563104994978943355085 851836164373117103758157)
                      ·
                        rfl

theorem cell23_1658945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1658945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658945 prefixEnd_1658945 := by exact prefixLift 1658945
  have htrace : WordTrace (prefixWord ++ tailWord_1658945) baseStart_1658945 baseEnd_1658945 := by
    simpa [prefixWord, tailWord_1658945, baseEnd_1658945] using wordTrace_append hprefix tailTrace_1658945
  have hstable : (prefixWord ++ tailWord_1658945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658945).length < 2 ^ (prefixWord ++ tailWord_1658945).sum := by decide
  have hdescent : baseEnd_1658945 < baseStart_1658945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658951 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_1658951 : Nat := 118140960795 + 1658951 * 2 ^ 59
def prefixEnd_1658951 : Nat := 4983230072969 + 3 ^ 40 * 1658951 * 2
def baseEnd_1658951 : Nat := 851839245257044080283129

theorem tailTrace_1658951 : CollatzResearch.WordTrace tailWord_1658951 prefixEnd_1658951 851839245257044080283129 := by
  unfold tailWord_1658951
  simp only [CollatzResearch.WordTrace]
  refine ⟨60506913812911328119152707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40337942541940885412768471 60506913812911328119152707)
  ·
    refine ⟨90760370719366992178729061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60506913812911328119152707 90760370719366992178729061)
    ·
      refine ⟨17017569509881311033511699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90760370719366992178729061 17017569509881311033511699)
      ·
        refine ⟨25526354264821966550267549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17017569509881311033511699 25526354264821966550267549)
        ·
          refine ⟨9572382849308237456350331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25526354264821966550267549 9572382849308237456350331)
          ·
            refine ⟨14358574273962356184525497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9572382849308237456350331 14358574273962356184525497)
            ·
              refine ⟨10768930705471767138394123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14358574273962356184525497 10768930705471767138394123)
              ·
                refine ⟨16153396058207650707591185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10768930705471767138394123 16153396058207650707591185)
                ·
                  refine ⟨12115047043655738030693389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16153396058207650707591185 12115047043655738030693389)
                  ·
                    refine ⟨4543142641370901761510021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12115047043655738030693389 4543142641370901761510021)
                    ·
                      refine ⟨851839245257044080283129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4543142641370901761510021 851839245257044080283129)
                      ·
                        rfl

theorem cell23_1658951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_1658951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658951 prefixEnd_1658951 := by exact prefixLift 1658951
  have htrace : WordTrace (prefixWord ++ tailWord_1658951) baseStart_1658951 baseEnd_1658951 := by
    simpa [prefixWord, tailWord_1658951, baseEnd_1658951] using wordTrace_append hprefix tailTrace_1658951
  have hstable : (prefixWord ++ tailWord_1658951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658951).length < 2 ^ (prefixWord ++ tailWord_1658951).sum := by decide
  have hdescent : baseEnd_1658951 < baseStart_1658951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658962 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_1658962 : Nat := 118140960795 + 1658962 * 2 ^ 59
def prefixEnd_1658962 : Nat := 4983230072969 + 3 ^ 40 * 1658962 * 2
def baseEnd_1658962 : Nat := 851844893544243537245579

theorem tailTrace_1658962 : CollatzResearch.WordTrace tailWord_1658962 prefixEnd_1658962 851844893544243537245579 := by
  unfold tailWord_1658962
  simp only [CollatzResearch.WordTrace]
  refine ⟨15126828753967869249450785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40338210010580984665202093 15126828753967869249450785)
  ·
    refine ⟨11345121565475901937088089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15126828753967869249450785 11345121565475901937088089)
    ·
      refine ⟨8508841174106926452816067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11345121565475901937088089 8508841174106926452816067)
      ·
        refine ⟨12763261761160389679224101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8508841174106926452816067 12763261761160389679224101)
        ·
          refine ⟨2393111580217573064854519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12763261761160389679224101 2393111580217573064854519)
          ·
            refine ⟨3589667370326359597281779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393111580217573064854519 3589667370326359597281779)
            ·
              refine ⟨5384501055489539395922669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589667370326359597281779 5384501055489539395922669)
              ·
                refine ⟨2019187895808577273471001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5384501055489539395922669 2019187895808577273471001)
                ·
                  refine ⟨1514390921856432955103251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2019187895808577273471001 1514390921856432955103251)
                  ·
                    refine ⟨2271586382784649432654877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1514390921856432955103251 2271586382784649432654877)
                    ·
                      refine ⟨851844893544243537245579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2271586382784649432654877 851844893544243537245579)
                      ·
                        rfl

theorem cell23_1658962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_1658962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658962 prefixEnd_1658962 := by exact prefixLift 1658962
  have htrace : WordTrace (prefixWord ++ tailWord_1658962) baseStart_1658962 baseEnd_1658962 := by
    simpa [prefixWord, tailWord_1658962, baseEnd_1658962] using wordTrace_append hprefix tailTrace_1658962
  have hstable : (prefixWord ++ tailWord_1658962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658962).length < 2 ^ (prefixWord ++ tailWord_1658962).sum := by decide
  have hdescent : baseEnd_1658962 < baseStart_1658962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658972 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_1658972 : Nat := 118140960795 + 1658972 * 2 ^ 59
def prefixEnd_1658972 : Nat := 4983230072969 + 3 ^ 40 * 1658972 * 2
def baseEnd_1658972 : Nat := 851850028350788498120533

theorem tailTrace_1658972 : CollatzResearch.WordTrace tailWord_1658972 prefixEnd_1658972 851850028350788498120533 := by
  unfold tailWord_1658972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30253839872917624352833585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40338453163890165803778113 30253839872917624352833585)
  ·
    refine ⟨22690379904688218264625189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30253839872917624352833585 22690379904688218264625189)
    ·
      refine ⟨4254446232129040924617223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22690379904688218264625189 4254446232129040924617223)
      ·
        refine ⟨6381669348193561386925835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254446232129040924617223 6381669348193561386925835)
        ·
          refine ⟨9572504022290342080388753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6381669348193561386925835 9572504022290342080388753)
          ·
            refine ⟨7179378016717756560291565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9572504022290342080388753 7179378016717756560291565)
            ·
              refine ⟨2692266756269158710109337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7179378016717756560291565 2692266756269158710109337)
              ·
                refine ⟨2019200067201869032582003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2692266756269158710109337 2019200067201869032582003)
                ·
                  refine ⟨3028800100802803548873005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019200067201869032582003 3028800100802803548873005)
                  ·
                    refine ⟨1135800037801051330827377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028800100802803548873005 1135800037801051330827377)
                    ·
                      refine ⟨851850028350788498120533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135800037801051330827377 851850028350788498120533)
                      ·
                        rfl

theorem cell23_1658972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_1658972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1658972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1658972 prefixEnd_1658972 := by exact prefixLift 1658972
  have htrace : WordTrace (prefixWord ++ tailWord_1658972) baseStart_1658972 baseEnd_1658972 := by
    simpa [prefixWord, tailWord_1658972, baseEnd_1658972] using wordTrace_append hprefix tailTrace_1658972
  have hstable : (prefixWord ++ tailWord_1658972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658972).length < 2 ^ (prefixWord ++ tailWord_1658972).sum := by decide
  have hdescent : baseEnd_1658972 < baseStart_1658972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659018 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_1659018 : Nat := 118140960795 + 1659018 * 2 ^ 59
def prefixEnd_1659018 : Nat := 4983230072969 + 3 ^ 40 * 1659018 * 2
def baseEnd_1659018 : Nat := 851873648460895318145321

theorem tailTrace_1659018 : CollatzResearch.WordTrace tailWord_1659018 prefixEnd_1659018 851873648460895318145321 := by
  unfold tailWord_1659018
  simp only [CollatzResearch.WordTrace]
  refine ⟨15127339375917149640460427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40339571669112399041227805 15127339375917149640460427)
  ·
    refine ⟨22691009063875724460690641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15127339375917149640460427 22691009063875724460690641)
    ·
      refine ⟨17018256797906793345517981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22691009063875724460690641 17018256797906793345517981)
      ·
        refine ⟨6381846299215047504569243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17018256797906793345517981 6381846299215047504569243)
        ·
          refine ⟨9572769448822571256853865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6381846299215047504569243 9572769448822571256853865)
          ·
            refine ⟨7179577086616928442640399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9572769448822571256853865 7179577086616928442640399)
            ·
              refine ⟨10769365629925392663960599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7179577086616928442640399 10769365629925392663960599)
              ·
                refine ⟨16154048444888088995940899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10769365629925392663960599 16154048444888088995940899)
                ·
                  refine ⟨24231072667332133493911349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16154048444888088995940899 24231072667332133493911349)
                  ·
                    refine ⟨2271663062562387515054189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24231072667332133493911349 2271663062562387515054189)
                    ·
                      refine ⟨851873648460895318145321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2271663062562387515054189 851873648460895318145321)
                      ·
                        rfl

theorem cell23_1659018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_1659018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659018 prefixEnd_1659018 := by exact prefixLift 1659018
  have htrace : WordTrace (prefixWord ++ tailWord_1659018) baseStart_1659018 baseEnd_1659018 := by
    simpa [prefixWord, tailWord_1659018, baseEnd_1659018] using wordTrace_append hprefix tailTrace_1659018
  have hstable : (prefixWord ++ tailWord_1659018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659018).length < 2 ^ (prefixWord ++ tailWord_1659018).sum := by decide
  have hdescent : baseEnd_1659018 < baseStart_1659018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659042 : List Nat := [3, 3, 1, 3, 1, 2, 2, 3, 5]
def baseStart_1659042 : Nat := 118140960795 + 1659042 * 2 ^ 59
def prefixEnd_1659042 : Nat := 4983230072969 + 3 ^ 40 * 1659042 * 2
def baseEnd_1659042 : Nat := 94653996888511469360579

theorem tailTrace_1659042 : CollatzResearch.WordTrace tailWord_1659042 prefixEnd_1659042 94653996888511469360579 := by
  unfold tailWord_1659042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15127558213895412665178845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40340155237054433773810253 15127558213895412665178845)
  ·
    refine ⟨5672834330210779749442067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15127558213895412665178845 5672834330210779749442067)
    ·
      refine ⟨8509251495316169624163101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5672834330210779749442067 8509251495316169624163101)
      ·
        refine ⟨3190969310743563609061163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8509251495316169624163101 3190969310743563609061163)
        ·
          refine ⟨4786453966115345413591745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3190969310743563609061163 4786453966115345413591745)
          ·
            refine ⟨3589840474586509060193809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4786453966115345413591745 3589840474586509060193809)
            ·
              refine ⟨2692380355939881795145357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3589840474586509060193809 2692380355939881795145357)
              ·
                refine ⟨1009642633477455673179509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2692380355939881795145357 1009642633477455673179509)
                ·
                  refine ⟨94653996888511469360579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1009642633477455673179509 94653996888511469360579)
                  ·
                    rfl

theorem cell23_1659042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_1659042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659042 prefixEnd_1659042 := by exact prefixLift 1659042
  have htrace : WordTrace (prefixWord ++ tailWord_1659042) baseStart_1659042 baseEnd_1659042 := by
    simpa [prefixWord, tailWord_1659042, baseEnd_1659042] using wordTrace_append hprefix tailTrace_1659042
  have hstable : (prefixWord ++ tailWord_1659042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659042).length < 2 ^ (prefixWord ++ tailWord_1659042).sum := by decide
  have hdescent : baseEnd_1659042 < baseStart_1659042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659058 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_1659058 : Nat := 118140960795 + 1659058 * 2 ^ 59
def prefixEnd_1659058 : Nat := 4983230072969 + 3 ^ 40 * 1659058 * 2
def baseEnd_1659058 : Nat := 851894187687075161645137

theorem tailTrace_1659058 : CollatzResearch.WordTrace tailWord_1659058 prefixEnd_1659058 851894187687075161645137 := by
  unfold tailWord_1659058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15127704105880921348324457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40340544282349123595531885 15127704105880921348324457)
  ·
    refine ⟨11345778079410691011243343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15127704105880921348324457 11345778079410691011243343)
    ·
      refine ⟨17018667119116036516865015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11345778079410691011243343 17018667119116036516865015)
      ·
        refine ⟨25528000678674054775297523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17018667119116036516865015 25528000678674054775297523)
        ·
          refine ⟨38292001018011082162946285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25528000678674054775297523 38292001018011082162946285)
          ·
            refine ⟨14359500381754155811104857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38292001018011082162946285 14359500381754155811104857)
            ·
              refine ⟨10769625286315616858328643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14359500381754155811104857 10769625286315616858328643)
              ·
                refine ⟨16154437929473425287492965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10769625286315616858328643 16154437929473425287492965)
                ·
                  refine ⟨3028957111776267241404931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16154437929473425287492965 3028957111776267241404931)
                  ·
                    refine ⟨4543435667664400862107397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3028957111776267241404931 4543435667664400862107397)
                    ·
                      refine ⟨851894187687075161645137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4543435667664400862107397 851894187687075161645137)
                      ·
                        rfl

theorem cell23_1659058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_1659058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659058 prefixEnd_1659058 := by exact prefixLift 1659058
  have htrace : WordTrace (prefixWord ++ tailWord_1659058) baseStart_1659058 baseEnd_1659058 := by
    simpa [prefixWord, tailWord_1659058, baseEnd_1659058] using wordTrace_append hprefix tailTrace_1659058
  have hstable : (prefixWord ++ tailWord_1659058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659058).length < 2 ^ (prefixWord ++ tailWord_1659058).sum := by decide
  have hdescent : baseEnd_1659058 < baseStart_1659058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659071 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_1659071 : Nat := 118140960795 + 1659071 * 2 ^ 59
def prefixEnd_1659071 : Nat := 4983230072969 + 3 ^ 40 * 1659071 * 2
def baseEnd_1659071 : Nat := 851900862935583610782577

theorem tailTrace_1659071 : CollatzResearch.WordTrace tailWord_1659071 prefixEnd_1659071 851900862935583610782577 := by
  unfold tailWord_1659071
  simp only [CollatzResearch.WordTrace]
  refine ⟨60511290572476588613521067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40340860381651059075680711 60511290572476588613521067)
  ·
    refine ⟨90766935858714882920281601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60511290572476588613521067 90766935858714882920281601)
    ·
      refine ⟨68075201894036162190211201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90766935858714882920281601 68075201894036162190211201)
      ·
        refine ⟨51056401420527121642658401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68075201894036162190211201 51056401420527121642658401)
        ·
          refine ⟨38292301065395341231993801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51056401420527121642658401 38292301065395341231993801)
          ·
            refine ⟨28719225799046505923995351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38292301065395341231993801 28719225799046505923995351)
            ·
              refine ⟨43078838698569758885993027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28719225799046505923995351 43078838698569758885993027)
              ·
                refine ⟨64618258047854638328989541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43078838698569758885993027 64618258047854638328989541)
                ·
                  refine ⟨12115923383972744686685539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64618258047854638328989541 12115923383972744686685539)
                  ·
                    refine ⟨18173885075959117030028309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12115923383972744686685539 18173885075959117030028309)
                    ·
                      refine ⟨851900862935583610782577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18173885075959117030028309 851900862935583610782577)
                      ·
                        rfl

theorem cell23_1659071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_1659071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659071 prefixEnd_1659071 := by exact prefixLift 1659071
  have htrace : WordTrace (prefixWord ++ tailWord_1659071) baseStart_1659071 baseEnd_1659071 := by
    simpa [prefixWord, tailWord_1659071, baseEnd_1659071] using wordTrace_append hprefix tailTrace_1659071
  have hstable : (prefixWord ++ tailWord_1659071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659071).length < 2 ^ (prefixWord ++ tailWord_1659071).sum := by decide
  have hdescent : baseEnd_1659071 < baseStart_1659071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659119 : List Nat := [1, 1, 2, 1, 6, 2, 3, 2, 1, 4]
def baseStart_1659119 : Nat := 118140960795 + 1659119 * 2 ^ 59
def prefixEnd_1659119 : Nat := 4983230072969 + 3 ^ 40 * 1659119 * 2
def baseEnd_1659119 : Nat := 283975170002333140994119

theorem tailTrace_1659119 : CollatzResearch.WordTrace tailWord_1659119 prefixEnd_1659119 283975170002333140994119 := by
  unfold tailWord_1659119
  simp only [CollatzResearch.WordTrace]
  refine ⟨60513041276302692811268411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40342027517535128540845607 60513041276302692811268411)
  ·
    refine ⟨90769561914454039216902617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60513041276302692811268411 90769561914454039216902617)
    ·
      refine ⟨68077171435840529412676963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90769561914454039216902617 68077171435840529412676963)
      ·
        refine ⟨102115757153760794119015445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68077171435840529412676963 102115757153760794119015445)
        ·
          refine ⟨4786676116582537224328849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102115757153760794119015445 4786676116582537224328849)
          ·
            refine ⟨3590007087436902918246637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4786676116582537224328849 3590007087436902918246637)
            ·
              refine ⟨1346252657788838594342489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3590007087436902918246637 1346252657788838594342489)
              ·
                refine ⟨1009689493341628945756867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346252657788838594342489 1009689493341628945756867)
                ·
                  refine ⟨1514534240012443418635301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009689493341628945756867 1514534240012443418635301)
                  ·
                    refine ⟨283975170002333140994119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1514534240012443418635301 283975170002333140994119)
                    ·
                      rfl

theorem cell23_1659119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 1, 4].length) (baseStart_1659119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659119 prefixEnd_1659119 := by exact prefixLift 1659119
  have htrace : WordTrace (prefixWord ++ tailWord_1659119) baseStart_1659119 baseEnd_1659119 := by
    simpa [prefixWord, tailWord_1659119, baseEnd_1659119] using wordTrace_append hprefix tailTrace_1659119
  have hstable : (prefixWord ++ tailWord_1659119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659119).length < 2 ^ (prefixWord ++ tailWord_1659119).sum := by decide
  have hdescent : baseEnd_1659119 < baseStart_1659119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659131 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 10]
def baseStart_1659131 : Nat := 118140960795 + 1659131 * 2 ^ 59
def prefixEnd_1659131 : Nat := 4983230072969 + 3 ^ 40 * 1659131 * 2
def baseEnd_1659131 : Nat := 851931671774853376032301

theorem tailTrace_1659131 : CollatzResearch.WordTrace tailWord_1659131 prefixEnd_1659131 851931671774853376032301 := by
  unfold tailWord_1659131
  simp only [CollatzResearch.WordTrace]
  refine ⟨60513478952259218860705247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40342319301506145907136831 60513478952259218860705247)
  ·
    refine ⟨90770218428388828291057871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60513478952259218860705247 90770218428388828291057871)
    ·
      refine ⟨136155327642583242436586807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90770218428388828291057871 136155327642583242436586807)
      ·
        refine ⟨204232991463874863654880211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136155327642583242436586807 204232991463874863654880211)
        ·
          refine ⟨306349487195812295482320317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204232991463874863654880211 306349487195812295482320317)
          ·
            refine ⟨114881057698429610805870119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306349487195812295482320317 114881057698429610805870119)
            ·
              refine ⟨172321586547644416208805179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114881057698429610805870119 172321586547644416208805179)
              ·
                refine ⟨258482379821466624313207769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172321586547644416208805179 258482379821466624313207769)
                ·
                  refine ⟨193861784866099968234905827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258482379821466624313207769 193861784866099968234905827)
                  ·
                    refine ⟨290792677299149952352358741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193861784866099968234905827 290792677299149952352358741)
                    ·
                      refine ⟨851931671774853376032301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 290792677299149952352358741 851931671774853376032301)
                      ·
                        rfl

theorem cell23_1659131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_1659131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659131 prefixEnd_1659131 := by exact prefixLift 1659131
  have htrace : WordTrace (prefixWord ++ tailWord_1659131) baseStart_1659131 baseEnd_1659131 := by
    simpa [prefixWord, tailWord_1659131, baseEnd_1659131] using wordTrace_append hprefix tailTrace_1659131
  have hstable : (prefixWord ++ tailWord_1659131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659131).length < 2 ^ (prefixWord ++ tailWord_1659131).sum := by decide
  have hdescent : baseEnd_1659131 < baseStart_1659131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659132 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 6]
def baseStart_1659132 : Nat := 118140960795 + 1659132 * 2 ^ 59
def prefixEnd_1659132 : Nat := 4983230072969 + 3 ^ 40 * 1659132 * 2
def baseEnd_1659132 : Nat := 94659131695056430235533

theorem tailTrace_1659132 : CollatzResearch.WordTrace tailWord_1659132 prefixEnd_1659132 94659131695056430235533 := by
  unfold tailWord_1659132
  simp only [CollatzResearch.WordTrace]
  refine ⟨30256757712627798015745825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40342343616837064020994433 30256757712627798015745825)
  ·
    refine ⟨22692568284470848511809369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30256757712627798015745825 22692568284470848511809369)
    ·
      refine ⟨17019426213353136383857027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22692568284470848511809369 17019426213353136383857027)
      ·
        refine ⟨25529139320029704575785541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17019426213353136383857027 25529139320029704575785541)
        ·
          refine ⟨4786713622505569607959789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25529139320029704575785541 4786713622505569607959789)
          ·
            refine ⟨1795017608439588602984921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4786713622505569607959789 1795017608439588602984921)
            ·
              refine ⟨1346263206329691452238691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795017608439588602984921 1346263206329691452238691)
              ·
                refine ⟨2019394809494537178358037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346263206329691452238691 2019394809494537178358037)
                ·
                  refine ⟨94659131695056430235533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2019394809494537178358037 94659131695056430235533)
                  ·
                    rfl

theorem cell23_1659132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_1659132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659132 prefixEnd_1659132 := by exact prefixLift 1659132
  have htrace : WordTrace (prefixWord ++ tailWord_1659132) baseStart_1659132 baseEnd_1659132 := by
    simpa [prefixWord, tailWord_1659132, baseEnd_1659132] using wordTrace_append hprefix tailTrace_1659132
  have hstable : (prefixWord ++ tailWord_1659132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659132).length < 2 ^ (prefixWord ++ tailWord_1659132).sum := by decide
  have hdescent : baseEnd_1659132 < baseStart_1659132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659135 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 4, 3, 2]
def baseStart_1659135 : Nat := 118140960795 + 1659135 * 2 ^ 59
def prefixEnd_1659135 : Nat := 4983230072969 + 3 ^ 40 * 1659135 * 2
def baseEnd_1659135 : Nat := 851933725697471360382283

theorem tailTrace_1659135 : CollatzResearch.WordTrace tailWord_1659135 prefixEnd_1659135 851933725697471360382283 := by
  unfold tailWord_1659135
  simp only [CollatzResearch.WordTrace]
  refine ⟨60513624844244727543850859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40342416562829818362567239 60513624844244727543850859)
  ·
    refine ⟨90770437266367091315776289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60513624844244727543850859 90770437266367091315776289)
    ·
      refine ⟨68077827949775318486832217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90770437266367091315776289 68077827949775318486832217)
      ·
        refine ⟨51058370962331488865124163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68077827949775318486832217 51058370962331488865124163)
        ·
          refine ⟨76587556443497233297686245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51058370962331488865124163 76587556443497233297686245)
          ·
            refine ⟨14360166833155731243316171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76587556443497233297686245 14360166833155731243316171)
            ·
              refine ⟨21540250249733596864974257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14360166833155731243316171 21540250249733596864974257)
              ·
                refine ⟨16155187687300197648730693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21540250249733596864974257 16155187687300197648730693)
                ·
                  refine ⟨3029097691368787059137005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16155187687300197648730693 3029097691368787059137005)
                  ·
                    refine ⟨1135911634263295147176377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029097691368787059137005 1135911634263295147176377)
                    ·
                      refine ⟨851933725697471360382283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135911634263295147176377 851933725697471360382283)
                      ·
                        rfl

theorem cell23_1659135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 3, 2].length) (baseStart_1659135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659135 prefixEnd_1659135 := by exact prefixLift 1659135
  have htrace : WordTrace (prefixWord ++ tailWord_1659135) baseStart_1659135 baseEnd_1659135 := by
    simpa [prefixWord, tailWord_1659135, baseEnd_1659135] using wordTrace_append hprefix tailTrace_1659135
  have hstable : (prefixWord ++ tailWord_1659135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659135).length < 2 ^ (prefixWord ++ tailWord_1659135).sum := by decide
  have hdescent : baseEnd_1659135 < baseStart_1659135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659145 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 1, 5]
def baseStart_1659145 : Nat := 118140960795 + 1659145 * 2 ^ 59
def prefixEnd_1659145 : Nat := 4983230072969 + 3 ^ 40 * 1659145 * 2
def baseEnd_1659145 : Nat := 283979620168005440419079

theorem tailTrace_1659145 : CollatzResearch.WordTrace tailWord_1659145 prefixEnd_1659145 283979620168005440419079 := by
  unfold tailWord_1659145
  simp only [CollatzResearch.WordTrace]
  refine ⟨60513989574208499251714889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40342659716138999501143259 60513989574208499251714889)
  ·
    refine ⟨45385492180656374438786167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60513989574208499251714889 45385492180656374438786167)
    ·
      refine ⟨68078238270984561658179251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45385492180656374438786167 68078238270984561658179251)
      ·
        refine ⟨102117357406476842487268877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68078238270984561658179251 102117357406476842487268877)
        ·
          refine ⟨38294009027428815932725829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102117357406476842487268877 38294009027428815932725829)
          ·
            refine ⟨7180126692642902987386093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38294009027428815932725829 7180126692642902987386093)
            ·
              refine ⟨2692547509741088620269785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7180126692642902987386093 2692547509741088620269785)
              ·
                refine ⟨2019410632305816465202339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2692547509741088620269785 2019410632305816465202339)
                ·
                  refine ⟨3029115948458724697803509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019410632305816465202339 3029115948458724697803509)
                  ·
                    refine ⟨283979620168005440419079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3029115948458724697803509 283979620168005440419079)
                    ·
                      rfl

theorem cell23_1659145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 5].length) (baseStart_1659145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659145 prefixEnd_1659145 := by exact prefixLift 1659145
  have htrace : WordTrace (prefixWord ++ tailWord_1659145) baseStart_1659145 baseEnd_1659145 := by
    simpa [prefixWord, tailWord_1659145, baseEnd_1659145] using wordTrace_append hprefix tailTrace_1659145
  have hstable : (prefixWord ++ tailWord_1659145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659145).length < 2 ^ (prefixWord ++ tailWord_1659145).sum := by decide
  have hdescent : baseEnd_1659145 < baseStart_1659145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659176 : List Nat := [2, 1, 5, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_1659176 : Nat := 118140960795 + 1659176 * 2 ^ 59
def prefixEnd_1659176 : Nat := 4983230072969 + 3 ^ 40 * 1659176 * 2
def baseEnd_1659176 : Nat := 851954778404305699969595

theorem tailTrace_1659176 : CollatzResearch.WordTrace tailWord_1659176 prefixEnd_1659176 851954778404305699969595 := by
  unfold tailWord_1659176
  simp only [CollatzResearch.WordTrace]
  refine ⟨30257560118548095773046691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40343413491397461030728921 30257560118548095773046691)
  ·
    refine ⟨45386340177822143659570037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30257560118548095773046691 45386340177822143659570037)
    ·
      refine ⟨4254969391670825968084691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45386340177822143659570037 4254969391670825968084691)
      ·
        refine ⟨6382454087506238952127037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254969391670825968084691 6382454087506238952127037)
        ·
          refine ⟨2393420282814839607047639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6382454087506238952127037 2393420282814839607047639)
          ·
            refine ⟨3590130424222259410571459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393420282814839607047639 3590130424222259410571459)
            ·
              refine ⟨5385195636333389115857189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590130424222259410571459 5385195636333389115857189)
              ·
                refine ⟨1009724181812510459223223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5385195636333389115857189 1009724181812510459223223)
                ·
                  refine ⟨1514586272718765688834835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009724181812510459223223 1514586272718765688834835)
                  ·
                    refine ⟨2271879409078148533252253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1514586272718765688834835 2271879409078148533252253)
                    ·
                      refine ⟨851954778404305699969595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2271879409078148533252253 851954778404305699969595)
                      ·
                        rfl

theorem cell23_1659176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_1659176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659176 prefixEnd_1659176 := by exact prefixLift 1659176
  have htrace : WordTrace (prefixWord ++ tailWord_1659176) baseStart_1659176 baseEnd_1659176 := by
    simpa [prefixWord, tailWord_1659176, baseEnd_1659176] using wordTrace_append hprefix tailTrace_1659176
  have hstable : (prefixWord ++ tailWord_1659176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659176).length < 2 ^ (prefixWord ++ tailWord_1659176).sum := by decide
  have hdescent : baseEnd_1659176 < baseStart_1659176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659216 : List Nat := [2, 1, 1, 1, 1, 7, 2, 3, 1, 2, 2]
def baseStart_1659216 : Nat := 118140960795 + 1659216 * 2 ^ 59
def prefixEnd_1659216 : Nat := 4983230072969 + 3 ^ 40 * 1659216 * 2
def baseEnd_1659216 : Nat := 851975317630485543469411

theorem tailTrace_1659216 : CollatzResearch.WordTrace tailWord_1659216 prefixEnd_1659216 851975317630485543469411 := by
  unfold tailWord_1659216
  simp only [CollatzResearch.WordTrace]
  refine ⟨30258289578475639188774751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40344386104634185585033001 30258289578475639188774751)
  ·
    refine ⟨45387434367713458783162127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30258289578475639188774751 45387434367713458783162127)
    ·
      refine ⟨68081151551570188174743191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45387434367713458783162127 68081151551570188174743191)
      ·
        refine ⟨102121727327355282262114787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68081151551570188174743191 102121727327355282262114787)
        ·
          refine ⟨153182590991032923393172181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102121727327355282262114787 153182590991032923393172181)
          ·
            refine ⟨3590216976352334142027473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 153182590991032923393172181 3590216976352334142027473)
            ·
              refine ⟨2692662732264250606520605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3590216976352334142027473 2692662732264250606520605)
              ·
                refine ⟨1009748524599093977445227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2692662732264250606520605 1009748524599093977445227)
                ·
                  refine ⟨1514622786898640966167841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009748524599093977445227 1514622786898640966167841)
                  ·
                    refine ⟨1135967090173980724625881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1514622786898640966167841 1135967090173980724625881)
                    ·
                      refine ⟨851975317630485543469411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135967090173980724625881 851975317630485543469411)
                      ·
                        rfl

theorem cell23_1659216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 1, 2, 2].length) (baseStart_1659216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659216 prefixEnd_1659216 := by exact prefixLift 1659216
  have htrace : WordTrace (prefixWord ++ tailWord_1659216) baseStart_1659216 baseEnd_1659216 := by
    simpa [prefixWord, tailWord_1659216, baseEnd_1659216] using wordTrace_append hprefix tailTrace_1659216
  have hstable : (prefixWord ++ tailWord_1659216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659216).length < 2 ^ (prefixWord ++ tailWord_1659216).sum := by decide
  have hdescent : baseEnd_1659216 < baseStart_1659216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659259 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 1, 3, 2]
def baseStart_1659259 : Nat := 118140960795 + 1659259 * 2 ^ 59
def prefixEnd_1659259 : Nat := 4983230072969 + 3 ^ 40 * 1659259 * 2
def baseEnd_1659259 : Nat := 851997397298628875231713

theorem tailTrace_1659259 : CollatzResearch.WordTrace tailWord_1659259 prefixEnd_1659259 851997397298628875231713 := by
  unfold tailWord_1659259
  simp only [CollatzResearch.WordTrace]
  refine ⟨60518147495795496721364831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40345431663863664480909887 60518147495795496721364831)
  ·
    refine ⟨90777221243693245082047247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60518147495795496721364831 90777221243693245082047247)
    ·
      refine ⟨136165831865539867623070871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90777221243693245082047247 136165831865539867623070871)
      ·
        refine ⟨204248747798309801434606307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136165831865539867623070871 204248747798309801434606307)
        ·
          refine ⟨306373121697464702151909461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204248747798309801434606307 306373121697464702151909461)
          ·
            refine ⟨3590310019892164478342689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 306373121697464702151909461 3590310019892164478342689)
            ·
              refine ⟨2692732514919123358757017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3590310019892164478342689 2692732514919123358757017)
              ·
                refine ⟨2019549386189342519067763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2692732514919123358757017 2019549386189342519067763)
                ·
                  refine ⟨3029324079284013778601645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019549386189342519067763 3029324079284013778601645)
                  ·
                    refine ⟨1135996529731505166975617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029324079284013778601645 1135996529731505166975617)
                    ·
                      refine ⟨851997397298628875231713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1135996529731505166975617 851997397298628875231713)
                      ·
                        rfl

theorem cell23_1659259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 3, 2].length) (baseStart_1659259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659259 prefixEnd_1659259 := by exact prefixLift 1659259
  have htrace : WordTrace (prefixWord ++ tailWord_1659259) baseStart_1659259 baseEnd_1659259 := by
    simpa [prefixWord, tailWord_1659259, baseEnd_1659259] using wordTrace_append hprefix tailTrace_1659259
  have hstable : (prefixWord ++ tailWord_1659259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659259).length < 2 ^ (prefixWord ++ tailWord_1659259).sum := by decide
  have hdescent : baseEnd_1659259 < baseStart_1659259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659272 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 3, 4, 2]
def baseStart_1659272 : Nat := 118140960795 + 1659272 * 2 ^ 59
def prefixEnd_1659272 : Nat := 4983230072969 + 3 ^ 40 * 1659272 * 2
def baseEnd_1659272 : Nat := 852004072547137324369153

theorem tailTrace_1659272 : CollatzResearch.WordTrace tailWord_1659272 prefixEnd_1659272 852004072547137324369153 := by
  unfold tailWord_1659272
  simp only [CollatzResearch.WordTrace]
  refine ⟨30259310822374199970794035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40345747763165599961058713 30259310822374199970794035)
  ·
    refine ⟨45388966233561299956191053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30259310822374199970794035 45388966233561299956191053)
    ·
      refine ⟨17020862337585487483571645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45388966233561299956191053 17020862337585487483571645)
      ·
        refine ⟨6382823376594557806339367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17020862337585487483571645 6382823376594557806339367)
        ·
          refine ⟨9574235064891836709509051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6382823376594557806339367 9574235064891836709509051)
          ·
            refine ⟨14361352597337755064263577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9574235064891836709509051 14361352597337755064263577)
            ·
              refine ⟨10771014448003316298197683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14361352597337755064263577 10771014448003316298197683)
              ·
                refine ⟨16156521672004974447296525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10771014448003316298197683 16156521672004974447296525)
                ·
                  refine ⟨6058695627001865417736197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16156521672004974447296525 6058695627001865417736197)
                  ·
                    refine ⟨1136005430062849765825537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6058695627001865417736197 1136005430062849765825537)
                    ·
                      refine ⟨852004072547137324369153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1136005430062849765825537 852004072547137324369153)
                      ·
                        rfl

theorem cell23_1659272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_1659272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659272 prefixEnd_1659272 := by exact prefixLift 1659272
  have htrace : WordTrace (prefixWord ++ tailWord_1659272) baseStart_1659272 baseEnd_1659272 := by
    simpa [prefixWord, tailWord_1659272, baseEnd_1659272] using wordTrace_append hprefix tailTrace_1659272
  have hstable : (prefixWord ++ tailWord_1659272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659272).length < 2 ^ (prefixWord ++ tailWord_1659272).sum := by decide
  have hdescent : baseEnd_1659272 < baseStart_1659272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659275 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 5]
def baseStart_1659275 : Nat := 118140960795 + 1659275 * 2 ^ 59
def prefixEnd_1659275 : Nat := 4983230072969 + 3 ^ 40 * 1659275 * 2
def baseEnd_1659275 : Nat := 852005612989100812631639

theorem tailTrace_1659275 : CollatzResearch.WordTrace tailWord_1659275 prefixEnd_1659275 852005612989100812631639 := by
  unfold tailWord_1659275
  simp only [CollatzResearch.WordTrace]
  refine ⟨60518731063737531453947279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40345820709158354302631519 60518731063737531453947279)
  ·
    refine ⟨90778096595606297180920919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60518731063737531453947279 90778096595606297180920919)
    ·
      refine ⟨136167144893409445771381379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90778096595606297180920919 136167144893409445771381379)
      ·
        refine ⟨204250717340114168657072069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136167144893409445771381379 204250717340114168657072069)
        ·
          refine ⟨38297009501271406623201013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204250717340114168657072069 38297009501271406623201013)
          ·
            refine ⟨3590344640744194370925095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38297009501271406623201013 3590344640744194370925095)
            ·
              refine ⟨5385516961116291556387643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590344640744194370925095 5385516961116291556387643)
              ·
                refine ⟨8078275441674437334581465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385516961116291556387643 8078275441674437334581465)
                ·
                  refine ⟨6058706581255828000936099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8078275441674437334581465 6058706581255828000936099)
                  ·
                    refine ⟨9088059871883742001404149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6058706581255828000936099 9088059871883742001404149)
                    ·
                      refine ⟨852005612989100812631639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9088059871883742001404149 852005612989100812631639)
                      ·
                        rfl

theorem cell23_1659275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 5].length) (baseStart_1659275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659275 prefixEnd_1659275 := by exact prefixLift 1659275
  have htrace : WordTrace (prefixWord ++ tailWord_1659275) baseStart_1659275 baseEnd_1659275 := by
    simpa [prefixWord, tailWord_1659275, baseEnd_1659275] using wordTrace_append hprefix tailTrace_1659275
  have hstable : (prefixWord ++ tailWord_1659275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659275).length < 2 ^ (prefixWord ++ tailWord_1659275).sum := by decide
  have hdescent : baseEnd_1659275 < baseStart_1659275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659289 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 2, 2, 2]
def baseStart_1659289 : Nat := 118140960795 + 1659289 * 2 ^ 59
def prefixEnd_1659289 : Nat := 4983230072969 + 3 ^ 40 * 1659289 * 2
def baseEnd_1659289 : Nat := 852012801718263757856575

theorem tailTrace_1659289 : CollatzResearch.WordTrace tailWord_1659289 prefixEnd_1659289 852012801718263757856575 := by
  unfold tailWord_1659289
  simp only [CollatzResearch.WordTrace]
  refine ⟨60519241685686811844956921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40346161123791207896637947 60519241685686811844956921)
  ·
    refine ⟨45389431264265108883717691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60519241685686811844956921 45389431264265108883717691)
    ·
      refine ⟨68084146896397663325576537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45389431264265108883717691 68084146896397663325576537)
      ·
        refine ⟨51063110172298247494182403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68084146896397663325576537 51063110172298247494182403)
        ·
          refine ⟨76594665258447371241273605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51063110172298247494182403 76594665258447371241273605)
          ·
            refine ⟨14361499735958882107738801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76594665258447371241273605 14361499735958882107738801)
            ·
              refine ⟨10771124801969161580804101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14361499735958882107738801 10771124801969161580804101)
              ·
                refine ⟨2019585900369217796400769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10771124801969161580804101 2019585900369217796400769)
                ·
                  refine ⟨1514689425276913347300577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2019585900369217796400769 1514689425276913347300577)
                  ·
                    refine ⟨1136017068957685010475433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1514689425276913347300577 1136017068957685010475433)
                    ·
                      refine ⟨852012801718263757856575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1136017068957685010475433 852012801718263757856575)
                      ·
                        rfl

theorem cell23_1659289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 2, 2].length) (baseStart_1659289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659289 prefixEnd_1659289 := by exact prefixLift 1659289
  have htrace : WordTrace (prefixWord ++ tailWord_1659289) baseStart_1659289 baseEnd_1659289 := by
    simpa [prefixWord, tailWord_1659289, baseEnd_1659289] using wordTrace_append hprefix tailTrace_1659289
  have hstable : (prefixWord ++ tailWord_1659289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659289).length < 2 ^ (prefixWord ++ tailWord_1659289).sum := by decide
  have hdescent : baseEnd_1659289 < baseStart_1659289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659305 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 2, 3, 3]
def baseStart_1659305 : Nat := 118140960795 + 1659305 * 2 ^ 59
def prefixEnd_1659305 : Nat := 4983230072969 + 3 ^ 40 * 1659305 * 2
def baseEnd_1659305 : Nat := 852021017408735695256501

theorem tailTrace_1659305 : CollatzResearch.WordTrace tailWord_1659305 prefixEnd_1659305 852021017408735695256501 := by
  unfold tailWord_1659305
  simp only [CollatzResearch.WordTrace]
  refine ⟨60519825253628846577539369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40346550169085897718359579 60519825253628846577539369)
  ·
    refine ⟨45389868940221634933154527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60519825253628846577539369 45389868940221634933154527)
    ·
      refine ⟨68084803410332452399731791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45389868940221634933154527 68084803410332452399731791)
      ·
        refine ⟨102127205115498678599597687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68084803410332452399731791 102127205115498678599597687)
        ·
          refine ⟨153190807673248017899396531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102127205115498678599597687 153190807673248017899396531)
          ·
            refine ⟨229786211509872026849094797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153190807673248017899396531 229786211509872026849094797)
            ·
              refine ⟨86169829316202010068410549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229786211509872026849094797 86169829316202010068410549)
              ·
                refine ⟨8078421498393938443913489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86169829316202010068410549 8078421498393938443913489)
                ·
                  refine ⟨6058816123795453832935117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8078421498393938443913489 6058816123795453832935117)
                  ·
                    refine ⟨2272056046423295187350669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6058816123795453832935117 2272056046423295187350669)
                    ·
                      refine ⟨852021017408735695256501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2272056046423295187350669 852021017408735695256501)
                      ·
                        rfl

theorem cell23_1659305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3, 3].length) (baseStart_1659305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659305 prefixEnd_1659305 := by exact prefixLift 1659305
  have htrace : WordTrace (prefixWord ++ tailWord_1659305) baseStart_1659305 baseEnd_1659305 := by
    simpa [prefixWord, tailWord_1659305, baseEnd_1659305] using wordTrace_append hprefix tailTrace_1659305
  have hstable : (prefixWord ++ tailWord_1659305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659305).length < 2 ^ (prefixWord ++ tailWord_1659305).sum := by decide
  have hdescent : baseEnd_1659305 < baseStart_1659305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659335 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_1659335 : Nat := 118140960795 + 1659335 * 2 ^ 59
def prefixEnd_1659335 : Nat := 4983230072969 + 3 ^ 40 * 1659335 * 2
def baseEnd_1659335 : Nat := 852036421828370577881363

theorem tailTrace_1659335 : CollatzResearch.WordTrace tailWord_1659335 prefixEnd_1659335 852036421828370577881363 := by
  unfold tailWord_1659335
  simp only [CollatzResearch.WordTrace]
  refine ⟨60520919443520161701131459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40347279629013441134087639 60520919443520161701131459)
  ·
    refine ⟨90781379165280242551697189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60520919443520161701131459 90781379165280242551697189)
    ·
      refine ⟨17021508593490045478443223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90781379165280242551697189 17021508593490045478443223)
      ·
        refine ⟨25532262890235068217664835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17021508593490045478443223 25532262890235068217664835)
        ·
          refine ⟨38298394335352602326497253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25532262890235068217664835 38298394335352602326497253)
          ·
            refine ⟨7180948937878612936218235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38298394335352602326497253 7180948937878612936218235)
            ·
              refine ⟨10771423406817919404327353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7180948937878612936218235 10771423406817919404327353)
              ·
                refine ⟨8078567555113439553245515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10771423406817919404327353 8078567555113439553245515)
                ·
                  refine ⟨12117851332670159329868273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8078567555113439553245515 12117851332670159329868273)
                  ·
                    refine ⟨9088388499502619497401205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12117851332670159329868273 9088388499502619497401205)
                    ·
                      refine ⟨852036421828370577881363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9088388499502619497401205 852036421828370577881363)
                      ·
                        rfl

theorem cell23_1659335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_1659335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659335 prefixEnd_1659335 := by exact prefixLift 1659335
  have htrace : WordTrace (prefixWord ++ tailWord_1659335) baseStart_1659335 baseEnd_1659335 := by
    simpa [prefixWord, tailWord_1659335, baseEnd_1659335] using wordTrace_append hprefix tailTrace_1659335
  have hstable : (prefixWord ++ tailWord_1659335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659335).length < 2 ^ (prefixWord ++ tailWord_1659335).sum := by decide
  have hdescent : baseEnd_1659335 < baseStart_1659335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659346 : List Nat := [3, 2, 2, 4, 1, 1, 1, 4, 5]
def baseStart_1659346 : Nat := 118140960795 + 1659346 * 2 ^ 59
def prefixEnd_1659346 : Nat := 4983230072969 + 3 ^ 40 * 1659346 * 2
def baseEnd_1659346 : Nat := 94671341123952226093757

theorem tailTrace_1659346 : CollatzResearch.WordTrace tailWord_1659346 prefixEnd_1659346 94671341123952226093757 := by
  unfold tailWord_1659346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15130330161620077644945473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40347547097653540386521261 15130330161620077644945473)
  ·
    refine ⟨11347747621215058233709105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15130330161620077644945473 11347747621215058233709105)
    ·
      refine ⟨8510810715911293675281829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11347747621215058233709105 8510810715911293675281829)
      ·
        refine ⟨1595777009233367564115343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8510810715911293675281829 1595777009233367564115343)
        ·
          refine ⟨2393665513850051346173015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595777009233367564115343 2393665513850051346173015)
          ·
            refine ⟨3590498270775077019259523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393665513850051346173015 3590498270775077019259523)
            ·
              refine ⟨5385747406162615528889285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590498270775077019259523 5385747406162615528889285)
              ·
                refine ⟨1009827638655490411666741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5385747406162615528889285 1009827638655490411666741)
                ·
                  refine ⟨94671341123952226093757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1009827638655490411666741 94671341123952226093757)
                  ·
                    rfl

theorem cell23_1659346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_1659346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659346 prefixEnd_1659346 := by exact prefixLift 1659346
  have htrace : WordTrace (prefixWord ++ tailWord_1659346) baseStart_1659346 baseEnd_1659346 := by
    simpa [prefixWord, tailWord_1659346, baseEnd_1659346] using wordTrace_append hprefix tailTrace_1659346
  have hstable : (prefixWord ++ tailWord_1659346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659346).length < 2 ^ (prefixWord ++ tailWord_1659346).sum := by decide
  have hdescent : baseEnd_1659346 < baseStart_1659346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659372 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 3, 4]
def baseStart_1659372 : Nat := 118140960795 + 1659372 * 2 ^ 59
def prefixEnd_1659372 : Nat := 4983230072969 + 3 ^ 40 * 1659372 * 2
def baseEnd_1659372 : Nat := 284018473537528977706231

theorem tailTrace_1659372 : CollatzResearch.WordTrace tailWord_1659372 prefixEnd_1659372 284018473537528977706231 := by
  unfold tailWord_1659372
  simp only [CollatzResearch.WordTrace]
  refine ⟨30261134472193058510114185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40348179296257411346818913 30261134472193058510114185)
  ·
    refine ⟨22695850854144793882585639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30261134472193058510114185 22695850854144793882585639)
    ·
      refine ⟨34043776281217190823878459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22695850854144793882585639 34043776281217190823878459)
      ·
        refine ⟨51065664421825786235817689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34043776281217190823878459 51065664421825786235817689)
        ·
          refine ⟨38299248316369339676863267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51065664421825786235817689 38299248316369339676863267)
          ·
            refine ⟨57448872474554009515294901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38299248316369339676863267 57448872474554009515294901)
            ·
              refine ⟨5385831794489438392058897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57448872474554009515294901 5385831794489438392058897)
              ·
                refine ⟨4039373845867078794044173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5385831794489438392058897 4039373845867078794044173)
                ·
                  refine ⟨1514765192200154547766565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4039373845867078794044173 1514765192200154547766565)
                  ·
                    refine ⟨284018473537528977706231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1514765192200154547766565 284018473537528977706231)
                    ·
                      rfl

theorem cell23_1659372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_1659372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659372 prefixEnd_1659372 := by exact prefixLift 1659372
  have htrace : WordTrace (prefixWord ++ tailWord_1659372) baseStart_1659372 baseEnd_1659372 := by
    simpa [prefixWord, tailWord_1659372, baseEnd_1659372] using wordTrace_append hprefix tailTrace_1659372
  have hstable : (prefixWord ++ tailWord_1659372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659372).length < 2 ^ (prefixWord ++ tailWord_1659372).sum := by decide
  have hdescent : baseEnd_1659372 < baseStart_1659372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659406 : List Nat := [4, 1, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_1659406 : Nat := 118140960795 + 1659406 * 2 ^ 59
def prefixEnd_1659406 : Nat := 4983230072969 + 3 ^ 40 * 1659406 * 2
def baseEnd_1659406 : Nat := 284024292984946600031179

theorem tailTrace_1659406 : CollatzResearch.WordTrace tailWord_1659406 prefixEnd_1659406 284024292984946600031179 := by
  unfold tailWord_1659406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7565438628282867603370759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40349006017508627217977381 7565438628282867603370759)
  ·
    refine ⟨11348157942424301405056139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7565438628282867603370759 11348157942424301405056139)
    ·
      refine ⟨17022236913636452107584209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11348157942424301405056139 17022236913636452107584209)
      ·
        refine ⟨12766677685227339080688157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17022236913636452107584209 12766677685227339080688157)
        ·
          refine ⟨4787504131960252155258059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12766677685227339080688157 4787504131960252155258059)
          ·
            refine ⟨7181256197940378232887089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787504131960252155258059 7181256197940378232887089)
            ·
              refine ⟨5385942148455283674665317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7181256197940378232887089 5385942148455283674665317)
              ·
                refine ⟨1009864152835365688999747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5385942148455283674665317 1009864152835365688999747)
                ·
                  refine ⟨1514796229253048533499621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009864152835365688999747 1514796229253048533499621)
                  ·
                    refine ⟨284024292984946600031179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1514796229253048533499621 284024292984946600031179)
                    ·
                      rfl

theorem cell23_1659406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_1659406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659406 prefixEnd_1659406 := by exact prefixLift 1659406
  have htrace : WordTrace (prefixWord ++ tailWord_1659406) baseStart_1659406 baseEnd_1659406 := by
    simpa [prefixWord, tailWord_1659406, baseEnd_1659406] using wordTrace_append hprefix tailTrace_1659406
  have hstable : (prefixWord ++ tailWord_1659406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659406).length < 2 ^ (prefixWord ++ tailWord_1659406).sum := by decide
  have hdescent : baseEnd_1659406 < baseStart_1659406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659429 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 3, 1, 3]
def baseStart_1659429 : Nat := 118140960795 + 1659429 * 2 ^ 59
def prefixEnd_1659429 : Nat := 4983230072969 + 3 ^ 40 * 1659429 * 2
def baseEnd_1659429 : Nat := 852084689009893210105931

theorem tailTrace_1659429 : CollatzResearch.WordTrace tailWord_1659429 prefixEnd_1659429 852084689009893210105931 := by
  unfold tailWord_1659429
  simp only [CollatzResearch.WordTrace]
  refine ⟨60524347905179615755053341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40349565270119743836702227 60524347905179615755053341)
  ·
    refine ⟨22696630464442355908145003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60524347905179615755053341 22696630464442355908145003)
    ·
      refine ⟨34044945696663533862217505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22696630464442355908145003 34044945696663533862217505)
      ·
        refine ⟨25533709272497650396663129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34044945696663533862217505 25533709272497650396663129)
        ·
          refine ⟨19150281954373237797497347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25533709272497650396663129 19150281954373237797497347)
          ·
            refine ⟨28725422931559856696246021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19150281954373237797497347 28725422931559856696246021)
            ·
              refine ⟨5386016799667473130546129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28725422931559856696246021 5386016799667473130546129)
              ·
                refine ⟨4039512599750604847909597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5386016799667473130546129 4039512599750604847909597)
                ·
                  refine ⟨1514817224906476817966099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4039512599750604847909597 1514817224906476817966099)
                  ·
                    refine ⟨2272225837359715226949149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1514817224906476817966099 2272225837359715226949149)
                    ·
                      refine ⟨852084689009893210105931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2272225837359715226949149 852084689009893210105931)
                      ·
                        rfl

theorem cell23_1659429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_1659429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659429 prefixEnd_1659429 := by exact prefixLift 1659429
  have htrace : WordTrace (prefixWord ++ tailWord_1659429) baseStart_1659429 baseEnd_1659429 := by
    simpa [prefixWord, tailWord_1659429, baseEnd_1659429] using wordTrace_append hprefix tailTrace_1659429
  have hstable : (prefixWord ++ tailWord_1659429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659429).length < 2 ^ (prefixWord ++ tailWord_1659429).sum := by decide
  have hdescent : baseEnd_1659429 < baseStart_1659429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659435 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 4]
def baseStart_1659435 : Nat := 118140960795 + 1659435 * 2 ^ 59
def prefixEnd_1659435 : Nat := 4983230072969 + 3 ^ 40 * 1659435 * 2
def baseEnd_1659435 : Nat := 852087769893820186630903

theorem tailTrace_1659435 : CollatzResearch.WordTrace tailWord_1659435 prefixEnd_1659435 852087769893820186630903 := by
  unfold tailWord_1659435
  simp only [CollatzResearch.WordTrace]
  refine ⟨60524566743157878779771759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40349711162105252519847839 60524566743157878779771759)
  ·
    refine ⟨90786850114736818169657639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60524566743157878779771759 90786850114736818169657639)
    ·
      refine ⟨136180275172105227254486459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90786850114736818169657639 136180275172105227254486459)
      ·
        refine ⟨204270412758157840881729689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136180275172105227254486459 204270412758157840881729689)
        ·
          refine ⟨153202809568618380661297267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204270412758157840881729689 153202809568618380661297267)
          ·
            refine ⟨229804214352927570991945901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153202809568618380661297267 229804214352927570991945901)
            ·
              refine ⟨86176580382347839121979713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229804214352927570991945901 86176580382347839121979713)
              ·
                refine ⟨64632435286760879341484785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86176580382347839121979713 64632435286760879341484785)
                ·
                  refine ⟨48474326465070659506113589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64632435286760879341484785 48474326465070659506113589)
                  ·
                    refine ⟨4544468106100374328698149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48474326465070659506113589 4544468106100374328698149)
                    ·
                      refine ⟨852087769893820186630903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4544468106100374328698149 852087769893820186630903)
                      ·
                        rfl

theorem cell23_1659435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 4].length) (baseStart_1659435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659435 prefixEnd_1659435 := by exact prefixLift 1659435
  have htrace : WordTrace (prefixWord ++ tailWord_1659435) baseStart_1659435 baseEnd_1659435 := by
    simpa [prefixWord, tailWord_1659435, baseEnd_1659435] using wordTrace_append hprefix tailTrace_1659435
  have hstable : (prefixWord ++ tailWord_1659435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659435).length < 2 ^ (prefixWord ++ tailWord_1659435).sum := by decide
  have hdescent : baseEnd_1659435 < baseStart_1659435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659479 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 2, 4]
def baseStart_1659479 : Nat := 118140960795 + 1659479 * 2 ^ 59
def prefixEnd_1659479 : Nat := 4983230072969 + 3 ^ 40 * 1659479 * 2
def baseEnd_1659479 : Nat := 284036787680872671493567

theorem tailTrace_1659479 : CollatzResearch.WordTrace tailWord_1659479 prefixEnd_1659479 284036787680872671493567 := by
  unfold tailWord_1659479
  simp only [CollatzResearch.WordTrace]
  refine ⟨60526171554998474294373491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40350781036665649529582327 60526171554998474294373491)
  ·
    refine ⟨90789257332497711441560237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60526171554998474294373491 90789257332497711441560237)
    ·
      refine ⟨34045971499686641790585089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90789257332497711441560237 34045971499686641790585089)
      ·
        refine ⟨25534478624764981342938817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34045971499686641790585089 25534478624764981342938817)
        ·
          refine ⟨19150858968573736007204113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25534478624764981342938817 19150858968573736007204113)
          ·
            refine ⟨14363144226430302005403085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19150858968573736007204113 14363144226430302005403085)
            ·
              refine ⟨5386179084911363252026157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14363144226430302005403085 5386179084911363252026157)
              ·
                refine ⟨2019817156841761219509809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5386179084911363252026157 2019817156841761219509809)
                ·
                  refine ⟨1514862867631320914632357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2019817156841761219509809 1514862867631320914632357)
                  ·
                    refine ⟨284036787680872671493567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1514862867631320914632357 284036787680872671493567)
                    ·
                      rfl

theorem cell23_1659479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_1659479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659479 prefixEnd_1659479 := by exact prefixLift 1659479
  have htrace : WordTrace (prefixWord ++ tailWord_1659479) baseStart_1659479 baseEnd_1659479 := by
    simpa [prefixWord, tailWord_1659479, baseEnd_1659479] using wordTrace_append hprefix tailTrace_1659479
  have hstable : (prefixWord ++ tailWord_1659479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659479).length < 2 ^ (prefixWord ++ tailWord_1659479).sum := by decide
  have hdescent : baseEnd_1659479 < baseStart_1659479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659489 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_1659489 : Nat := 118140960795 + 1659489 * 2 ^ 59
def prefixEnd_1659489 : Nat := 4983230072969 + 3 ^ 40 * 1659489 * 2
def baseEnd_1659489 : Nat := 852115497849162975355655

theorem tailTrace_1659489 : CollatzResearch.WordTrace tailWord_1659489 prefixEnd_1659489 852115497849162975355655 := by
  unfold tailWord_1659489
  simp only [CollatzResearch.WordTrace]
  refine ⟨60526536284962246002237521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40351024189974830668158347 60526536284962246002237521)
  ·
    refine ⟨45394902213721684501678141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60526536284962246002237521 45394902213721684501678141)
    ·
      refine ⟨17023088330145631688129303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45394902213721684501678141 17023088330145631688129303)
      ·
        refine ⟨25534632495218447532193955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17023088330145631688129303 25534632495218447532193955)
        ·
          refine ⟨38301948742827671298290933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25534632495218447532193955 38301948742827671298290933)
          ·
            refine ⟨3590807694640094184214775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38301948742827671298290933 3590807694640094184214775)
            ·
              refine ⟨5386211541960141276322163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590807694640094184214775 5386211541960141276322163)
              ·
                refine ⟨8079317312940211914483245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386211541960141276322163 8079317312940211914483245)
                ·
                  refine ⟨3029743992352579467931217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8079317312940211914483245 3029743992352579467931217)
                  ·
                    refine ⟨2272307994264434600948413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3029743992352579467931217 2272307994264434600948413)
                    ·
                      refine ⟨852115497849162975355655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2272307994264434600948413 852115497849162975355655)
                      ·
                        rfl

theorem cell23_1659489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_1659489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659489 prefixEnd_1659489 := by exact prefixLift 1659489
  have htrace : WordTrace (prefixWord ++ tailWord_1659489) baseStart_1659489 baseEnd_1659489 := by
    simpa [prefixWord, tailWord_1659489, baseEnd_1659489] using wordTrace_append hprefix tailTrace_1659489
  have hstable : (prefixWord ++ tailWord_1659489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659489).length < 2 ^ (prefixWord ++ tailWord_1659489).sum := by decide
  have hdescent : baseEnd_1659489 < baseStart_1659489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659490 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1659490 : Nat := 118140960795 + 1659490 * 2 ^ 59
def prefixEnd_1659490 : Nat := 4983230072969 + 3 ^ 40 * 1659490 * 2
def baseEnd_1659490 : Nat := 852116011329817471443151

theorem tailTrace_1659490 : CollatzResearch.WordTrace tailWord_1659490 prefixEnd_1659490 852116011329817471443151 := by
  unfold tailWord_1659490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15131643189489655793255981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40351048505305748782015949 15131643189489655793255981)
  ·
    refine ⟨5674366196058620922470993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15131643189489655793255981 5674366196058620922470993)
    ·
      refine ⟨4255774647043965691853245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5674366196058620922470993 4255774647043965691853245)
      ·
        refine ⟨1595915492641487134444967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4255774647043965691853245 1595915492641487134444967)
        ·
          refine ⟨2393873238962230701667451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595915492641487134444967 2393873238962230701667451)
          ·
            refine ⟨3590809858443346052501177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393873238962230701667451 3590809858443346052501177)
            ·
              refine ⟨2693107393832509539375883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3590809858443346052501177 2693107393832509539375883)
              ·
                refine ⟨4039661090748764309063825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693107393832509539375883 4039661090748764309063825)
                ·
                  refine ⟨3029745818061573231797869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4039661090748764309063825 3029745818061573231797869)
                  ·
                    refine ⟨1136154681773089961924201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029745818061573231797869 1136154681773089961924201)
                    ·
                      refine ⟨852116011329817471443151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1136154681773089961924201 852116011329817471443151)
                      ·
                        rfl

theorem cell23_1659490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1659490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659490 prefixEnd_1659490 := by exact prefixLift 1659490
  have htrace : WordTrace (prefixWord ++ tailWord_1659490) baseStart_1659490 baseEnd_1659490 := by
    simpa [prefixWord, tailWord_1659490, baseEnd_1659490] using wordTrace_append hprefix tailTrace_1659490
  have hstable : (prefixWord ++ tailWord_1659490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659490).length < 2 ^ (prefixWord ++ tailWord_1659490).sum := by decide
  have hdescent : baseEnd_1659490 < baseStart_1659490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659506 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_1659506 : Nat := 118140960795 + 1659506 * 2 ^ 59
def prefixEnd_1659506 : Nat := 4983230072969 + 3 ^ 40 * 1659506 * 2
def baseEnd_1659506 : Nat := 852124227020289408843077

theorem tailTrace_1659506 : CollatzResearch.WordTrace tailWord_1659506 prefixEnd_1659506 852124227020289408843077 := by
  unfold tailWord_1659506
  simp only [CollatzResearch.WordTrace]
  refine ⟨15131789081475164476401593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40351437550600438603737581 15131789081475164476401593)
  ·
    refine ⟨11348841811106373357301195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15131789081475164476401593 11348841811106373357301195)
    ·
      refine ⟨17023262716659560035951793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11348841811106373357301195 17023262716659560035951793)
      ·
        refine ⟨12767447037494670026963845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17023262716659560035951793 12767447037494670026963845)
        ·
          refine ⟨2393896319530250630055721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12767447037494670026963845 2393896319530250630055721)
          ·
            refine ⟨1795422239647687972541791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2393896319530250630055721 1795422239647687972541791)
            ·
              refine ⟨2693133359471531958812687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795422239647687972541791 2693133359471531958812687)
              ·
                refine ⟨4039700039207297938219031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693133359471531958812687 4039700039207297938219031)
                ·
                  refine ⟨6059550058810946907328547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039700039207297938219031 6059550058810946907328547)
                  ·
                    refine ⟨9089325088216420360992821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6059550058810946907328547 9089325088216420360992821)
                    ·
                      refine ⟨852124227020289408843077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9089325088216420360992821 852124227020289408843077)
                      ·
                        rfl

theorem cell23_1659506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_1659506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659506 prefixEnd_1659506 := by exact prefixLift 1659506
  have htrace : WordTrace (prefixWord ++ tailWord_1659506) baseStart_1659506 baseEnd_1659506 := by
    simpa [prefixWord, tailWord_1659506, baseEnd_1659506] using wordTrace_append hprefix tailTrace_1659506
  have hstable : (prefixWord ++ tailWord_1659506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659506).length < 2 ^ (prefixWord ++ tailWord_1659506).sum := by decide
  have hdescent : baseEnd_1659506 < baseStart_1659506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659509 : List Nat := [1, 3, 4, 2, 3, 10]
def baseStart_1659509 : Nat := 118140960795 + 1659509 * 2 ^ 59
def prefixEnd_1659509 : Nat := 4983230072969 + 3 ^ 40 * 1659509 * 2
def baseEnd_1659509 : Nat := 3506690401079230029241

theorem tailTrace_1659509 : CollatzResearch.WordTrace tailWord_1659509 prefixEnd_1659509 3506690401079230029241 := by
  unfold tailWord_1659509
  simp only [CollatzResearch.WordTrace]
  refine ⟨60527265744889789417965581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40351510496593192945310387 60527265744889789417965581)
  ·
    refine ⟨22697724654333671031737093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60527265744889789417965581 22697724654333671031737093)
    ·
      refine ⟨4255823372687563318450705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22697724654333671031737093 4255823372687563318450705)
      ·
        refine ⟨3191867529515672488838029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4255823372687563318450705 3191867529515672488838029)
        ·
          refine ⟨1196950323568377183314261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3191867529515672488838029 1196950323568377183314261)
          ·
            refine ⟨3506690401079230029241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1196950323568377183314261 3506690401079230029241)
            ·
              rfl

theorem cell23_1659509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 10].length) (baseStart_1659509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659509 prefixEnd_1659509 := by exact prefixLift 1659509
  have htrace : WordTrace (prefixWord ++ tailWord_1659509) baseStart_1659509 baseEnd_1659509 := by
    simpa [prefixWord, tailWord_1659509, baseEnd_1659509] using wordTrace_append hprefix tailTrace_1659509
  have hstable : (prefixWord ++ tailWord_1659509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659509).length < 2 ^ (prefixWord ++ tailWord_1659509).sum := by decide
  have hdescent : baseEnd_1659509 < baseStart_1659509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659520 : List Nat := [2, 1, 1, 2, 1, 5, 4, 2, 1, 2, 2]
def baseStart_1659520 : Nat := 118140960795 + 1659520 * 2 ^ 59
def prefixEnd_1659520 : Nat := 4983230072969 + 3 ^ 40 * 1659520 * 2
def baseEnd_1659520 : Nat := 852131415749452354068013

theorem tailTrace_1659520 : CollatzResearch.WordTrace tailWord_1659520 prefixEnd_1659520 852131415749452354068013 := by
  unfold tailWord_1659520
  simp only [CollatzResearch.WordTrace]
  refine ⟨30263833473924969148308007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40351777965233292197744009 30263833473924969148308007)
  ·
    refine ⟨45395750210887453722462011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30263833473924969148308007 45395750210887453722462011)
    ·
      refine ⟨68093625316331180583693017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45395750210887453722462011 68093625316331180583693017)
      ·
        refine ⟨51070218987248385437769763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68093625316331180583693017 51070218987248385437769763)
        ·
          refine ⟨76605328480872578156654645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51070218987248385437769763 76605328480872578156654645)
          ·
            refine ⟨7181749545081804202186373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76605328480872578156654645 7181749545081804202186373)
            ·
              refine ⟨1346578039702838287909945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7181749545081804202186373 1346578039702838287909945)
              ·
                refine ⟨1009933529777128715932459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346578039702838287909945 1009933529777128715932459)
                ·
                  refine ⟨1514900294665693073898689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009933529777128715932459 1514900294665693073898689)
                  ·
                    refine ⟨1136175220999269805424017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1514900294665693073898689 1136175220999269805424017)
                    ·
                      refine ⟨852131415749452354068013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1136175220999269805424017 852131415749452354068013)
                      ·
                        rfl

theorem cell23_1659520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 1, 2, 2].length) (baseStart_1659520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659520 prefixEnd_1659520 := by exact prefixLift 1659520
  have htrace : WordTrace (prefixWord ++ tailWord_1659520) baseStart_1659520 baseEnd_1659520 := by
    simpa [prefixWord, tailWord_1659520, baseEnd_1659520] using wordTrace_append hprefix tailTrace_1659520
  have hstable : (prefixWord ++ tailWord_1659520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659520).length < 2 ^ (prefixWord ++ tailWord_1659520).sum := by decide
  have hdescent : baseEnd_1659520 < baseStart_1659520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659597 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_1659597 : Nat := 118140960795 + 1659597 * 2 ^ 59
def prefixEnd_1659597 : Nat := 4983230072969 + 3 ^ 40 * 1659597 * 2
def baseEnd_1659597 : Nat := 852170953759848552805159

theorem tailTrace_1659597 : CollatzResearch.WordTrace tailWord_1659597 prefixEnd_1659597 852170953759848552805159 := by
  unfold tailWord_1659597
  simp only [CollatzResearch.WordTrace]
  refine ⟨60530475368570980447169045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40353650245713986964779363 60530475368570980447169045)
  ·
    refine ⟨2837366032901764708461049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60530475368570980447169045 2837366032901764708461049)
    ·
      refine ⟨2128024524676323531345787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2837366032901764708461049 2128024524676323531345787)
      ·
        refine ⟨3192036787014485297018681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128024524676323531345787 3192036787014485297018681)
        ·
          refine ⟨2394027590260863972764011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3192036787014485297018681 2394027590260863972764011)
          ·
            refine ⟨3591041385391295959146017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394027590260863972764011 3591041385391295959146017)
            ·
              refine ⟨2693281039043471969359513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3591041385391295959146017 2693281039043471969359513)
              ·
                refine ⟨2019960779282603977019635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2693281039043471969359513 2019960779282603977019635)
                ·
                  refine ⟨3029941168923905965529453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019960779282603977019635 3029941168923905965529453)
                  ·
                    refine ⟨1136227938346464737073545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029941168923905965529453 1136227938346464737073545)
                    ·
                      refine ⟨852170953759848552805159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1136227938346464737073545 852170953759848552805159)
                      ·
                        rfl

theorem cell23_1659597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_1659597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659597 prefixEnd_1659597 := by exact prefixLift 1659597
  have htrace : WordTrace (prefixWord ++ tailWord_1659597) baseStart_1659597 baseEnd_1659597 := by
    simpa [prefixWord, tailWord_1659597, baseEnd_1659597] using wordTrace_append hprefix tailTrace_1659597
  have hstable : (prefixWord ++ tailWord_1659597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659597).length < 2 ^ (prefixWord ++ tailWord_1659597).sum := by decide
  have hdescent : baseEnd_1659597 < baseStart_1659597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659649 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1659649 : Nat := 118140960795 + 1659649 * 2 ^ 59
def prefixEnd_1659649 : Nat := 4983230072969 + 3 ^ 40 * 1659649 * 2
def baseEnd_1659649 : Nat := 852197654753882349354919

theorem tailTrace_1659649 : CollatzResearch.WordTrace tailWord_1659649 prefixEnd_1659649 852197654753882349354919 := by
  unfold tailWord_1659649
  simp only [CollatzResearch.WordTrace]
  refine ⟨60532371964382593328062001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40354914642921728885374667 60532371964382593328062001)
  ·
    refine ⟨45399278973286944996046501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60532371964382593328062001 45399278973286944996046501)
    ·
      refine ⟨8512364807491302186758719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45399278973286944996046501 8512364807491302186758719)
      ·
        refine ⟨12768547211236953280138079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8512364807491302186758719 12768547211236953280138079)
        ·
          refine ⟨19152820816855429920207119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12768547211236953280138079 19152820816855429920207119)
          ·
            refine ⟨28729231225283144880310679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19152820816855429920207119 28729231225283144880310679)
            ·
              refine ⟨43093846837924717320466019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28729231225283144880310679 43093846837924717320466019)
              ·
                refine ⟨64640770256887075980699029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43093846837924717320466019 64640770256887075980699029)
                ·
                  refine ⟨3030036105791581686595267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64640770256887075980699029 3030036105791581686595267)
                  ·
                    refine ⟨4545054158687372529892901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3030036105791581686595267 4545054158687372529892901)
                    ·
                      refine ⟨852197654753882349354919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4545054158687372529892901 852197654753882349354919)
                      ·
                        rfl

theorem cell23_1659649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1659649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659649 prefixEnd_1659649 := by exact prefixLift 1659649
  have htrace : WordTrace (prefixWord ++ tailWord_1659649) baseStart_1659649 baseEnd_1659649 := by
    simpa [prefixWord, tailWord_1659649, baseEnd_1659649] using wordTrace_append hprefix tailTrace_1659649
  have hstable : (prefixWord ++ tailWord_1659649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659649).length < 2 ^ (prefixWord ++ tailWord_1659649).sum := by decide
  have hdescent : baseEnd_1659649 < baseStart_1659649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659659 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 5, 4]
def baseStart_1659659 : Nat := 118140960795 + 1659659 * 2 ^ 59
def prefixEnd_1659659 : Nat := 4983230072969 + 3 ^ 40 * 1659659 * 2
def baseEnd_1659659 : Nat := 284067596520142436743291

theorem tailTrace_1659659 : CollatzResearch.WordTrace tailWord_1659659 prefixEnd_1659659 284067596520142436743291 := by
  unfold tailWord_1659659
  simp only [CollatzResearch.WordTrace]
  refine ⟨60532736694346365035926031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40355157796230910023950687 60532736694346365035926031)
  ·
    refine ⟨90799105041519547553889047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60532736694346365035926031 90799105041519547553889047)
    ·
      refine ⟨136198657562279321330833571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90799105041519547553889047 136198657562279321330833571)
      ·
        refine ⟨204297986343418981996250357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136198657562279321330833571 204297986343418981996250357)
        ·
          refine ⟨19152936219695529562148471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204297986343418981996250357 19152936219695529562148471)
          ·
            refine ⟨28729404329543294343222707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19152936219695529562148471 28729404329543294343222707)
            ·
              refine ⟨43094106494314941514834061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28729404329543294343222707 43094106494314941514834061)
              ·
                refine ⟨16160289935368103068062773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43094106494314941514834061 16160289935368103068062773)
                ·
                  refine ⟨1515027181440759662630885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16160289935368103068062773 1515027181440759662630885)
                  ·
                    refine ⟨284067596520142436743291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1515027181440759662630885 284067596520142436743291)
                    ·
                      rfl

theorem cell23_1659659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 4].length) (baseStart_1659659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659659 prefixEnd_1659659 := by exact prefixLift 1659659
  have htrace : WordTrace (prefixWord ++ tailWord_1659659) baseStart_1659659 baseEnd_1659659 := by
    simpa [prefixWord, tailWord_1659659, baseEnd_1659659] using wordTrace_append hprefix tailTrace_1659659
  have hstable : (prefixWord ++ tailWord_1659659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659659).length < 2 ^ (prefixWord ++ tailWord_1659659).sum := by decide
  have hdescent : baseEnd_1659659 < baseStart_1659659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659700 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_1659700 : Nat := 118140960795 + 1659700 * 2 ^ 59
def prefixEnd_1659700 : Nat := 4983230072969 + 3 ^ 40 * 1659700 * 2
def baseEnd_1659700 : Nat := 852223842267261649817185

theorem tailTrace_1659700 : CollatzResearch.WordTrace tailWord_1659700 prefixEnd_1659700 852223842267261649817185 := by
  unfold tailWord_1659700
  simp only [CollatzResearch.WordTrace]
  refine ⟨30267116043598914519084277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40356154724798552692112369 30267116043598914519084277)
  ·
    refine ⟨2837542129087398236164151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30267116043598914519084277 2837542129087398236164151)
    ·
      refine ⟨4256313193631097354246227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2837542129087398236164151 4256313193631097354246227)
      ·
        refine ⟨6384469790446646031369341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4256313193631097354246227 6384469790446646031369341)
        ·
          refine ⟨2394176171417492261763503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6384469790446646031369341 2394176171417492261763503)
          ·
            refine ⟨3591264257126238392645255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394176171417492261763503 3591264257126238392645255)
            ·
              refine ⟨5386896385689357588967883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3591264257126238392645255 5386896385689357588967883)
              ·
                refine ⟨8080344578534036383451825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386896385689357588967883 8080344578534036383451825)
                ·
                  refine ⟨6060258433900527287588869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8080344578534036383451825 6060258433900527287588869)
                  ·
                    refine ⟨1136298456356348866422913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6060258433900527287588869 1136298456356348866422913)
                    ·
                      refine ⟨852223842267261649817185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1136298456356348866422913 852223842267261649817185)
                      ·
                        rfl

theorem cell23_1659700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_1659700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659700 prefixEnd_1659700 := by exact prefixLift 1659700
  have htrace : WordTrace (prefixWord ++ tailWord_1659700) baseStart_1659700 baseEnd_1659700 := by
    simpa [prefixWord, tailWord_1659700, baseEnd_1659700] using wordTrace_append hprefix tailTrace_1659700
  have hstable : (prefixWord ++ tailWord_1659700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659700).length < 2 ^ (prefixWord ++ tailWord_1659700).sum := by decide
  have hdescent : baseEnd_1659700 < baseStart_1659700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659749 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_1659749 : Nat := 118140960795 + 1659749 * 2 ^ 59
def prefixEnd_1659749 : Nat := 4983230072969 + 3 ^ 40 * 1659749 * 2
def baseEnd_1659749 : Nat := 284083000939777319368153

theorem tailTrace_1659749 : CollatzResearch.WordTrace tailWord_1659749 prefixEnd_1659749 284083000939777319368153 := by
  unfold tailWord_1659749
  simp only [CollatzResearch.WordTrace]
  refine ⟨60536019264020310406702301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40357346176013540271134867 60536019264020310406702301)
  ·
    refine ⟨22701007224007616402513363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60536019264020310406702301 22701007224007616402513363)
    ·
      refine ⟨34051510836011424603770045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22701007224007616402513363 34051510836011424603770045)
      ·
        refine ⟨12769316563504284226413767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34051510836011424603770045 12769316563504284226413767)
        ·
          refine ⟨19153974845256426339620651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12769316563504284226413767 19153974845256426339620651)
          ·
            refine ⟨28730962267884639509430977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19153974845256426339620651 28730962267884639509430977)
            ·
              refine ⟨21548221700913479632073233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28730962267884639509430977 21548221700913479632073233)
              ·
                refine ⟨16161166275685109724054925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21548221700913479632073233 16161166275685109724054925)
                ·
                  refine ⟨6060437353381916146520597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16161166275685109724054925 6060437353381916146520597)
                  ·
                    refine ⟨284083000939777319368153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6060437353381916146520597 284083000939777319368153)
                    ·
                      rfl

theorem cell23_1659749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_1659749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659749 prefixEnd_1659749 := by exact prefixLift 1659749
  have htrace : WordTrace (prefixWord ++ tailWord_1659749) baseStart_1659749 baseEnd_1659749 := by
    simpa [prefixWord, tailWord_1659749, baseEnd_1659749] using wordTrace_append hprefix tailTrace_1659749
  have hstable : (prefixWord ++ tailWord_1659749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659749).length < 2 ^ (prefixWord ++ tailWord_1659749).sum := by decide
  have hdescent : baseEnd_1659749 < baseStart_1659749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659779 : List Nat := [1, 1, 1, 3, 4, 1, 3, 9]
def baseStart_1659779 : Nat := 118140960795 + 1659779 * 2 ^ 59
def prefixEnd_1659779 : Nat := 4983230072969 + 3 ^ 40 * 1659779 * 2
def baseEnd_1659779 : Nat := 31565348416258031138123

theorem tailTrace_1659779 : CollatzResearch.WordTrace tailWord_1659779 prefixEnd_1659779 31565348416258031138123 := by
  unfold tailWord_1659779
  simp only [CollatzResearch.WordTrace]
  refine ⟨60537113453911625530294391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40358075635941083686862927 60537113453911625530294391)
  ·
    refine ⟨90805670180867438295441587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60537113453911625530294391 90805670180867438295441587)
    ·
      refine ⟨136208505271301157443162381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90805670180867438295441587 136208505271301157443162381)
      ·
        refine ⟨51078189476737934041185893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136208505271301157443162381 51078189476737934041185893)
        ·
          refine ⟨9577160526888362632722355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51078189476737934041185893 9577160526888362632722355)
          ·
            refine ⟨14365740790332543949083533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9577160526888362632722355 14365740790332543949083533)
            ·
              refine ⟨5387152796374703980906325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14365740790332543949083533 5387152796374703980906325)
              ·
                refine ⟨31565348416258031138123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5387152796374703980906325 31565348416258031138123)
                ·
                  rfl

theorem cell23_1659779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 9].length) (baseStart_1659779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659779 prefixEnd_1659779 := by exact prefixLift 1659779
  have htrace : WordTrace (prefixWord ++ tailWord_1659779) baseStart_1659779 baseEnd_1659779 := by
    simpa [prefixWord, tailWord_1659779, baseEnd_1659779] using wordTrace_append hprefix tailTrace_1659779
  have hstable : (prefixWord ++ tailWord_1659779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659779).length < 2 ^ (prefixWord ++ tailWord_1659779).sum := by decide
  have hdescent : baseEnd_1659779 < baseStart_1659779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659807 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 3, 2, 2]
def baseStart_1659807 : Nat := 118140960795 + 1659807 * 2 ^ 59
def prefixEnd_1659807 : Nat := 4983230072969 + 3 ^ 40 * 1659807 * 2
def baseEnd_1659807 : Nat := 852278784697292731179193

theorem tailTrace_1659807 : CollatzResearch.WordTrace tailWord_1659807 prefixEnd_1659807 852278784697292731179193 := by
  unfold tailWord_1659807
  simp only [CollatzResearch.WordTrace]
  refine ⟨60538134697810186312313675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40358756465206790874875783 60538134697810186312313675)
  ·
    refine ⟨90807202046715279468470513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60538134697810186312313675 90807202046715279468470513)
    ·
      refine ⟨68105401535036459601352885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90807202046715279468470513 68105401535036459601352885)
      ·
        refine ⟨6384881393909668087626833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68105401535036459601352885 6384881393909668087626833)
        ·
          refine ⟨4788661045432251065720125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6384881393909668087626833 4788661045432251065720125)
          ·
            refine ⟨1795747892037094149645047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4788661045432251065720125 1795747892037094149645047)
            ·
              refine ⟨2693621838055641224467571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795747892037094149645047 2693621838055641224467571)
              ·
                refine ⟨4040432757083461836701357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693621838055641224467571 4040432757083461836701357)
                ·
                  refine ⟨1515162283906298188763009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4040432757083461836701357 1515162283906298188763009)
                  ·
                    refine ⟨1136371712929723641572257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1515162283906298188763009 1136371712929723641572257)
                    ·
                      refine ⟨852278784697292731179193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1136371712929723641572257 852278784697292731179193)
                      ·
                        rfl

theorem cell23_1659807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_1659807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659807 prefixEnd_1659807 := by exact prefixLift 1659807
  have htrace : WordTrace (prefixWord ++ tailWord_1659807) baseStart_1659807 baseEnd_1659807 := by
    simpa [prefixWord, tailWord_1659807, baseEnd_1659807] using wordTrace_append hprefix tailTrace_1659807
  have hstable : (prefixWord ++ tailWord_1659807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659807).length < 2 ^ (prefixWord ++ tailWord_1659807).sum := by decide
  have hdescent : baseEnd_1659807 < baseStart_1659807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659819 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 5]
def baseStart_1659819 : Nat := 118140960795 + 1659819 * 2 ^ 59
def prefixEnd_1659819 : Nat := 4983230072969 + 3 ^ 40 * 1659819 * 2
def baseEnd_1659819 : Nat := 852284946465146684229137

theorem tailTrace_1659819 : CollatzResearch.WordTrace tailWord_1659819 prefixEnd_1659819 852284946465146684229137 := by
  unfold tailWord_1659819
  simp only [CollatzResearch.WordTrace]
  refine ⟨60538572373766712361750511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40359048249177808241167007 60538572373766712361750511)
  ·
    refine ⟨90807858560650068542625767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60538572373766712361750511 90807858560650068542625767)
    ·
      refine ⟨136211787840975102813938651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90807858560650068542625767 136211787840975102813938651)
      ·
        refine ⟨204317681761462654220907977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136211787840975102813938651 204317681761462654220907977)
        ·
          refine ⟨153238261321096990665680983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204317681761462654220907977 153238261321096990665680983)
          ·
            refine ⟨229857391981645485998521475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153238261321096990665680983 229857391981645485998521475)
            ·
              refine ⟨344786087972468228997782213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229857391981645485998521475 344786087972468228997782213)
              ·
                refine ⟨64647391494837792937084165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344786087972468228997782213 64647391494837792937084165)
                ·
                  refine ⟨12121385905282086175703281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64647391494837792937084165 12121385905282086175703281)
                  ·
                    refine ⟨9091039428961564631777461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12121385905282086175703281 9091039428961564631777461)
                    ·
                      refine ⟨852284946465146684229137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9091039428961564631777461 852284946465146684229137)
                      ·
                        rfl

theorem cell23_1659819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_1659819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659819 prefixEnd_1659819 := by exact prefixLift 1659819
  have htrace : WordTrace (prefixWord ++ tailWord_1659819) baseStart_1659819 baseEnd_1659819 := by
    simpa [prefixWord, tailWord_1659819, baseEnd_1659819] using wordTrace_append hprefix tailTrace_1659819
  have hstable : (prefixWord ++ tailWord_1659819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659819).length < 2 ^ (prefixWord ++ tailWord_1659819).sum := by decide
  have hdescent : baseEnd_1659819 < baseStart_1659819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659839 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 3, 8]
def baseStart_1659839 : Nat := 118140960795 + 1659839 * 2 ^ 59
def prefixEnd_1659839 : Nat := 4983230072969 + 3 ^ 40 * 1659839 * 2
def baseEnd_1659839 : Nat := 284098405359412201993015

theorem tailTrace_1659839 : CollatzResearch.WordTrace tailWord_1659839 prefixEnd_1659839 284098405359412201993015 := by
  unfold tailWord_1659839
  simp only [CollatzResearch.WordTrace]
  refine ⟨60539301833694255777478571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40359534555796170518319047 60539301833694255777478571)
  ·
    refine ⟨90808952750541383666217857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60539301833694255777478571 90808952750541383666217857)
    ·
      refine ⟨68106714562906037749663393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90808952750541383666217857 68106714562906037749663393)
      ·
        refine ⟨51080035922179528312247545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68106714562906037749663393 51080035922179528312247545)
        ·
          refine ⟨38310026941634646234185659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51080035922179528312247545 38310026941634646234185659)
          ·
            refine ⟨57465040412451969351278489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38310026941634646234185659 57465040412451969351278489)
            ·
              refine ⟨43098780309338977013458867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57465040412451969351278489 43098780309338977013458867)
              ·
                refine ⟨64648170464008465520188301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43098780309338977013458867 64648170464008465520188301)
                ·
                  refine ⟨24243063924003174570070613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64648170464008465520188301 24243063924003174570070613)
                  ·
                    refine ⟨284098405359412201993015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24243063924003174570070613 284098405359412201993015)
                    ·
                      rfl

theorem cell23_1659839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_1659839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659839 prefixEnd_1659839 := by exact prefixLift 1659839
  have htrace : WordTrace (prefixWord ++ tailWord_1659839) baseStart_1659839 baseEnd_1659839 := by
    simpa [prefixWord, tailWord_1659839, baseEnd_1659839] using wordTrace_append hprefix tailTrace_1659839
  have hstable : (prefixWord ++ tailWord_1659839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659839).length < 2 ^ (prefixWord ++ tailWord_1659839).sum := by decide
  have hdescent : baseEnd_1659839 < baseStart_1659839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659844 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_1659844 : Nat := 118140960795 + 1659844 * 2 ^ 59
def prefixEnd_1659844 : Nat := 4983230072969 + 3 ^ 40 * 1659844 * 2
def baseEnd_1659844 : Nat := 852297783481509086416523

theorem tailTrace_1659844 : CollatzResearch.WordTrace tailWord_1659844 prefixEnd_1659844 852297783481509086416523 := by
  unfold tailWord_1659844
  simp only [CollatzResearch.WordTrace]
  refine ⟨30269742099338070815705293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40359656132450761087607057 30269742099338070815705293)
  ·
    refine ⟨11351153287251776555889485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30269742099338070815705293 11351153287251776555889485)
    ·
      refine ⟨4256682482719416208458557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11351153287251776555889485 4256682482719416208458557)
      ·
        refine ⟨1596255931019781078171959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4256682482719416208458557 1596255931019781078171959)
        ·
          refine ⟨2394383896529671617257939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596255931019781078171959 2394383896529671617257939)
          ·
            refine ⟨3591575844794507425886909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394383896529671617257939 3591575844794507425886909)
            ·
              refine ⟨1346840941797940284707591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3591575844794507425886909 1346840941797940284707591)
              ·
                refine ⟨2020261412696910427061387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346840941797940284707591 2020261412696910427061387)
                ·
                  refine ⟨3030392119045365640592081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020261412696910427061387 3030392119045365640592081)
                  ·
                    refine ⟨2272794089284024230444061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3030392119045365640592081 2272794089284024230444061)
                    ·
                      refine ⟨852297783481509086416523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2272794089284024230444061 852297783481509086416523)
                      ·
                        rfl

theorem cell23_1659844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_1659844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659844 prefixEnd_1659844 := by exact prefixLift 1659844
  have htrace : WordTrace (prefixWord ++ tailWord_1659844) baseStart_1659844 baseEnd_1659844 := by
    simpa [prefixWord, tailWord_1659844, baseEnd_1659844] using wordTrace_append hprefix tailTrace_1659844
  have hstable : (prefixWord ++ tailWord_1659844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659844).length < 2 ^ (prefixWord ++ tailWord_1659844).sum := by decide
  have hdescent : baseEnd_1659844 < baseStart_1659844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659896 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 3, 5, 3]
def baseStart_1659896 : Nat := 118140960795 + 1659896 * 2 ^ 59
def prefixEnd_1659896 : Nat := 4983230072969 + 3 ^ 40 * 1659896 * 2
def baseEnd_1659896 : Nat := 852324484475542882966283

theorem tailTrace_1659896 : CollatzResearch.WordTrace tailWord_1659896 prefixEnd_1659896 852324484475542882966283 := by
  unfold tailWord_1659896
  simp only [CollatzResearch.WordTrace]
  refine ⟨30270690397243877256151771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40360920529658503008202361 30270690397243877256151771)
  ·
    refine ⟨45406035595865815884227657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30270690397243877256151771 45406035595865815884227657)
    ·
      refine ⟨34054526696899361913170743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45406035595865815884227657 34054526696899361913170743)
      ·
        refine ⟨51081790045349042869756115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34054526696899361913170743 51081790045349042869756115)
        ·
          refine ⟨76622685068023564304634173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51081790045349042869756115 76622685068023564304634173)
          ·
            refine ⟨28733506900508836614237815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76622685068023564304634173 28733506900508836614237815)
            ·
              refine ⟨43100260350763254921356723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28733506900508836614237815 43100260350763254921356723)
              ·
                refine ⟨64650390526144882382035085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43100260350763254921356723 64650390526144882382035085)
                ·
                  refine ⟨24243896447304330893263157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64650390526144882382035085 24243896447304330893263157)
                  ·
                    refine ⟨2272865291934781021243421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24243896447304330893263157 2272865291934781021243421)
                    ·
                      refine ⟨852324484475542882966283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2272865291934781021243421 852324484475542882966283)
                      ·
                        rfl

theorem cell23_1659896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_1659896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659896 prefixEnd_1659896 := by exact prefixLift 1659896
  have htrace : WordTrace (prefixWord ++ tailWord_1659896) baseStart_1659896 baseEnd_1659896 := by
    simpa [prefixWord, tailWord_1659896, baseEnd_1659896] using wordTrace_append hprefix tailTrace_1659896
  have hstable : (prefixWord ++ tailWord_1659896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659896).length < 2 ^ (prefixWord ++ tailWord_1659896).sum := by decide
  have hdescent : baseEnd_1659896 < baseStart_1659896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659914 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2]
def baseStart_1659914 : Nat := 118140960795 + 1659914 * 2 ^ 59
def prefixEnd_1659914 : Nat := 4983230072969 + 3 ^ 40 * 1659914 * 2
def baseEnd_1659914 : Nat := 852333727127323812541201

theorem tailTrace_1659914 : CollatzResearch.WordTrace tailWord_1659914 prefixEnd_1659914 852333727127323812541201 := by
  unfold tailWord_1659914
  simp only [CollatzResearch.WordTrace]
  refine ⟨15135509327105635896614699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40361358205615029057639197 15135509327105635896614699)
  ·
    refine ⟨22703263990658453844922049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15135509327105635896614699 22703263990658453844922049)
    ·
      refine ⟨17027447992993840383691537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22703263990658453844922049 17027447992993840383691537)
      ·
        refine ⟨12770585994745380287768653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17027447992993840383691537 12770585994745380287768653)
        ·
          refine ⟨4788969748029517607913245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12770585994745380287768653 4788969748029517607913245)
          ·
            refine ⟨1795863655511069102967467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4788969748029517607913245 1795863655511069102967467)
            ·
              refine ⟨2693795483266603654451201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795863655511069102967467 2693795483266603654451201)
              ·
                refine ⟨2020346612449952740838401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2693795483266603654451201 2020346612449952740838401)
                ·
                  refine ⟨1515259959337464555628801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2020346612449952740838401 1515259959337464555628801)
                  ·
                    refine ⟨1136444969503098416721601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1515259959337464555628801 1136444969503098416721601)
                    ·
                      refine ⟨852333727127323812541201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1136444969503098416721601 852333727127323812541201)
                      ·
                        rfl

theorem cell23_1659914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_1659914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659914 prefixEnd_1659914 := by exact prefixLift 1659914
  have htrace : WordTrace (prefixWord ++ tailWord_1659914) baseStart_1659914 baseEnd_1659914 := by
    simpa [prefixWord, tailWord_1659914, baseEnd_1659914] using wordTrace_append hprefix tailTrace_1659914
  have hstable : (prefixWord ++ tailWord_1659914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659914).length < 2 ^ (prefixWord ++ tailWord_1659914).sum := by decide
  have hdescent : baseEnd_1659914 < baseStart_1659914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659953 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_1659953 : Nat := 118140960795 + 1659953 * 2 ^ 59
def prefixEnd_1659953 : Nat := 4983230072969 + 3 ^ 40 * 1659953 * 2
def baseEnd_1659953 : Nat := 852353752872849159953521

theorem tailTrace_1659953 : CollatzResearch.WordTrace tailWord_1659953 prefixEnd_1659953 852353752872849159953521 := by
  unfold tailWord_1659953
  simp only [CollatzResearch.WordTrace]
  refine ⟨60543459755281253247128513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40362306503520835498085675 60543459755281253247128513)
  ·
    refine ⟨45407594816460939935346385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60543459755281253247128513 45407594816460939935346385)
    ·
      refine ⟨34055696112345704951509789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45407594816460939935346385 34055696112345704951509789)
      ·
        refine ⟨12770886042129639356816171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34055696112345704951509789 12770886042129639356816171)
        ·
          refine ⟨19156329063194459035224257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12770886042129639356816171 19156329063194459035224257)
          ·
            refine ⟨14367246797395844276418193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19156329063194459035224257 14367246797395844276418193)
            ·
              refine ⟨10775435098046883207313645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14367246797395844276418193 10775435098046883207313645)
              ·
                refine ⟨4040788161767581202742617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10775435098046883207313645 4040788161767581202742617)
                ·
                  refine ⟨3030591121325685902056963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4040788161767581202742617 3030591121325685902056963)
                  ·
                    refine ⟨4545886681988528853085445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3030591121325685902056963 4545886681988528853085445)
                    ·
                      refine ⟨852353752872849159953521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4545886681988528853085445 852353752872849159953521)
                      ·
                        rfl

theorem cell23_1659953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_1659953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659953 prefixEnd_1659953 := by exact prefixLift 1659953
  have htrace : WordTrace (prefixWord ++ tailWord_1659953) baseStart_1659953 baseEnd_1659953 := by
    simpa [prefixWord, tailWord_1659953, baseEnd_1659953] using wordTrace_append hprefix tailTrace_1659953
  have hstable : (prefixWord ++ tailWord_1659953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659953).length < 2 ^ (prefixWord ++ tailWord_1659953).sum := by decide
  have hdescent : baseEnd_1659953 < baseStart_1659953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659973 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 4, 2, 3]
def baseStart_1659973 : Nat := 118140960795 + 1659973 * 2 ^ 59
def prefixEnd_1659973 : Nat := 4983230072969 + 3 ^ 40 * 1659973 * 2
def baseEnd_1659973 : Nat := 852364022485939081703429

theorem tailTrace_1659973 : CollatzResearch.WordTrace tailWord_1659973 prefixEnd_1659973 852364022485939081703429 := by
  unfold tailWord_1659973
  simp only [CollatzResearch.WordTrace]
  refine ⟨60544189215208796662856573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40362792810139197775237715 60544189215208796662856573)
  ·
    refine ⟨22704070955703298748571215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60544189215208796662856573 22704070955703298748571215)
    ·
      refine ⟨34056106433554948122856823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22704070955703298748571215 34056106433554948122856823)
      ·
        refine ⟨51084159650332422184285235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34056106433554948122856823 51084159650332422184285235)
        ·
          refine ⟨76626239475498633276427853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51084159650332422184285235 76626239475498633276427853)
          ·
            refine ⟨28734839803311987478660445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76626239475498633276427853 28734839803311987478660445)
            ·
              refine ⟨10775564926241995304497667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28734839803311987478660445 10775564926241995304497667)
              ·
                refine ⟨16163347389362992956746501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10775564926241995304497667 16163347389362992956746501)
                ·
                  refine ⟨3030627635505561179389969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16163347389362992956746501 3030627635505561179389969)
                  ·
                    refine ⟨2272970726629170884542477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3030627635505561179389969 2272970726629170884542477)
                    ·
                      refine ⟨852364022485939081703429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2272970726629170884542477 852364022485939081703429)
                      ·
                        rfl

theorem cell23_1659973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_1659973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659973 prefixEnd_1659973 := by exact prefixLift 1659973
  have htrace : WordTrace (prefixWord ++ tailWord_1659973) baseStart_1659973 baseEnd_1659973 := by
    simpa [prefixWord, tailWord_1659973, baseEnd_1659973] using wordTrace_append hprefix tailTrace_1659973
  have hstable : (prefixWord ++ tailWord_1659973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659973).length < 2 ^ (prefixWord ++ tailWord_1659973).sum := by decide
  have hdescent : baseEnd_1659973 < baseStart_1659973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659976 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 8]
def baseStart_1659976 : Nat := 118140960795 + 1659976 * 2 ^ 59
def prefixEnd_1659976 : Nat := 4983230072969 + 3 ^ 40 * 1659976 * 2
def baseEnd_1659976 : Nat := 94707284769766952218435

theorem tailTrace_1659976 : CollatzResearch.WordTrace tailWord_1659976 prefixEnd_1659976 94707284769766952218435 := by
  unfold tailWord_1659976
  simp only [CollatzResearch.WordTrace]
  refine ⟨30272149317098964087607891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40362865756131952116810521 30272149317098964087607891)
  ·
    refine ⟨45408223975648446131411837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30272149317098964087607891 45408223975648446131411837)
    ·
      refine ⟨17028083990868167299279439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45408223975648446131411837 17028083990868167299279439)
      ·
        refine ⟨25542125986302250948919159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17028083990868167299279439 25542125986302250948919159)
        ·
          refine ⟨38313188979453376423378739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25542125986302250948919159 38313188979453376423378739)
          ·
            refine ⟨57469783469180064635068109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38313188979453376423378739 57469783469180064635068109)
            ·
              refine ⟨21551168800942524238150541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57469783469180064635068109 21551168800942524238150541)
              ·
                refine ⟨8081688300353446589306453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21551168800942524238150541 8081688300353446589306453)
                ·
                  refine ⟨94707284769766952218435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8081688300353446589306453 94707284769766952218435)
                  ·
                    rfl

theorem cell23_1659976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 8].length) (baseStart_1659976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1659976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1659976 prefixEnd_1659976 := by exact prefixLift 1659976
  have htrace : WordTrace (prefixWord ++ tailWord_1659976) baseStart_1659976 baseEnd_1659976 := by
    simpa [prefixWord, tailWord_1659976, baseEnd_1659976] using wordTrace_append hprefix tailTrace_1659976
  have hstable : (prefixWord ++ tailWord_1659976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659976).length < 2 ^ (prefixWord ++ tailWord_1659976).sum := by decide
  have hdescent : baseEnd_1659976 < baseStart_1659976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660060 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1660060 : Nat := 118140960795 + 1660060 * 2 ^ 59
def prefixEnd_1660060 : Nat := 4983230072969 + 3 ^ 40 * 1660060 * 2
def baseEnd_1660060 : Nat := 852408695302880241315529

theorem tailTrace_1660060 : CollatzResearch.WordTrace tailWord_1660060 prefixEnd_1660060 852408695302880241315529 := by
  unfold tailWord_1660060
  simp only [CollatzResearch.WordTrace]
  refine ⟨30273681182946805260636817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40364908243929073680849089 30273681182946805260636817)
  ·
    refine ⟨22705260887210103945477613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30273681182946805260636817 22705260887210103945477613)
    ·
      refine ⟨8514472832703788979554105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22705260887210103945477613 8514472832703788979554105)
      ·
        refine ⟨6385854624527841734665579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8514472832703788979554105 6385854624527841734665579)
        ·
          refine ⟨9578781936791762601998369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6385854624527841734665579 9578781936791762601998369)
          ·
            refine ⟨7184086452593821951498777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9578781936791762601998369 7184086452593821951498777)
            ·
              refine ⟨5388064839445366463624083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7184086452593821951498777 5388064839445366463624083)
              ·
                refine ⟨8082097259168049695436125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5388064839445366463624083 8082097259168049695436125)
                ·
                  refine ⟨3030786472188018635788547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8082097259168049695436125 3030786472188018635788547)
                  ·
                    refine ⟨4546179708282027953682821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3030786472188018635788547 4546179708282027953682821)
                    ·
                      refine ⟨852408695302880241315529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4546179708282027953682821 852408695302880241315529)
                      ·
                        rfl

theorem cell23_1660060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1660060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660060 prefixEnd_1660060 := by exact prefixLift 1660060
  have htrace : WordTrace (prefixWord ++ tailWord_1660060) baseStart_1660060 baseEnd_1660060 := by
    simpa [prefixWord, tailWord_1660060, baseEnd_1660060] using wordTrace_append hprefix tailTrace_1660060
  have hstable : (prefixWord ++ tailWord_1660060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660060).length < 2 ^ (prefixWord ++ tailWord_1660060).sum := by decide
  have hdescent : baseEnd_1660060 < baseStart_1660060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660071 : List Nat := [1, 1, 6, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_1660071 : Nat := 118140960795 + 1660071 * 2 ^ 59
def prefixEnd_1660071 : Nat := 4983230072969 + 3 ^ 40 * 1660071 * 2
def baseEnd_1660071 : Nat := 852414343590079698277979

theorem tailTrace_1660071 : CollatzResearch.WordTrace tailWord_1660071 prefixEnd_1660071 852414343590079698277979 := by
  unfold tailWord_1660071
  simp only [CollatzResearch.WordTrace]
  refine ⟨60547763568853759399924067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40365175712569172933282711 60547763568853759399924067)
  ·
    refine ⟨90821645353280639099886101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60547763568853759399924067 90821645353280639099886101)
    ·
      refine ⟨4257264625935029957807161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90821645353280639099886101 4257264625935029957807161)
      ·
        refine ⟨3192948469451272468355371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4257264625935029957807161 3192948469451272468355371)
        ·
          refine ⟨4789422704176908702533057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3192948469451272468355371 4789422704176908702533057)
          ·
            refine ⟨3592067028132681526899793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4789422704176908702533057 3592067028132681526899793)
            ·
              refine ⟨2694050271099511145174845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3592067028132681526899793 2694050271099511145174845)
              ·
                refine ⟨1010268851662316679440567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2694050271099511145174845 1010268851662316679440567)
                ·
                  refine ⟨1515403277493475019160851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010268851662316679440567 1515403277493475019160851)
                  ·
                    refine ⟨2273104916240212528741277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1515403277493475019160851 2273104916240212528741277)
                    ·
                      refine ⟨852414343590079698277979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2273104916240212528741277 852414343590079698277979)
                      ·
                        rfl

theorem cell23_1660071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_1660071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660071 prefixEnd_1660071 := by exact prefixLift 1660071
  have htrace : WordTrace (prefixWord ++ tailWord_1660071) baseStart_1660071 baseEnd_1660071 := by
    simpa [prefixWord, tailWord_1660071, baseEnd_1660071] using wordTrace_append hprefix tailTrace_1660071
  have hstable : (prefixWord ++ tailWord_1660071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660071).length < 2 ^ (prefixWord ++ tailWord_1660071).sum := by decide
  have hdescent : baseEnd_1660071 < baseStart_1660071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660074 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1660074 : Nat := 118140960795 + 1660074 * 2 ^ 59
def prefixEnd_1660074 : Nat := 4983230072969 + 3 ^ 40 * 1660074 * 2
def baseEnd_1660074 : Nat := 284138628010681062180155

theorem tailTrace_1660074 : CollatzResearch.WordTrace tailWord_1660074 prefixEnd_1660074 284138628010681062180155 := by
  unfold tailWord_1660074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15136968246960722728070819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40365248658561927274855517 15136968246960722728070819)
  ·
    refine ⟨22705452370441084092106229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15136968246960722728070819 22705452370441084092106229)
    ·
      refine ⟨2128636159728851633634959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22705452370441084092106229 2128636159728851633634959)
      ·
        refine ⟨3192954239593277450452439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128636159728851633634959 3192954239593277450452439)
        ·
          refine ⟨4789431359389916175678659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3192954239593277450452439 4789431359389916175678659)
          ·
            refine ⟨7184147039084874263517989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789431359389916175678659 7184147039084874263517989)
            ·
              refine ⟨1347027569828413924409623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7184147039084874263517989 1347027569828413924409623)
              ·
                refine ⟨2020541354742620886614435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347027569828413924409623 2020541354742620886614435)
                ·
                  refine ⟨3030812032113931329921653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020541354742620886614435 3030812032113931329921653)
                  ·
                    refine ⟨284138628010681062180155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3030812032113931329921653 284138628010681062180155)
                    ·
                      rfl

theorem cell23_1660074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1660074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660074 prefixEnd_1660074 := by exact prefixLift 1660074
  have htrace : WordTrace (prefixWord ++ tailWord_1660074) baseStart_1660074 baseEnd_1660074 := by
    simpa [prefixWord, tailWord_1660074, baseEnd_1660074] using wordTrace_append hprefix tailTrace_1660074
  have hstable : (prefixWord ++ tailWord_1660074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660074).length < 2 ^ (prefixWord ++ tailWord_1660074).sum := by decide
  have hdescent : baseEnd_1660074 < baseStart_1660074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660080 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 3]
def baseStart_1660080 : Nat := 118140960795 + 1660080 * 2 ^ 59
def prefixEnd_1660080 : Nat := 4983230072969 + 3 ^ 40 * 1660080 * 2
def baseEnd_1660080 : Nat := 852418964915970163065437

theorem tailTrace_1660080 : CollatzResearch.WordTrace tailWord_1660080 prefixEnd_1660080 852418964915970163065437 := by
  unfold tailWord_1660080
  simp only [CollatzResearch.WordTrace]
  refine ⟨30274045912910576968500847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40365394550547435958001129 30274045912910576968500847)
  ·
    refine ⟨45411068869365865452751271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30274045912910576968500847 45411068869365865452751271)
    ·
      refine ⟨68116603304048798179126907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45411068869365865452751271 68116603304048798179126907)
      ·
        refine ⟨102174904956073197268690361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68116603304048798179126907 102174904956073197268690361)
        ·
          refine ⟨76631178717054897951517771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102174904956073197268690361 76631178717054897951517771)
          ·
            refine ⟨114946768075582346927276657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76631178717054897951517771 114946768075582346927276657)
            ·
              refine ⟨86210076056686760195457493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114946768075582346927276657 86210076056686760195457493)
              ·
                refine ⟨2020548657578595942081035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 86210076056686760195457493 2020548657578595942081035)
                ·
                  refine ⟨3030822986367893913121553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020548657578595942081035 3030822986367893913121553)
                  ·
                    refine ⟨2273117239775920434841165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3030822986367893913121553 2273117239775920434841165)
                    ·
                      refine ⟨852418964915970163065437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2273117239775920434841165 852418964915970163065437)
                      ·
                        rfl

theorem cell23_1660080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 3].length) (baseStart_1660080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660080 prefixEnd_1660080 := by exact prefixLift 1660080
  have htrace : WordTrace (prefixWord ++ tailWord_1660080) baseStart_1660080 baseEnd_1660080 := by
    simpa [prefixWord, tailWord_1660080, baseEnd_1660080] using wordTrace_append hprefix tailTrace_1660080
  have hstable : (prefixWord ++ tailWord_1660080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660080).length < 2 ^ (prefixWord ++ tailWord_1660080).sum := by decide
  have hdescent : baseEnd_1660080 < baseStart_1660080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660094 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_1660094 : Nat := 118140960795 + 1660094 * 2 ^ 59
def prefixEnd_1660094 : Nat := 4983230072969 + 3 ^ 40 * 1660094 * 2
def baseEnd_1660094 : Nat := 852426153645133108290373

theorem tailTrace_1660094 : CollatzResearch.WordTrace tailWord_1660094 prefixEnd_1660094 852426153645133108290373 := by
  unfold tailWord_1660094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7568575305971304291001417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40365734965180289552007557 7568575305971304291001417)
  ·
    refine ⟨5676431479478478218251063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7568575305971304291001417 5676431479478478218251063)
    ·
      refine ⟨8514647219217717327376595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5676431479478478218251063 8514647219217717327376595)
      ·
        refine ⟨12771970828826575991064893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8514647219217717327376595 12771970828826575991064893)
        ·
          refine ⟨4789489060809965996649335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12771970828826575991064893 4789489060809965996649335)
          ·
            refine ⟨7184233591214948994974003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789489060809965996649335 7184233591214948994974003)
            ·
              refine ⟨10776350386822423492461005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7184233591214948994974003 10776350386822423492461005)
              ·
                refine ⟨4041131395058408809672877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10776350386822423492461005 4041131395058408809672877)
                ·
                  refine ⟨1515424273146903303627329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4041131395058408809672877 1515424273146903303627329)
                  ·
                    refine ⟨1136568204860177477720497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1515424273146903303627329 1136568204860177477720497)
                    ·
                      refine ⟨852426153645133108290373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1136568204860177477720497 852426153645133108290373)
                      ·
                        rfl

theorem cell23_1660094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_1660094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660094 prefixEnd_1660094 := by exact prefixLift 1660094
  have htrace : WordTrace (prefixWord ++ tailWord_1660094) baseStart_1660094 baseEnd_1660094 := by
    simpa [prefixWord, tailWord_1660094, baseEnd_1660094] using wordTrace_append hprefix tailTrace_1660094
  have hstable : (prefixWord ++ tailWord_1660094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660094).length < 2 ^ (prefixWord ++ tailWord_1660094).sum := by decide
  have hdescent : baseEnd_1660094 < baseStart_1660094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660097 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1660097 : Nat := 118140960795 + 1660097 * 2 ^ 59
def prefixEnd_1660097 : Nat := 4983230072969 + 3 ^ 40 * 1660097 * 2
def baseEnd_1660097 : Nat := 852427694087096596552859

theorem tailTrace_1660097 : CollatzResearch.WordTrace tailWord_1660097 prefixEnd_1660097 852427694087096596552859 := by
  unfold tailWord_1660097
  simp only [CollatzResearch.WordTrace]
  refine ⟨60548711866759565840370545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40365807911173043893580363 60548711866759565840370545)
  ·
    refine ⟨45411533900069674380277909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60548711866759565840370545 45411533900069674380277909)
    ·
      refine ⟨2128665651565765986575527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45411533900069674380277909 2128665651565765986575527)
      ·
        refine ⟨3192998477348648979863291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128665651565765986575527 3192998477348648979863291)
        ·
          refine ⟨4789497716022973469794937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3192998477348648979863291 4789497716022973469794937)
          ·
            refine ⟨3592123287017230102346203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4789497716022973469794937 3592123287017230102346203)
            ·
              refine ⟨5388184930525845153519305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592123287017230102346203 5388184930525845153519305)
              ·
                refine ⟨4041138697894383865139479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388184930525845153519305 4041138697894383865139479)
                ·
                  refine ⟨6061708046841575797709219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041138697894383865139479 6061708046841575797709219)
                  ·
                    refine ⟨9092562070262363696563829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6061708046841575797709219 9092562070262363696563829)
                    ·
                      refine ⟨852427694087096596552859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9092562070262363696563829 852427694087096596552859)
                      ·
                        rfl

theorem cell23_1660097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1660097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660097 prefixEnd_1660097 := by exact prefixLift 1660097
  have htrace : WordTrace (prefixWord ++ tailWord_1660097) baseStart_1660097 baseEnd_1660097 := by
    simpa [prefixWord, tailWord_1660097, baseEnd_1660097] using wordTrace_append hprefix tailTrace_1660097
  have hstable : (prefixWord ++ tailWord_1660097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660097).length < 2 ^ (prefixWord ++ tailWord_1660097).sum := by decide
  have hdescent : baseEnd_1660097 < baseStart_1660097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660117 : List Nat := [1, 3, 2, 4, 1, 3, 2, 7]
def baseStart_1660117 : Nat := 118140960795 + 1660117 * 2 ^ 59
def prefixEnd_1660117 : Nat := 4983230072969 + 3 ^ 40 * 1660117 * 2
def baseEnd_1660117 : Nat := 31571776433340241418621

theorem tailTrace_1660117 : CollatzResearch.WordTrace tailWord_1660117 prefixEnd_1660117 31571776433340241418621 := by
  unfold tailWord_1660117
  simp only [CollatzResearch.WordTrace]
  refine ⟨60549441326687109256098605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40366294217791406170732403 60549441326687109256098605)
  ·
    refine ⟨22706040497507665971036977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60549441326687109256098605 22706040497507665971036977)
    ·
      refine ⟨17029530373130749478277733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22706040497507665971036977 17029530373130749478277733)
      ·
        refine ⟨3193036944962015527177075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17029530373130749478277733 3193036944962015527177075)
        ·
          refine ⟨4789555417443023290765613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193036944962015527177075 4789555417443023290765613)
          ·
            refine ⟨1796083281541133734037105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4789555417443023290765613 1796083281541133734037105)
            ·
              refine ⟨1347062461155850300527829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1796083281541133734037105 1347062461155850300527829)
              ·
                refine ⟨31571776433340241418621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1347062461155850300527829 31571776433340241418621)
                ·
                  rfl

theorem cell23_1660117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 7].length) (baseStart_1660117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660117 prefixEnd_1660117 := by exact prefixLift 1660117
  have htrace : WordTrace (prefixWord ++ tailWord_1660117) baseStart_1660117 baseEnd_1660117 := by
    simpa [prefixWord, tailWord_1660117, baseEnd_1660117] using wordTrace_append hprefix tailTrace_1660117
  have hstable : (prefixWord ++ tailWord_1660117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660117).length < 2 ^ (prefixWord ++ tailWord_1660117).sum := by decide
  have hdescent : baseEnd_1660117 < baseStart_1660117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660150 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1660150 : Nat := 118140960795 + 1660150 * 2 ^ 59
def prefixEnd_1660150 : Nat := 4983230072969 + 3 ^ 40 * 1660150 * 2
def baseEnd_1660150 : Nat := 852454908561784889190115

theorem tailTrace_1660150 : CollatzResearch.WordTrace tailWord_1660150 prefixEnd_1660150 852454908561784889190115 := by
  unfold tailWord_1660150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3784415308472972243253119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40367096623711703928033269 3784415308472972243253119)
  ·
    refine ⟨5676622962709458364879679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3784415308472972243253119 5676622962709458364879679)
    ·
      refine ⟨8514934444064187547319519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5676622962709458364879679 8514934444064187547319519)
      ·
        refine ⟨12772401666096281320979279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8514934444064187547319519 12772401666096281320979279)
        ·
          refine ⟨19158602499144421981468919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12772401666096281320979279 19158602499144421981468919)
          ·
            refine ⟨28737903748716632972203379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19158602499144421981468919 28737903748716632972203379)
            ·
              refine ⟨43106855623074949458305069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28737903748716632972203379 43106855623074949458305069)
              ·
                refine ⟨16165070858653106046864401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43106855623074949458305069 16165070858653106046864401)
                ·
                  refine ⟨12123803143989829535148301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16165070858653106046864401 12123803143989829535148301)
                  ·
                    refine ⟨4546426178996186075680613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12123803143989829535148301 4546426178996186075680613)
                    ·
                      refine ⟨852454908561784889190115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4546426178996186075680613 852454908561784889190115)
                      ·
                        rfl

theorem cell23_1660150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1660150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660150 prefixEnd_1660150 := by exact prefixLift 1660150
  have htrace : WordTrace (prefixWord ++ tailWord_1660150) baseStart_1660150 baseEnd_1660150 := by
    simpa [prefixWord, tailWord_1660150, baseEnd_1660150] using wordTrace_append hprefix tailTrace_1660150
  have hstable : (prefixWord ++ tailWord_1660150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660150).length < 2 ^ (prefixWord ++ tailWord_1660150).sum := by decide
  have hdescent : baseEnd_1660150 < baseStart_1660150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660153 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1660153 : Nat := 118140960795 + 1660153 * 2 ^ 59
def prefixEnd_1660153 : Nat := 4983230072969 + 3 ^ 40 * 1660153 * 2
def baseEnd_1660153 : Nat := 852456449003748377452601

theorem tailTrace_1660153 : CollatzResearch.WordTrace tailWord_1660153 prefixEnd_1660153 852456449003748377452601 := by
  unfold tailWord_1660153
  simp only [CollatzResearch.WordTrace]
  refine ⟨60550754354556687404409113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40367169569704458269606075 60550754354556687404409113)
  ·
    refine ⟨45413065765917515553306835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60550754354556687404409113 45413065765917515553306835)
    ·
      refine ⟨68119598648876273329960253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45413065765917515553306835 68119598648876273329960253)
      ·
        refine ⟨25544849493328602498735095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68119598648876273329960253 25544849493328602498735095)
        ·
          refine ⟨38317274239992903748102643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25544849493328602498735095 38317274239992903748102643)
          ·
            refine ⟨57475911359989355622153965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38317274239992903748102643 57475911359989355622153965)
            ·
              refine ⟨21553466759996008358307737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57475911359989355622153965 21553466759996008358307737)
              ·
                refine ⟨16165100069997006268730803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21553466759996008358307737 16165100069997006268730803)
                ·
                  refine ⟨24247650104995509403096205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16165100069997006268730803 24247650104995509403096205)
                  ·
                    refine ⟨9092868789373316026161077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24247650104995509403096205 9092868789373316026161077)
                    ·
                      refine ⟨852456449003748377452601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9092868789373316026161077 852456449003748377452601)
                      ·
                        rfl

theorem cell23_1660153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1660153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660153 prefixEnd_1660153 := by exact prefixLift 1660153
  have htrace : WordTrace (prefixWord ++ tailWord_1660153) baseStart_1660153 baseEnd_1660153 := by
    simpa [prefixWord, tailWord_1660153, baseEnd_1660153] using wordTrace_append hprefix tailTrace_1660153
  have hstable : (prefixWord ++ tailWord_1660153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660153).length < 2 ^ (prefixWord ++ tailWord_1660153).sum := by decide
  have hdescent : baseEnd_1660153 < baseStart_1660153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660161 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_1660161 : Nat := 118140960795 + 1660161 * 2 ^ 59
def prefixEnd_1660161 : Nat := 4983230072969 + 3 ^ 40 * 1660161 * 2
def baseEnd_1660161 : Nat := 852460556848984346152565

theorem tailTrace_1660161 : CollatzResearch.WordTrace tailWord_1660161 prefixEnd_1660161 852460556848984346152565 := by
  unfold tailWord_1660161
  simp only [CollatzResearch.WordTrace]
  refine ⟨60551046138527704770700337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40367364092351803180466891 60551046138527704770700337)
  ·
    refine ⟨45413284603895778578025253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60551046138527704770700337 45413284603895778578025253)
    ·
      refine ⟨8514990863230458483379735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45413284603895778578025253 8514990863230458483379735)
      ·
        refine ⟨12772486294845687725069603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8514990863230458483379735 12772486294845687725069603)
        ·
          refine ⟨19158729442268531587604405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12772486294845687725069603 19158729442268531587604405)
          ·
            refine ⟨1796130885212674836337913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19158729442268531587604405 1796130885212674836337913)
            ·
              refine ⟨1347098163909506127253435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1796130885212674836337913 1347098163909506127253435)
              ·
                refine ⟨2020647245864259190880153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347098163909506127253435 2020647245864259190880153)
                ·
                  refine ⟨1515485434398194393160115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2020647245864259190880153 1515485434398194393160115)
                  ·
                    refine ⟨2273228151597291589740173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1515485434398194393160115 2273228151597291589740173)
                    ·
                      refine ⟨852460556848984346152565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2273228151597291589740173 852460556848984346152565)
                      ·
                        rfl

theorem cell23_1660161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_1660161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660161 prefixEnd_1660161 := by exact prefixLift 1660161
  have htrace : WordTrace (prefixWord ++ tailWord_1660161) baseStart_1660161 baseEnd_1660161 := by
    simpa [prefixWord, tailWord_1660161, baseEnd_1660161] using wordTrace_append hprefix tailTrace_1660161
  have hstable : (prefixWord ++ tailWord_1660161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660161).length < 2 ^ (prefixWord ++ tailWord_1660161).sum := by decide
  have hdescent : baseEnd_1660161 < baseStart_1660161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660240 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 4]
def baseStart_1660240 : Nat := 118140960795 + 1660240 * 2 ^ 59
def prefixEnd_1660240 : Nat := 4983230072969 + 3 ^ 40 * 1660240 * 2
def baseEnd_1660240 : Nat := 852501121820689537064701

theorem tailTrace_1660240 : CollatzResearch.WordTrace tailWord_1660240 prefixEnd_1660240 852501121820689537064701 := by
  unfold tailWord_1660240
  simp only [CollatzResearch.WordTrace]
  refine ⟨30276963752620750631413087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40369285003494334175217449 30276963752620750631413087)
  ·
    refine ⟨45415445628931125947119631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30276963752620750631413087 45415445628931125947119631)
    ·
      refine ⟨68123168443396688920679447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45415445628931125947119631 68123168443396688920679447)
      ·
        refine ⟨102184752665095033381019171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68123168443396688920679447 102184752665095033381019171)
        ·
          refine ⟨153277128997642550071528757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102184752665095033381019171 153277128997642550071528757)
          ·
            refine ⟨14369730843528989069205821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153277128997642550071528757 14369730843528989069205821)
            ·
              refine ⟨5388649066323370900952183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14369730843528989069205821 5388649066323370900952183)
              ·
                refine ⟨8082973599485056351428275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5388649066323370900952183 8082973599485056351428275)
                ·
                  refine ⟨12124460399227584527142413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8082973599485056351428275 12124460399227584527142413)
                  ·
                    refine ⟨4546672649710344197678405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12124460399227584527142413 4546672649710344197678405)
                    ·
                      refine ⟨852501121820689537064701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4546672649710344197678405 852501121820689537064701)
                      ·
                        rfl

theorem cell23_1660240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_1660240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660240 prefixEnd_1660240 := by exact prefixLift 1660240
  have htrace : WordTrace (prefixWord ++ tailWord_1660240) baseStart_1660240 baseEnd_1660240 := by
    simpa [prefixWord, tailWord_1660240, baseEnd_1660240] using wordTrace_append hprefix tailTrace_1660240
  have hstable : (prefixWord ++ tailWord_1660240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660240).length < 2 ^ (prefixWord ++ tailWord_1660240).sum := by decide
  have hdescent : baseEnd_1660240 < baseStart_1660240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660318 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1660318 : Nat := 118140960795 + 1660318 * 2 ^ 59
def prefixEnd_1660318 : Nat := 4983230072969 + 3 ^ 40 * 1660318 * 2
def baseEnd_1660318 : Nat := 284180391103913410629781

theorem tailTrace_1660318 : CollatzResearch.WordTrace tailWord_1660318 prefixEnd_1660318 284180391103913410629781 := by
  unfold tailWord_1660318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7569596549869865073020701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40371181599305947056110405 7569596549869865073020701)
  ·
    refine ⟨2838598706201199402382763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7569596549869865073020701 2838598706201199402382763)
    ·
      refine ⟨4257898059301799103574145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2838598706201199402382763 4257898059301799103574145)
      ·
        refine ⟨3193423544476349327680609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4257898059301799103574145 3193423544476349327680609)
        ·
          refine ⟨2395067658357261995760457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3193423544476349327680609 2395067658357261995760457)
          ·
            refine ⟨1796300743767946496820343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2395067658357261995760457 1796300743767946496820343)
            ·
              refine ⟨2694451115651919745230515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796300743767946496820343 2694451115651919745230515)
              ·
                refine ⟨4041676673477879617845773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694451115651919745230515 4041676673477879617845773)
                ·
                  refine ⟨1515628752554204856692165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4041676673477879617845773 1515628752554204856692165)
                  ·
                    refine ⟨284180391103913410629781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1515628752554204856692165 284180391103913410629781)
                    ·
                      rfl

theorem cell23_1660318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1660318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660318 prefixEnd_1660318 := by exact prefixLift 1660318
  have htrace : WordTrace (prefixWord ++ tailWord_1660318) baseStart_1660318 baseEnd_1660318 := by
    simpa [prefixWord, tailWord_1660318, baseEnd_1660318] using wordTrace_append hprefix tailTrace_1660318
  have hstable : (prefixWord ++ tailWord_1660318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660318).length < 2 ^ (prefixWord ++ tailWord_1660318).sum := by decide
  have hdescent : baseEnd_1660318 < baseStart_1660318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660327 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1660327 : Nat := 118140960795 + 1660327 * 2 ^ 59
def prefixEnd_1660327 : Nat := 4983230072969 + 3 ^ 40 * 1660327 * 2
def baseEnd_1660327 : Nat := 284181931545876898892267

theorem tailTrace_1660327 : CollatzResearch.WordTrace tailWord_1660327 prefixEnd_1660327 284181931545876898892267 := by
  unfold tailWord_1660327
  simp only [CollatzResearch.WordTrace]
  refine ⟨60557100655926315121243235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40371400437284210080828823 60557100655926315121243235)
  ·
    refine ⟨90835650983889472681864853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60557100655926315121243235 90835650983889472681864853)
    ·
      refine ⟨4257921139869819031962415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90835650983889472681864853 4257921139869819031962415)
      ·
        refine ⟨6386881709804728547943623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4257921139869819031962415 6386881709804728547943623)
        ·
          refine ⟨9580322564707092821915435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6386881709804728547943623 9580322564707092821915435)
          ·
            refine ⟨14370483847060639232873153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9580322564707092821915435 14370483847060639232873153)
            ·
              refine ⟨10777862885295479424654865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14370483847060639232873153 10777862885295479424654865)
              ·
                refine ⟨8083397163971609568491149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10777862885295479424654865 8083397163971609568491149)
                ·
                  refine ⟨3031273936489353588184181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8083397163971609568491149 3031273936489353588184181)
                  ·
                    refine ⟨284181931545876898892267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3031273936489353588184181 284181931545876898892267)
                    ·
                      rfl

theorem cell23_1660327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1660327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660327 prefixEnd_1660327 := by exact prefixLift 1660327
  have htrace : WordTrace (prefixWord ++ tailWord_1660327) baseStart_1660327 baseEnd_1660327 := by
    simpa [prefixWord, tailWord_1660327, baseEnd_1660327] using wordTrace_append hprefix tailTrace_1660327
  have hstable : (prefixWord ++ tailWord_1660327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660327).length < 2 ^ (prefixWord ++ tailWord_1660327).sum := by decide
  have hdescent : baseEnd_1660327 < baseStart_1660327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660367 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 5]
def baseStart_1660367 : Nat := 118140960795 + 1660367 * 2 ^ 59
def prefixEnd_1660367 : Nat := 4983230072969 + 3 ^ 40 * 1660367 * 2
def baseEnd_1660367 : Nat := 852566333863810540176617

theorem tailTrace_1660367 : CollatzResearch.WordTrace tailWord_1660367 prefixEnd_1660367 852566333863810540176617 := by
  unfold tailWord_1660367
  simp only [CollatzResearch.WordTrace]
  refine ⟨60558559575781401952699355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40372373050520934635132903 60558559575781401952699355)
  ·
    refine ⟨90837839363672102929049033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60558559575781401952699355 90837839363672102929049033)
    ·
      refine ⟨68128379522754077196786775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90837839363672102929049033 68128379522754077196786775)
      ·
        refine ⟨102192569284131115795180163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68128379522754077196786775 102192569284131115795180163)
        ·
          refine ⟨153288853926196673692770245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102192569284131115795180163 153288853926196673692770245)
          ·
            refine ⟨28741660111161876317394421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153288853926196673692770245 28741660111161876317394421)
            ·
              refine ⟨2694530635421425904755727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28741660111161876317394421 2694530635421425904755727)
              ·
                refine ⟨4041795953132138857133591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694530635421425904755727 4041795953132138857133591)
                ·
                  refine ⟨6062693929698208285700387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041795953132138857133591 6062693929698208285700387)
                  ·
                    refine ⟨9094040894547312428550581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6062693929698208285700387 9094040894547312428550581)
                    ·
                      refine ⟨852566333863810540176617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9094040894547312428550581 852566333863810540176617)
                      ·
                        rfl

theorem cell23_1660367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 5].length) (baseStart_1660367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660367 prefixEnd_1660367 := by exact prefixLift 1660367
  have htrace : WordTrace (prefixWord ++ tailWord_1660367) baseStart_1660367 baseEnd_1660367 := by
    simpa [prefixWord, tailWord_1660367, baseEnd_1660367] using wordTrace_append hprefix tailTrace_1660367
  have hstable : (prefixWord ++ tailWord_1660367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660367).length < 2 ^ (prefixWord ++ tailWord_1660367).sum := by decide
  have hdescent : baseEnd_1660367 < baseStart_1660367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660370 : List Nat := [3, 2, 2, 16]
def baseStart_1660370 : Nat := 118140960795 + 1660370 * 2 ^ 59
def prefixEnd_1660370 : Nat := 4983230072969 + 3 ^ 40 * 1660370 * 2
def baseEnd_1660370 : Nat := 389834418978406048669

theorem tailTrace_1660370 : CollatzResearch.WordTrace tailWord_1660370 prefixEnd_1660370 389834418978406048669 := by
  unfold tailWord_1660370
  simp only [CollatzResearch.WordTrace]
  refine ⟨15139667248692633366264641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40372445996513688976705709 15139667248692633366264641)
  ·
    refine ⟨11354750436519475024698481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15139667248692633366264641 11354750436519475024698481)
    ·
      refine ⟨8516062827389606268523861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11354750436519475024698481 8516062827389606268523861)
      ·
        refine ⟨389834418978406048669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 8516062827389606268523861 389834418978406048669)
        ·
          rfl

theorem cell23_1660370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 16].length) (baseStart_1660370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660370 prefixEnd_1660370 := by exact prefixLift 1660370
  have htrace : WordTrace (prefixWord ++ tailWord_1660370) baseStart_1660370 baseEnd_1660370 := by
    simpa [prefixWord, tailWord_1660370, baseEnd_1660370] using wordTrace_append hprefix tailTrace_1660370
  have hstable : (prefixWord ++ tailWord_1660370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660370).length < 2 ^ (prefixWord ++ tailWord_1660370).sum := by decide
  have hdescent : baseEnd_1660370 < baseStart_1660370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660387 : List Nat := [1, 1, 1, 6, 2, 1, 3, 8]
def baseStart_1660387 : Nat := 118140960795 + 1660387 * 2 ^ 59
def prefixEnd_1660387 : Nat := 4983230072969 + 3 ^ 40 * 1660387 * 2
def baseEnd_1660387 : Nat := 31576911239885202293575

theorem tailTrace_1660387 : CollatzResearch.WordTrace tailWord_1660387 prefixEnd_1660387 31576911239885202293575 := by
  unfold tailWord_1660387
  simp only [CollatzResearch.WordTrace]
  refine ⟨60559289035708945368427415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40372859357139296912284943 60559289035708945368427415)
  ·
    refine ⟨90838933553563418052641123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60559289035708945368427415 90838933553563418052641123)
    ·
      refine ⟨136258400330345127078961685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90838933553563418052641123 136258400330345127078961685)
      ·
        refine ⟨6387112515484927831826329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136258400330345127078961685 6387112515484927831826329)
        ·
          refine ⟨4790334386613695873869747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6387112515484927831826329 4790334386613695873869747)
          ·
            refine ⟨7185501579920543810804621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4790334386613695873869747 7185501579920543810804621)
            ·
              refine ⟨2694563092470203929051733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7185501579920543810804621 2694563092470203929051733)
              ·
                refine ⟨31576911239885202293575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2694563092470203929051733 31576911239885202293575)
                ·
                  rfl

theorem cell23_1660387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 8].length) (baseStart_1660387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660387 prefixEnd_1660387 := by exact prefixLift 1660387
  have htrace : WordTrace (prefixWord ++ tailWord_1660387) baseStart_1660387 baseEnd_1660387 := by
    simpa [prefixWord, tailWord_1660387, baseEnd_1660387] using wordTrace_append hprefix tailTrace_1660387
  have hstable : (prefixWord ++ tailWord_1660387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660387).length < 2 ^ (prefixWord ++ tailWord_1660387).sum := by decide
  have hdescent : baseEnd_1660387 < baseStart_1660387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660418 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1660418 : Nat := 118140960795 + 1660418 * 2 ^ 59
def prefixEnd_1660418 : Nat := 4983230072969 + 3 ^ 40 * 1660418 * 2
def baseEnd_1660418 : Nat := 852592521377189840638883

theorem tailTrace_1660418 : CollatzResearch.WordTrace tailWord_1660418 prefixEnd_1660418 852592521377189840638883 := by
  unfold tailWord_1660418
  simp only [CollatzResearch.WordTrace]
  refine ⟨15140104924649159415701477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40373613132397758441870605 15140104924649159415701477)
  ·
    refine ⟨2838769673371717390444027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15140104924649159415701477 2838769673371717390444027)
    ·
      refine ⟨4258154510057576085666041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2838769673371717390444027 4258154510057576085666041)
      ·
        refine ⟨3193615882543182064249531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4258154510057576085666041 3193615882543182064249531)
        ·
          refine ⟨4790423823814773096374297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193615882543182064249531 4790423823814773096374297)
          ·
            refine ⟨3592817867861079822280723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4790423823814773096374297 3592817867861079822280723)
            ·
              refine ⟨5389226801791619733421085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592817867861079822280723 5389226801791619733421085)
              ·
                refine ⟨2020960050671857400032907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5389226801791619733421085 2020960050671857400032907)
                ·
                  refine ⟨3031440076007786100049361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020960050671857400032907 3031440076007786100049361)
                  ·
                    refine ⟨2273580057005839575037021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3031440076007786100049361 2273580057005839575037021)
                    ·
                      refine ⟨852592521377189840638883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2273580057005839575037021 852592521377189840638883)
                      ·
                        rfl

theorem cell23_1660418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1660418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660418 prefixEnd_1660418 := by exact prefixLift 1660418
  have htrace : WordTrace (prefixWord ++ tailWord_1660418) baseStart_1660418 baseEnd_1660418 := by
    simpa [prefixWord, tailWord_1660418, baseEnd_1660418] using wordTrace_append hprefix tailTrace_1660418
  have hstable : (prefixWord ++ tailWord_1660418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660418).length < 2 ^ (prefixWord ++ tailWord_1660418).sum := by decide
  have hdescent : baseEnd_1660418 < baseStart_1660418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660447 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 2, 6]
def baseStart_1660447 : Nat := 118140960795 + 1660447 * 2 ^ 59
def prefixEnd_1660447 : Nat := 4983230072969 + 3 ^ 40 * 1660447 * 2
def baseEnd_1660447 : Nat := 284202470772056742392083

theorem tailTrace_1660447 : CollatzResearch.WordTrace tailWord_1660447 prefixEnd_1660447 284202470772056742392083 := by
  unfold tailWord_1660447
  simp only [CollatzResearch.WordTrace]
  refine ⟨60561477415491575615611595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40374318276994383743741063 60561477415491575615611595)
  ·
    refine ⟨90842216123237363423417393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60561477415491575615611595 90842216123237363423417393)
    ·
      refine ⟨68131662092428022567563045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90842216123237363423417393 68131662092428022567563045)
      ·
        refine ⟨12774686642330254231418071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68131662092428022567563045 12774686642330254231418071)
        ·
          refine ⟨19162029963495381347127107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12774686642330254231418071 19162029963495381347127107)
          ·
            refine ⟨28743044945243072020690661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19162029963495381347127107 28743044945243072020690661)
            ·
              refine ⟨5389320927233076003879499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28743044945243072020690661 5389320927233076003879499)
              ·
                refine ⟨8083981390849614005819249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5389320927233076003879499 8083981390849614005819249)
                ·
                  refine ⟨6062986043137210504364437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8083981390849614005819249 6062986043137210504364437)
                  ·
                    refine ⟨284202470772056742392083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6062986043137210504364437 284202470772056742392083)
                    ·
                      rfl

theorem cell23_1660447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_1660447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660447 prefixEnd_1660447 := by exact prefixLift 1660447
  have htrace : WordTrace (prefixWord ++ tailWord_1660447) baseStart_1660447 baseEnd_1660447 := by
    simpa [prefixWord, tailWord_1660447, baseEnd_1660447] using wordTrace_append hprefix tailTrace_1660447
  have hstable : (prefixWord ++ tailWord_1660447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660447).length < 2 ^ (prefixWord ++ tailWord_1660447).sum := by decide
  have hdescent : baseEnd_1660447 < baseStart_1660447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660458 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_1660458 : Nat := 118140960795 + 1660458 * 2 ^ 59
def prefixEnd_1660458 : Nat := 4983230072969 + 3 ^ 40 * 1660458 * 2
def baseEnd_1660458 : Nat := 852613060603369684138699

theorem tailTrace_1660458 : CollatzResearch.WordTrace tailWord_1660458 prefixEnd_1660458 852613060603369684138699 := by
  unfold tailWord_1660458
  simp only [CollatzResearch.WordTrace]
  refine ⟨15140469654612931123565507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40374585745634482996174685 15140469654612931123565507)
  ·
    refine ⟨22710704481919396685348261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15140469654612931123565507 22710704481919396685348261)
    ·
      refine ⟨4258257090359886878502799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22710704481919396685348261 4258257090359886878502799)
      ·
        refine ⟨6387385635539830317754199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4258257090359886878502799 6387385635539830317754199)
        ·
          refine ⟨9581078453309745476631299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6387385635539830317754199 9581078453309745476631299)
          ·
            refine ⟨14371617679964618214946949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9581078453309745476631299 14371617679964618214946949)
            ·
              refine ⟨2694678314993365915302553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14371617679964618214946949 2694678314993365915302553)
              ·
                refine ⟨2021008736245024436476915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694678314993365915302553 2021008736245024436476915)
                ·
                  refine ⟨3031513104367536654715373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021008736245024436476915 3031513104367536654715373)
                  ·
                    refine ⟨1136817414137826245518265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3031513104367536654715373 1136817414137826245518265)
                    ·
                      refine ⟨852613060603369684138699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1136817414137826245518265 852613060603369684138699)
                      ·
                        rfl

theorem cell23_1660458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_1660458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660458 prefixEnd_1660458 := by exact prefixLift 1660458
  have htrace : WordTrace (prefixWord ++ tailWord_1660458) baseStart_1660458 baseEnd_1660458 := by
    simpa [prefixWord, tailWord_1660458, baseEnd_1660458] using wordTrace_append hprefix tailTrace_1660458
  have hstable : (prefixWord ++ tailWord_1660458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660458).length < 2 ^ (prefixWord ++ tailWord_1660458).sum := by decide
  have hdescent : baseEnd_1660458 < baseStart_1660458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660471 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 4, 2, 2]
def baseStart_1660471 : Nat := 118140960795 + 1660471 * 2 ^ 59
def prefixEnd_1660471 : Nat := 4983230072969 + 3 ^ 40 * 1660471 * 2
def baseEnd_1660471 : Nat := 852619735851878133276139

theorem tailTrace_1660471 : CollatzResearch.WordTrace tailWord_1660471 prefixEnd_1660471 852619735851878133276139 := by
  unfold tailWord_1660471
  simp only [CollatzResearch.WordTrace]
  refine ⟨60562352767404627714485267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40374901844936418476323511 60562352767404627714485267)
  ·
    refine ⟨90843529151106941571727901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60562352767404627714485267 90843529151106941571727901)
    ·
      refine ⟨34066323431665103089397963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90843529151106941571727901 34066323431665103089397963)
      ·
        refine ⟨51099485147497654634096945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34066323431665103089397963 51099485147497654634096945)
        ·
          refine ⟨38324613860623240975572709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51099485147497654634096945 38324613860623240975572709)
          ·
            refine ⟨7185865098866857682919883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38324613860623240975572709 7185865098866857682919883)
            ·
              refine ⟨10778797648300286524379825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185865098866857682919883 10778797648300286524379825)
              ·
                refine ⟨8084098236225214893284869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10778797648300286524379825 8084098236225214893284869)
                ·
                  refine ⟨1515768419292227792490913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8084098236225214893284869 1515768419292227792490913)
                  ·
                    refine ⟨1136826314469170844368185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1515768419292227792490913 1136826314469170844368185)
                    ·
                      refine ⟨852619735851878133276139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1136826314469170844368185 852619735851878133276139)
                      ·
                        rfl

theorem cell23_1660471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 2, 2].length) (baseStart_1660471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660471 prefixEnd_1660471 := by exact prefixLift 1660471
  have htrace : WordTrace (prefixWord ++ tailWord_1660471) baseStart_1660471 baseEnd_1660471 := by
    simpa [prefixWord, tailWord_1660471, baseEnd_1660471] using wordTrace_append hprefix tailTrace_1660471
  have hstable : (prefixWord ++ tailWord_1660471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660471).length < 2 ^ (prefixWord ++ tailWord_1660471).sum := by decide
  have hdescent : baseEnd_1660471 < baseStart_1660471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660509 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1660509 : Nat := 118140960795 + 1660509 * 2 ^ 59
def prefixEnd_1660509 : Nat := 4983230072969 + 3 ^ 40 * 1660509 * 2
def baseEnd_1660509 : Nat := 852639248116748984600965

theorem tailTrace_1660509 : CollatzResearch.WordTrace tailWord_1660509 prefixEnd_1660509 852639248116748984600965 := by
  unfold tailWord_1660509
  simp only [CollatzResearch.WordTrace]
  refine ⟨60563738741266960204368581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40375825827511306802912387 60563738741266960204368581)
  ·
    refine ⟨11355701013987555038319109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60563738741266960204368581 11355701013987555038319109)
    ·
      refine ⟨2129193940122666569684833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11355701013987555038319109 2129193940122666569684833)
      ·
        refine ⟨1596895455091999927263625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2129193940122666569684833 1596895455091999927263625)
        ·
          refine ⟨1197671591318999945447719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1596895455091999927263625 1197671591318999945447719)
          ·
            refine ⟨1796507386978499918171579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197671591318999945447719 1796507386978499918171579)
            ·
              refine ⟨2694761080467749877257369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796507386978499918171579 2694761080467749877257369)
              ·
                refine ⟨2021070810350812407943027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694761080467749877257369 2021070810350812407943027)
                ·
                  refine ⟨3031606215526218611914541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021070810350812407943027 3031606215526218611914541)
                  ·
                    refine ⟨1136852330822331979467953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3031606215526218611914541 1136852330822331979467953)
                    ·
                      refine ⟨852639248116748984600965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1136852330822331979467953 852639248116748984600965)
                      ·
                        rfl

theorem cell23_1660509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1660509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660509 prefixEnd_1660509 := by exact prefixLift 1660509
  have htrace : WordTrace (prefixWord ++ tailWord_1660509) baseStart_1660509 baseEnd_1660509 := by
    simpa [prefixWord, tailWord_1660509, baseEnd_1660509] using wordTrace_append hprefix tailTrace_1660509
  have hstable : (prefixWord ++ tailWord_1660509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660509).length < 2 ^ (prefixWord ++ tailWord_1660509).sum := by decide
  have hdescent : baseEnd_1660509 < baseStart_1660509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660544 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 4]
def baseStart_1660544 : Nat := 118140960795 + 1660544 * 2 ^ 59
def prefixEnd_1660544 : Nat := 4983230072969 + 3 ^ 40 * 1660544 * 2
def baseEnd_1660544 : Nat := 852657219939656347663303

theorem tailTrace_1660544 : CollatzResearch.WordTrace tailWord_1660544 prefixEnd_1660544 852657219939656347663303 := by
  unfold tailWord_1660544
  simp only [CollatzResearch.WordTrace]
  refine ⟨30282507648070080590946343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40376676864093440787928457 30282507648070080590946343)
  ·
    refine ⟨45423761472105120886419515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30282507648070080590946343 45423761472105120886419515)
    ·
      refine ⟨68135642208157681329629273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45423761472105120886419515 68135642208157681329629273)
      ·
        refine ⟨51101731656118260997221955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68135642208157681329629273 51101731656118260997221955)
        ·
          refine ⟨76652597484177391495832933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51101731656118260997221955 76652597484177391495832933)
          ·
            refine ⟨14372362028283260905468675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76652597484177391495832933 14372362028283260905468675)
            ·
              refine ⟨21558543042424891358203013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14372362028283260905468675 21558543042424891358203013)
              ·
                refine ⟨4042226820454667129663065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21558543042424891358203013 4042226820454667129663065)
                ·
                  refine ⟨3031670115341000347247299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4042226820454667129663065 3031670115341000347247299)
                  ·
                    refine ⟨4547505173011500520870949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3031670115341000347247299 4547505173011500520870949)
                    ·
                      refine ⟨852657219939656347663303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4547505173011500520870949 852657219939656347663303)
                      ·
                        rfl

theorem cell23_1660544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_1660544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660544 prefixEnd_1660544 := by exact prefixLift 1660544
  have htrace : WordTrace (prefixWord ++ tailWord_1660544) baseStart_1660544 baseEnd_1660544 := by
    simpa [prefixWord, tailWord_1660544, baseEnd_1660544] using wordTrace_append hprefix tailTrace_1660544
  have hstable : (prefixWord ++ tailWord_1660544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660544).length < 2 ^ (prefixWord ++ tailWord_1660544).sum := by decide
  have hdescent : baseEnd_1660544 < baseStart_1660544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660547 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 5]
def baseStart_1660547 : Nat := 118140960795 + 1660547 * 2 ^ 59
def prefixEnd_1660547 : Nat := 4983230072969 + 3 ^ 40 * 1660547 * 2
def baseEnd_1660547 : Nat := 852658760381619835925789

theorem tailTrace_1660547 : CollatzResearch.WordTrace tailWord_1660547 prefixEnd_1660547 852658760381619835925789 := by
  unfold tailWord_1660547
  simp only [CollatzResearch.WordTrace]
  refine ⟨60565124715129292694251895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40376749810086195129501263 60565124715129292694251895)
  ·
    refine ⟨90847687072693939041377843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60565124715129292694251895 90847687072693939041377843)
    ·
      refine ⟨136271530609040908562066765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90847687072693939041377843 136271530609040908562066765)
      ·
        refine ⟨51101823978390340710775037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136271530609040908562066765 51101823978390340710775037)
        ·
          refine ⟨19163183991896377766540639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51101823978390340710775037 19163183991896377766540639)
          ·
            refine ⟨28744775987844566649810959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19163183991896377766540639 28744775987844566649810959)
            ·
              refine ⟨43117163981766849974716439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28744775987844566649810959 43117163981766849974716439)
              ·
                refine ⟨64675745972650274962074659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43117163981766849974716439 64675745972650274962074659)
                ·
                  refine ⟨97013618958975412443111989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64675745972650274962074659 97013618958975412443111989)
                  ·
                    refine ⟨9095026777403944916541749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97013618958975412443111989 9095026777403944916541749)
                    ·
                      refine ⟨852658760381619835925789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9095026777403944916541749 852658760381619835925789)
                      ·
                        rfl

theorem cell23_1660547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_1660547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660547 prefixEnd_1660547 := by exact prefixLift 1660547
  have htrace : WordTrace (prefixWord ++ tailWord_1660547) baseStart_1660547 baseEnd_1660547 := by
    simpa [prefixWord, tailWord_1660547, baseEnd_1660547] using wordTrace_append hprefix tailTrace_1660547
  have hstable : (prefixWord ++ tailWord_1660547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660547).length < 2 ^ (prefixWord ++ tailWord_1660547).sum := by decide
  have hdescent : baseEnd_1660547 < baseStart_1660547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660575 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 2, 5]
def baseStart_1660575 : Nat := 118140960795 + 1660575 * 2 ^ 59
def prefixEnd_1660575 : Nat := 4983230072969 + 3 ^ 40 * 1660575 * 2
def baseEnd_1660575 : Nat := 284224379279981908791887

theorem tailTrace_1660575 : CollatzResearch.WordTrace tailWord_1660575 prefixEnd_1660575 284224379279981908791887 := by
  unfold tailWord_1660575
  simp only [CollatzResearch.WordTrace]
  refine ⟨60566145959027853476271179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40377430639351902317514119 60566145959027853476271179)
  ·
    refine ⟨90849218938541780214406769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60566145959027853476271179 90849218938541780214406769)
    ·
      refine ⟨68136914203906335160805077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90849218938541780214406769 68136914203906335160805077)
      ·
        refine ⟨1596958926654054730331369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 68136914203906335160805077 1596958926654054730331369)
        ·
          refine ⟨1197719194990541047748527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1596958926654054730331369 1197719194990541047748527)
          ·
            refine ⟨1796578792485811571622791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197719194990541047748527 1796578792485811571622791)
            ·
              refine ⟨2694868188728717357434187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796578792485811571622791 2694868188728717357434187)
              ·
                refine ⟨4042302283093076036151281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694868188728717357434187 4042302283093076036151281)
                ·
                  refine ⟨3031726712319807027113461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4042302283093076036151281 3031726712319807027113461)
                  ·
                    refine ⟨284224379279981908791887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3031726712319807027113461 284224379279981908791887)
                    ·
                      rfl

theorem cell23_1660575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 5].length) (baseStart_1660575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660575 prefixEnd_1660575 := by exact prefixLift 1660575
  have htrace : WordTrace (prefixWord ++ tailWord_1660575) baseStart_1660575 baseEnd_1660575 := by
    simpa [prefixWord, tailWord_1660575, baseEnd_1660575] using wordTrace_append hprefix tailTrace_1660575
  have hstable : (prefixWord ++ tailWord_1660575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660575).length < 2 ^ (prefixWord ++ tailWord_1660575).sum := by decide
  have hdescent : baseEnd_1660575 < baseStart_1660575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660578 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1660578 : Nat := 118140960795 + 1660578 * 2 ^ 59
def prefixEnd_1660578 : Nat := 4983230072969 + 3 ^ 40 * 1660578 * 2
def baseEnd_1660578 : Nat := 852674678281909214638147

theorem tailTrace_1660578 : CollatzResearch.WordTrace tailWord_1660578 prefixEnd_1660578 852674678281909214638147 := by
  unfold tailWord_1660578
  simp only [CollatzResearch.WordTrace]
  refine ⟨15141563844504246247157597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40377503585344656659086925 15141563844504246247157597)
  ·
    refine ⟨5678086441689092342684099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15141563844504246247157597 5678086441689092342684099)
    ·
      refine ⟨8517129662533638514026149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5678086441689092342684099 8517129662533638514026149)
      ·
        refine ⟨1596961811725057221379903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8517129662533638514026149 1596961811725057221379903)
        ·
          refine ⟨2395442717587585832069855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596961811725057221379903 2395442717587585832069855)
          ·
            refine ⟨3593164076381378748104783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395442717587585832069855 3593164076381378748104783)
            ·
              refine ⟨5389746114572068122157175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593164076381378748104783 5389746114572068122157175)
              ·
                refine ⟨8084619171858102183235763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5389746114572068122157175 8084619171858102183235763)
                ·
                  refine ⟨12126928757787153274853645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8084619171858102183235763 12126928757787153274853645)
                  ·
                    refine ⟨4547598284170182478070117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12126928757787153274853645 4547598284170182478070117)
                    ·
                      refine ⟨852674678281909214638147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4547598284170182478070117 852674678281909214638147)
                      ·
                        rfl

theorem cell23_1660578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1660578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660578 prefixEnd_1660578 := by exact prefixLift 1660578
  have htrace : WordTrace (prefixWord ++ tailWord_1660578) baseStart_1660578 baseEnd_1660578 := by
    simpa [prefixWord, tailWord_1660578, baseEnd_1660578] using wordTrace_append hprefix tailTrace_1660578
  have hstable : (prefixWord ++ tailWord_1660578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660578).length < 2 ^ (prefixWord ++ tailWord_1660578).sum := by decide
  have hdescent : baseEnd_1660578 < baseStart_1660578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660581 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 2, 2, 3]
def baseStart_1660581 : Nat := 118140960795 + 1660581 * 2 ^ 59
def prefixEnd_1660581 : Nat := 4983230072969 + 3 ^ 40 * 1660581 * 2
def baseEnd_1660581 : Nat := 852676218723872702900633

theorem tailTrace_1660581 : CollatzResearch.WordTrace tailWord_1660581 prefixEnd_1660581 852676218723872702900633 := by
  unfold tailWord_1660581
  simp only [CollatzResearch.WordTrace]
  refine ⟨60566364797006116500989597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40377576531337411000659731 60566364797006116500989597)
  ·
    refine ⟨22712386798877293687871099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60566364797006116500989597 22712386798877293687871099)
    ·
      refine ⟨34068580198315940531806649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22712386798877293687871099 34068580198315940531806649)
      ·
        refine ⟨25551435148736955398854987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34068580198315940531806649 25551435148736955398854987)
        ·
          refine ⟨38327152723105433098282481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25551435148736955398854987 38327152723105433098282481)
          ·
            refine ⟨28745364542329074823711861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38327152723105433098282481 28745364542329074823711861)
            ·
              refine ⟨2694877925843350764722987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28745364542329074823711861 2694877925843350764722987)
              ·
                refine ⟨4042316888765026147084481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694877925843350764722987 4042316888765026147084481)
                ·
                  refine ⟨3031737666573769610313361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4042316888765026147084481 3031737666573769610313361)
                  ·
                    refine ⟨2273803249930327207735021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3031737666573769610313361 2273803249930327207735021)
                    ·
                      refine ⟨852676218723872702900633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2273803249930327207735021 852676218723872702900633)
                      ·
                        rfl

theorem cell23_1660581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_1660581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660581 prefixEnd_1660581 := by exact prefixLift 1660581
  have htrace : WordTrace (prefixWord ++ tailWord_1660581) baseStart_1660581 baseEnd_1660581 := by
    simpa [prefixWord, tailWord_1660581, baseEnd_1660581] using wordTrace_append hprefix tailTrace_1660581
  have hstable : (prefixWord ++ tailWord_1660581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660581).length < 2 ^ (prefixWord ++ tailWord_1660581).sum := by decide
  have hdescent : baseEnd_1660581 < baseStart_1660581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660604 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1660604 : Nat := 118140960795 + 1660604 * 2 ^ 59
def prefixEnd_1660604 : Nat := 4983230072969 + 3 ^ 40 * 1660604 * 2
def baseEnd_1660604 : Nat := 852688028778926112913027

theorem tailTrace_1660604 : CollatzResearch.WordTrace tailWord_1660604 prefixEnd_1660604 852688028778926112913027 := by
  unfold tailWord_1660604
  simp only [CollatzResearch.WordTrace]
  refine ⟨30283601837961395714538433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40378135783948527619384577 30283601837961395714538433)
  ·
    refine ⟨22712701378471046785903825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30283601837961395714538433 22712701378471046785903825)
    ·
      refine ⟨17034526033853285089427869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22712701378471046785903825 17034526033853285089427869)
      ·
        refine ⟨6387947262694981908535451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17034526033853285089427869 6387947262694981908535451)
        ·
          refine ⟨9581920894042472862803177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6387947262694981908535451 9581920894042472862803177)
          ·
            refine ⟨7186440670531854647102383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9581920894042472862803177 7186440670531854647102383)
            ·
              refine ⟨10779661005797781970653575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7186440670531854647102383 10779661005797781970653575)
              ·
                refine ⟨16169491508696672955980363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10779661005797781970653575 16169491508696672955980363)
                ·
                  refine ⟨24254237263045009433970545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16169491508696672955980363 24254237263045009433970545)
                  ·
                    refine ⟨18190677947283757075477909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24254237263045009433970545 18190677947283757075477909)
                    ·
                      refine ⟨852688028778926112913027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18190677947283757075477909 852688028778926112913027)
                      ·
                        rfl

theorem cell23_1660604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1660604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660604 prefixEnd_1660604 := by exact prefixLift 1660604
  have htrace : WordTrace (prefixWord ++ tailWord_1660604) baseStart_1660604 baseEnd_1660604 := by
    simpa [prefixWord, tailWord_1660604, baseEnd_1660604] using wordTrace_append hprefix tailTrace_1660604
  have hstable : (prefixWord ++ tailWord_1660604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660604).length < 2 ^ (prefixWord ++ tailWord_1660604).sum := by decide
  have hdescent : baseEnd_1660604 < baseStart_1660604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660618 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 6]
def baseStart_1660618 : Nat := 118140960795 + 1660618 * 2 ^ 59
def prefixEnd_1660618 : Nat := 4983230072969 + 3 ^ 40 * 1660618 * 2
def baseEnd_1660618 : Nat := 94743913056454339793107

theorem tailTrace_1660618 : CollatzResearch.WordTrace tailWord_1660618 prefixEnd_1660618 94743913056454339793107 := by
  unfold tailWord_1660618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15141928574468017955021627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40378476198581381213391005 15141928574468017955021627)
  ·
    refine ⟨22712892861702026932532441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15141928574468017955021627 22712892861702026932532441)
    ·
      refine ⟨17034669646276520199399331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22712892861702026932532441 17034669646276520199399331)
      ·
        refine ⟨25552004469414780299098997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17034669646276520199399331 25552004469414780299098997)
        ·
          refine ⟨2395500419007635653040531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25552004469414780299098997 2395500419007635653040531)
          ·
            refine ⟨3593250628511453479560797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395500419007635653040531 3593250628511453479560797)
            ·
              refine ⟨1347468985691795054835299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3593250628511453479560797 1347468985691795054835299)
              ·
                refine ⟨2021203478537692582252949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347468985691795054835299 2021203478537692582252949)
                ·
                  refine ⟨94743913056454339793107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2021203478537692582252949 94743913056454339793107)
                  ·
                    rfl

theorem cell23_1660618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_1660618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660618 prefixEnd_1660618 := by exact prefixLift 1660618
  have htrace : WordTrace (prefixWord ++ tailWord_1660618) baseStart_1660618 baseEnd_1660618 := by
    simpa [prefixWord, tailWord_1660618, baseEnd_1660618] using wordTrace_append hprefix tailTrace_1660618
  have hstable : (prefixWord ++ tailWord_1660618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660618).length < 2 ^ (prefixWord ++ tailWord_1660618).sum := by decide
  have hdescent : baseEnd_1660618 < baseStart_1660618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660631 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 1, 5]
def baseStart_1660631 : Nat := 118140960795 + 1660631 * 2 ^ 59
def prefixEnd_1660631 : Nat := 4983230072969 + 3 ^ 40 * 1660631 * 2
def baseEnd_1660631 : Nat := 284233964252199169091801

theorem tailTrace_1660631 : CollatzResearch.WordTrace tailWord_1660631 prefixEnd_1660631 284233964252199169091801 := by
  unfold tailWord_1660631
  simp only [CollatzResearch.WordTrace]
  refine ⟨60568188446824975040309747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40378792297883316693539831 60568188446824975040309747)
  ·
    refine ⟨90852282670237462560464621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60568188446824975040309747 90852282670237462560464621)
    ·
      refine ⟨34069606001339048460174233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90852282670237462560464621 34069606001339048460174233)
      ·
        refine ⟨25552204501004286345130675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34069606001339048460174233 25552204501004286345130675)
        ·
          refine ⟨38328306751506429517696013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25552204501004286345130675 38328306751506429517696013)
          ·
            refine ⟨14373115031814911069136005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38328306751506429517696013 14373115031814911069136005)
            ·
              refine ⟨2694959068465295825463001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14373115031814911069136005 2694959068465295825463001)
              ·
                refine ⟨2021219301348971869097251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694959068465295825463001 2021219301348971869097251)
                ·
                  refine ⟨3031828952023457803645877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021219301348971869097251 3031828952023457803645877)
                  ·
                    refine ⟨284233964252199169091801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3031828952023457803645877 284233964252199169091801)
                    ·
                      rfl

theorem cell23_1660631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_1660631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660631 prefixEnd_1660631 := by exact prefixLift 1660631
  have htrace : WordTrace (prefixWord ++ tailWord_1660631) baseStart_1660631 baseEnd_1660631 := by
    simpa [prefixWord, tailWord_1660631, baseEnd_1660631] using wordTrace_append hprefix tailTrace_1660631
  have hstable : (prefixWord ++ tailWord_1660631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660631).length < 2 ^ (prefixWord ++ tailWord_1660631).sum := by decide
  have hdescent : baseEnd_1660631 < baseStart_1660631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660644 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_1660644 : Nat := 118140960795 + 1660644 * 2 ^ 59
def prefixEnd_1660644 : Nat := 4983230072969 + 3 ^ 40 * 1660644 * 2
def baseEnd_1660644 : Nat := 284236189335035318804281

theorem tailTrace_1660644 : CollatzResearch.WordTrace tailWord_1660644 prefixEnd_1660644 284236189335035318804281 := by
  unfold tailWord_1660644
  simp only [CollatzResearch.WordTrace]
  refine ⟨30284331297888939130266493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40379108397185252173688657 30284331297888939130266493)
  ·
    refine ⟨11356624236708352173849935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30284331297888939130266493 11356624236708352173849935)
    ·
      refine ⟨17034936355062528260774903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11356624236708352173849935 17034936355062528260774903)
      ·
        refine ⟨25552404532593792391162355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17034936355062528260774903 25552404532593792391162355)
        ·
          refine ⟨38328606798890688586743533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25552404532593792391162355 38328606798890688586743533)
          ·
            refine ⟨14373227549584008220028825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38328606798890688586743533 14373227549584008220028825)
            ·
              refine ⟨10779920662188006165021619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14373227549584008220028825 10779920662188006165021619)
              ·
                refine ⟨16169880993282009247532429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10779920662188006165021619 16169880993282009247532429)
                ·
                  refine ⟨6063705372480753467824661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16169880993282009247532429 6063705372480753467824661)
                  ·
                    refine ⟨284236189335035318804281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6063705372480753467824661 284236189335035318804281)
                    ·
                      rfl

theorem cell23_1660644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_1660644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660644 prefixEnd_1660644 := by exact prefixLift 1660644
  have htrace : WordTrace (prefixWord ++ tailWord_1660644) baseStart_1660644 baseEnd_1660644 := by
    simpa [prefixWord, tailWord_1660644, baseEnd_1660644] using wordTrace_append hprefix tailTrace_1660644
  have hstable : (prefixWord ++ tailWord_1660644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660644).length < 2 ^ (prefixWord ++ tailWord_1660644).sum := by decide
  have hdescent : baseEnd_1660644 < baseStart_1660644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660651 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 4]
def baseStart_1660651 : Nat := 118140960795 + 1660651 * 2 ^ 59
def prefixEnd_1660651 : Nat := 4983230072969 + 3 ^ 40 * 1660651 * 2
def baseEnd_1660651 : Nat := 852712162369687429025311

theorem tailTrace_1660651 : CollatzResearch.WordTrace tailWord_1660651 prefixEnd_1660651 852712162369687429025311 := by
  unfold tailWord_1660651
  simp only [CollatzResearch.WordTrace]
  refine ⟨60568917906752518456037807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40379278604501678970691871 60568917906752518456037807)
  ·
    refine ⟨90853376860128777684056711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60568917906752518456037807 90853376860128777684056711)
    ·
      refine ⟨136280065290193166526085067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90853376860128777684056711 136280065290193166526085067)
      ·
        refine ⟨204420097935289749789127601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136280065290193166526085067 204420097935289749789127601)
        ·
          refine ⟨153315073451467312341845701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204420097935289749789127601 153315073451467312341845701)
          ·
            refine ⟨28746576272150121064096069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153315073451467312341845701 28746576272150121064096069)
            ·
              refine ⟨5389983051028147699518013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28746576272150121064096069 5389983051028147699518013)
              ·
                refine ⟨2021243644135555387319255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5389983051028147699518013 2021243644135555387319255)
                ·
                  refine ⟨3031865466203333080978883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021243644135555387319255 3031865466203333080978883)
                  ·
                    refine ⟨4547798199304999621468325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3031865466203333080978883 4547798199304999621468325)
                    ·
                      refine ⟨852712162369687429025311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4547798199304999621468325 852712162369687429025311)
                      ·
                        rfl

theorem cell23_1660651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 4].length) (baseStart_1660651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660651 prefixEnd_1660651 := by exact prefixLift 1660651
  have htrace : WordTrace (prefixWord ++ tailWord_1660651) baseStart_1660651 baseEnd_1660651 := by
    simpa [prefixWord, tailWord_1660651, baseEnd_1660651] using wordTrace_append hprefix tailTrace_1660651
  have hstable : (prefixWord ++ tailWord_1660651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660651).length < 2 ^ (prefixWord ++ tailWord_1660651).sum := by decide
  have hdescent : baseEnd_1660651 < baseStart_1660651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660664 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_1660664 : Nat := 118140960795 + 1660664 * 2 ^ 59
def prefixEnd_1660664 : Nat := 4983230072969 + 3 ^ 40 * 1660664 * 2
def baseEnd_1660664 : Nat := 852718837618195878162751

theorem tailTrace_1660664 : CollatzResearch.WordTrace tailWord_1660664 prefixEnd_1660664 852718837618195878162751 := by
  unfold tailWord_1660664
  simp only [CollatzResearch.WordTrace]
  refine ⟨30284696027852710838130523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40379594703803614450840697 30284696027852710838130523)
  ·
    refine ⟨45427044041779066257195785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30284696027852710838130523 45427044041779066257195785)
    ·
      refine ⟨34070283031334299692896839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45427044041779066257195785 34070283031334299692896839)
      ·
        refine ⟨51105424547001449539345259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34070283031334299692896839 51105424547001449539345259)
        ·
          refine ⟨76658136820502174309017889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51105424547001449539345259 76658136820502174309017889)
          ·
            refine ⟨57493602615376630731763417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76658136820502174309017889 57493602615376630731763417)
            ·
              refine ⟨43120201961532473048822563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57493602615376630731763417 43120201961532473048822563)
              ·
                refine ⟨64680302942298709573233845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43120201961532473048822563 64680302942298709573233845)
                ·
                  refine ⟨6063778400840504022490673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64680302942298709573233845 6063778400840504022490673)
                  ·
                    refine ⟨4547833800630378016868005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6063778400840504022490673 4547833800630378016868005)
                    ·
                      refine ⟨852718837618195878162751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4547833800630378016868005 852718837618195878162751)
                      ·
                        rfl

theorem cell23_1660664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_1660664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660664 prefixEnd_1660664 := by exact prefixLift 1660664
  have htrace : WordTrace (prefixWord ++ tailWord_1660664) baseStart_1660664 baseEnd_1660664 := by
    simpa [prefixWord, tailWord_1660664, baseEnd_1660664] using wordTrace_append hprefix tailTrace_1660664
  have hstable : (prefixWord ++ tailWord_1660664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660664).length < 2 ^ (prefixWord ++ tailWord_1660664).sum := by decide
  have hdescent : baseEnd_1660664 < baseStart_1660664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660705 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 1, 2, 3]
def baseStart_1660705 : Nat := 118140960795 + 1660705 * 2 ^ 59
def prefixEnd_1660705 : Nat := 4983230072969 + 3 ^ 40 * 1660705 * 2
def baseEnd_1660705 : Nat := 852739890325030217750063

theorem tailTrace_1660705 : CollatzResearch.WordTrace tailWord_1660705 prefixEnd_1660705 852739890325030217750063 := by
  unfold tailWord_1660705
  simp only [CollatzResearch.WordTrace]
  refine ⟨60570887448556885678503569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40380591632371257119002379 60570887448556885678503569)
  ·
    refine ⟨45428165586417664258877677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60570887448556885678503569 45428165586417664258877677)
    ·
      refine ⟨17035562094906624097079129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45428165586417664258877677 17035562094906624097079129)
      ·
        refine ⟨12776671571179968072809347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17035562094906624097079129 12776671571179968072809347)
        ·
          refine ⟨19165007356769952109214021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12776671571179968072809347 19165007356769952109214021)
          ·
            refine ⟨3593438879394366020477629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19165007356769952109214021 3593438879394366020477629)
            ·
              refine ⟨1347539579772887257679111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3593438879394366020477629 1347539579772887257679111)
              ·
                refine ⟨2021309369659330886518667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347539579772887257679111 2021309369659330886518667)
                ·
                  refine ⟨3031964054488996329778001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021309369659330886518667 3031964054488996329778001)
                  ·
                    refine ⟨2273973040866747247333501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3031964054488996329778001 2273973040866747247333501)
                    ·
                      refine ⟨852739890325030217750063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2273973040866747247333501 852739890325030217750063)
                      ·
                        rfl

theorem cell23_1660705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_1660705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660705 prefixEnd_1660705 := by exact prefixLift 1660705
  have htrace : WordTrace (prefixWord ++ tailWord_1660705) baseStart_1660705 baseEnd_1660705 := by
    simpa [prefixWord, tailWord_1660705, baseEnd_1660705] using wordTrace_append hprefix tailTrace_1660705
  have hstable : (prefixWord ++ tailWord_1660705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660705).length < 2 ^ (prefixWord ++ tailWord_1660705).sum := by decide
  have hdescent : baseEnd_1660705 < baseStart_1660705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660728 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 3, 3, 2]
def baseStart_1660728 : Nat := 118140960795 + 1660728 * 2 ^ 59
def prefixEnd_1660728 : Nat := 4983230072969 + 3 ^ 40 * 1660728 * 2
def baseEnd_1660728 : Nat := 852751700380083627762457

theorem tailTrace_1660728 : CollatzResearch.WordTrace tailWord_1660728 prefixEnd_1660728 852751700380083627762457 := by
  unfold tailWord_1660728
  simp only [CollatzResearch.WordTrace]
  refine ⟨30285863163736780303295419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40381150884982373737727225 30285863163736780303295419)
  ·
    refine ⟨45428794745605170454943129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30285863163736780303295419 45428794745605170454943129)
    ·
      refine ⟨34071596059203877841207347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45428794745605170454943129 34071596059203877841207347)
      ·
        refine ⟨51107394088805816761811021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34071596059203877841207347 51107394088805816761811021)
        ·
          refine ⟨19165272783302181285679133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51107394088805816761811021 19165272783302181285679133)
          ·
            refine ⟨7186977293738317982129675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19165272783302181285679133 7186977293738317982129675)
            ·
              refine ⟨10780465940607476973194513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7186977293738317982129675 10780465940607476973194513)
              ·
                refine ⟨8085349455455607729895885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10780465940607476973194513 8085349455455607729895885)
                ·
                  refine ⟨3032006045795852898710957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8085349455455607729895885 3032006045795852898710957)
                  ·
                    refine ⟨1137002267173444837016609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3032006045795852898710957 1137002267173444837016609)
                    ·
                      refine ⟨852751700380083627762457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1137002267173444837016609 852751700380083627762457)
                      ·
                        rfl

theorem cell23_1660728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 3, 2].length) (baseStart_1660728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660728 prefixEnd_1660728 := by exact prefixLift 1660728
  have htrace : WordTrace (prefixWord ++ tailWord_1660728) baseStart_1660728 baseEnd_1660728 := by
    simpa [prefixWord, tailWord_1660728, baseEnd_1660728] using wordTrace_append hprefix tailTrace_1660728
  have hstable : (prefixWord ++ tailWord_1660728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660728).length < 2 ^ (prefixWord ++ tailWord_1660728).sum := by decide
  have hdescent : baseEnd_1660728 < baseStart_1660728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660775 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_1660775 : Nat := 118140960795 + 1660775 * 2 ^ 59
def prefixEnd_1660775 : Nat := 4983230072969 + 3 ^ 40 * 1660775 * 2
def baseEnd_1660775 : Nat := 852775833970844943874741

theorem tailTrace_1660775 : CollatzResearch.WordTrace tailWord_1660775 prefixEnd_1660775 852775833970844943874741 := by
  unfold tailWord_1660775
  simp only [CollatzResearch.WordTrace]
  refine ⟨60573440558303287633551779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40382293705535525089034519 60573440558303287633551779)
  ·
    refine ⟨90860160837454931450327669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60573440558303287633551779 90860160837454931450327669)
    ·
      refine ⟨8518140078511399823468219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90860160837454931450327669 8518140078511399823468219)
      ·
        refine ⟨12777210117767099735202329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8518140078511399823468219 12777210117767099735202329)
        ·
          refine ⟨9582907588325324801401747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12777210117767099735202329 9582907588325324801401747)
          ·
            refine ⟨14374361382487987202102621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9582907588325324801401747 14374361382487987202102621)
            ·
              refine ⟨5390385518432995200788483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14374361382487987202102621 5390385518432995200788483)
              ·
                refine ⟨8085578277649492801182725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5390385518432995200788483 8085578277649492801182725)
                ·
                  refine ⟨1516045927059279900221761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8085578277649492801182725 1516045927059279900221761)
                  ·
                    refine ⟨1137034445294459925166321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1516045927059279900221761 1137034445294459925166321)
                    ·
                      refine ⟨852775833970844943874741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1137034445294459925166321 852775833970844943874741)
                      ·
                        rfl

theorem cell23_1660775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_1660775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660775 prefixEnd_1660775 := by exact prefixLift 1660775
  have htrace : WordTrace (prefixWord ++ tailWord_1660775) baseStart_1660775 baseEnd_1660775 := by
    simpa [prefixWord, tailWord_1660775, baseEnd_1660775] using wordTrace_append hprefix tailTrace_1660775
  have hstable : (prefixWord ++ tailWord_1660775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660775).length < 2 ^ (prefixWord ++ tailWord_1660775).sum := by decide
  have hdescent : baseEnd_1660775 < baseStart_1660775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660781 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 7]
def baseStart_1660781 : Nat := 118140960795 + 1660781 * 2 ^ 59
def prefixEnd_1660781 : Nat := 4983230072969 + 3 ^ 40 * 1660781 * 2
def baseEnd_1660781 : Nat := 94753212761641324488857

theorem tailTrace_1660781 : CollatzResearch.WordTrace tailWord_1660781 prefixEnd_1660781 94753212761641324488857 := by
  unfold tailWord_1660781
  simp only [CollatzResearch.WordTrace]
  refine ⟨60573659396281550658270197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40382439597521033772180131 60573659396281550658270197)
  ·
    refine ⟨5678780568401395374212831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60573659396281550658270197 5678780568401395374212831)
    ·
      refine ⟨8518170852602093061319247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5678780568401395374212831 8518170852602093061319247)
      ·
        refine ⟨12777256278903139591978871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8518170852602093061319247 12777256278903139591978871)
        ·
          refine ⟨19165884418354709387968307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12777256278903139591978871 19165884418354709387968307)
          ·
            refine ⟨28748826627532064081952461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19165884418354709387968307 28748826627532064081952461)
            ·
              refine ⟨10780809985324524030732173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28748826627532064081952461 10780809985324524030732173)
              ·
                refine ⟨4042803744496696511524565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10780809985324524030732173 4042803744496696511524565)
                ·
                  refine ⟨94753212761641324488857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4042803744496696511524565 94753212761641324488857)
                  ·
                    rfl

theorem cell23_1660781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_1660781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660781 prefixEnd_1660781 := by exact prefixLift 1660781
  have htrace : WordTrace (prefixWord ++ tailWord_1660781) baseStart_1660781 baseEnd_1660781 := by
    simpa [prefixWord, tailWord_1660781, baseEnd_1660781] using wordTrace_append hprefix tailTrace_1660781
  have hstable : (prefixWord ++ tailWord_1660781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660781).length < 2 ^ (prefixWord ++ tailWord_1660781).sum := by decide
  have hdescent : baseEnd_1660781 < baseStart_1660781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660811 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 2, 5]
def baseStart_1660811 : Nat := 118140960795 + 1660811 * 2 ^ 59
def prefixEnd_1660811 : Nat := 4983230072969 + 3 ^ 40 * 1660811 * 2
def baseEnd_1660811 : Nat := 284264773091468934341525

theorem tailTrace_1660811 : CollatzResearch.WordTrace tailWord_1660811 prefixEnd_1660811 284264773091468934341525 := by
  unfold tailWord_1660811
  simp only [CollatzResearch.WordTrace]
  refine ⟨60574753586172865781862287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40383169057448577187908191 60574753586172865781862287)
  ·
    refine ⟨90862130379259298672793431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60574753586172865781862287 90862130379259298672793431)
    ·
      refine ⟨136293195568888948009190147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90862130379259298672793431 136293195568888948009190147)
      ·
        refine ⟨204439793353333422013785221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136293195568888948009190147 204439793353333422013785221)
        ·
          refine ⟨38332461253750016627584729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204439793353333422013785221 38332461253750016627584729)
          ·
            refine ⟨28749345940312512470688547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38332461253750016627584729 28749345940312512470688547)
            ·
              refine ⟨43124018910468768706032821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28749345940312512470688547 43124018910468768706032821)
              ·
                refine ⟨4042876772856447066190577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43124018910468768706032821 4042876772856447066190577)
                ·
                  refine ⟨3032157579642335299642933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4042876772856447066190577 3032157579642335299642933)
                  ·
                    refine ⟨284264773091468934341525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3032157579642335299642933 284264773091468934341525)
                    ·
                      rfl

theorem cell23_1660811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 5].length) (baseStart_1660811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660811 prefixEnd_1660811 := by exact prefixLift 1660811
  have htrace : WordTrace (prefixWord ++ tailWord_1660811) baseStart_1660811 baseEnd_1660811 := by
    simpa [prefixWord, tailWord_1660811, baseEnd_1660811] using wordTrace_append hprefix tailTrace_1660811
  have hstable : (prefixWord ++ tailWord_1660811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660811).length < 2 ^ (prefixWord ++ tailWord_1660811).sum := by decide
  have hdescent : baseEnd_1660811 < baseStart_1660811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660821 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_1660821 : Nat := 118140960795 + 1660821 * 2 ^ 59
def prefixEnd_1660821 : Nat := 4983230072969 + 3 ^ 40 * 1660821 * 2
def baseEnd_1660821 : Nat := 852799454080951763899529

theorem tailTrace_1660821 : CollatzResearch.WordTrace tailWord_1660821 prefixEnd_1660821 852799454080951763899529 := by
  unfold tailWord_1660821
  simp only [CollatzResearch.WordTrace]
  refine ⟨60575118316136637489726317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40383412210757758326484211 60575118316136637489726317)
  ·
    refine ⟨22715669368551239058647369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60575118316136637489726317 22715669368551239058647369)
    ·
      refine ⟨17036752026413429293985527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22715669368551239058647369 17036752026413429293985527)
      ·
        refine ⟨25555128039620143940978291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17036752026413429293985527 25555128039620143940978291)
        ·
          refine ⟨38332692059430215911467437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25555128039620143940978291 38332692059430215911467437)
          ·
            refine ⟨14374759522286330966800289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38332692059430215911467437 14374759522286330966800289)
            ·
              refine ⟨10781069641714748225100217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14374759522286330966800289 10781069641714748225100217)
              ·
                refine ⟨8085802231286061168825163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10781069641714748225100217 8085802231286061168825163)
                ·
                  refine ⟨12128703346929091753237745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8085802231286061168825163 12128703346929091753237745)
                  ·
                    refine ⟨9096527510196818814928309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12128703346929091753237745 9096527510196818814928309)
                    ·
                      refine ⟨852799454080951763899529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9096527510196818814928309 852799454080951763899529)
                      ·
                        rfl

theorem cell23_1660821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_1660821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660821 prefixEnd_1660821 := by exact prefixLift 1660821
  have htrace : WordTrace (prefixWord ++ tailWord_1660821) baseStart_1660821 baseEnd_1660821 := by
    simpa [prefixWord, tailWord_1660821, baseEnd_1660821] using wordTrace_append hprefix tailTrace_1660821
  have hstable : (prefixWord ++ tailWord_1660821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660821).length < 2 ^ (prefixWord ++ tailWord_1660821).sum := by decide
  have hdescent : baseEnd_1660821 < baseStart_1660821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660828 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1660828 : Nat := 118140960795 + 1660828 * 2 ^ 59
def prefixEnd_1660828 : Nat := 4983230072969 + 3 ^ 40 * 1660828 * 2
def baseEnd_1660828 : Nat := 284267682815177745503999

theorem tailTrace_1660828 : CollatzResearch.WordTrace tailWord_1660828 prefixEnd_1660828 284267682815177745503999 := by
  unfold tailWord_1660828
  simp only [CollatzResearch.WordTrace]
  refine ⟨30287686813555638842615569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40383582418074185123487425 30287686813555638842615569)
  ·
    refine ⟨22715765110166729131961677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30287686813555638842615569 22715765110166729131961677)
    ·
      refine ⟨8518411916312523424485629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22715765110166729131961677 8518411916312523424485629)
      ·
        refine ⟨3194404468617196284182111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8518411916312523424485629 3194404468617196284182111)
        ·
          refine ⟨4791606702925794426273167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3194404468617196284182111 4791606702925794426273167)
          ·
            refine ⟨7187410054388691639409751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4791606702925794426273167 7187410054388691639409751)
            ·
              refine ⟨10781115081583037459114627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7187410054388691639409751 10781115081583037459114627)
              ·
                refine ⟨16171672622374556188671941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10781115081583037459114627 16171672622374556188671941)
                ·
                  refine ⟨3032188616695229285375989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16171672622374556188671941 3032188616695229285375989)
                  ·
                    refine ⟨284267682815177745503999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3032188616695229285375989 284267682815177745503999)
                    ·
                      rfl

theorem cell23_1660828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1660828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660828 prefixEnd_1660828 := by exact prefixLift 1660828
  have htrace : WordTrace (prefixWord ++ tailWord_1660828) baseStart_1660828 baseEnd_1660828 := by
    simpa [prefixWord, tailWord_1660828, baseEnd_1660828] using wordTrace_append hprefix tailTrace_1660828
  have hstable : (prefixWord ++ tailWord_1660828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660828).length < 2 ^ (prefixWord ++ tailWord_1660828).sum := by decide
  have hdescent : baseEnd_1660828 < baseStart_1660828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660875 : List Nat := [1, 1, 1, 1, 3, 4, 2, 5, 1, 4]
def baseStart_1660875 : Nat := 118140960795 + 1660875 * 2 ^ 59
def prefixEnd_1660875 : Nat := 4983230072969 + 3 ^ 40 * 1660875 * 2
def baseEnd_1660875 : Nat := 284275727345431517541427

theorem tailTrace_1660875 : CollatzResearch.WordTrace tailWord_1660875 prefixEnd_1660875 284275727345431517541427 := by
  unfold tailWord_1660875
  simp only [CollatzResearch.WordTrace]
  refine ⟨60577087857941004712192079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40384725238627336474794719 60577087857941004712192079)
  ·
    refine ⟨90865631786911507068288119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60577087857941004712192079 90865631786911507068288119)
    ·
      refine ⟨136298447680367260602432179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90865631786911507068288119 136298447680367260602432179)
      ·
        refine ⟨204447671520550890903648269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136298447680367260602432179 204447671520550890903648269)
        ·
          refine ⟨76667876820206584088868101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204447671520550890903648269 76667876820206584088868101)
          ·
            refine ⟨14375226903788734516662769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76667876820206584088868101 14375226903788734516662769)
            ·
              refine ⟨10781420177841550887497077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14375226903788734516662769 10781420177841550887497077)
              ·
                refine ⟨1010758141672645395702851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10781420177841550887497077 1010758141672645395702851)
                ·
                  refine ⟨1516137212508968093554277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010758141672645395702851 1516137212508968093554277)
                  ·
                    refine ⟨284275727345431517541427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1516137212508968093554277 284275727345431517541427)
                    ·
                      rfl

theorem cell23_1660875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 1, 4].length) (baseStart_1660875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660875 prefixEnd_1660875 := by exact prefixLift 1660875
  have htrace : WordTrace (prefixWord ++ tailWord_1660875) baseStart_1660875 baseEnd_1660875 := by
    simpa [prefixWord, tailWord_1660875, baseEnd_1660875] using wordTrace_append hprefix tailTrace_1660875
  have hstable : (prefixWord ++ tailWord_1660875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660875).length < 2 ^ (prefixWord ++ tailWord_1660875).sum := by decide
  have hdescent : baseEnd_1660875 < baseStart_1660875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660885 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1660885 : Nat := 118140960795 + 1660885 * 2 ^ 59
def prefixEnd_1660885 : Nat := 4983230072969 + 3 ^ 40 * 1660885 * 2
def baseEnd_1660885 : Nat := 852832316842839513499235

theorem tailTrace_1660885 : CollatzResearch.WordTrace tailWord_1660885 prefixEnd_1660885 852832316842839513499235 := by
  unfold tailWord_1660885
  simp only [CollatzResearch.WordTrace]
  refine ⟨60577452587904776420056109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40384968391936517613370739 60577452587904776420056109)
  ·
    refine ⟨22716544720464291157521041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60577452587904776420056109 22716544720464291157521041)
    ·
      refine ⟨17037408540348218368140781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22716544720464291157521041 17037408540348218368140781)
      ·
        refine ⟨6389028202630581888052793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17037408540348218368140781 6389028202630581888052793)
        ·
          refine ⟨4791771151972936416039595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6389028202630581888052793 4791771151972936416039595)
          ·
            refine ⟨7187656727959404624059393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4791771151972936416039595 7187656727959404624059393)
            ·
              refine ⟨5390742545969553468044545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7187656727959404624059393 5390742545969553468044545)
              ·
                refine ⟨4043056909477165101033409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5390742545969553468044545 4043056909477165101033409)
                ·
                  refine ⟨3032292682107873825775057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4043056909477165101033409 3032292682107873825775057)
                  ·
                    refine ⟨2274219511580905369331293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3032292682107873825775057 2274219511580905369331293)
                    ·
                      refine ⟨852832316842839513499235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2274219511580905369331293 852832316842839513499235)
                      ·
                        rfl

theorem cell23_1660885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1660885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660885 prefixEnd_1660885 := by exact prefixLift 1660885
  have htrace : WordTrace (prefixWord ++ tailWord_1660885) baseStart_1660885 baseEnd_1660885 := by
    simpa [prefixWord, tailWord_1660885, baseEnd_1660885] using wordTrace_append hprefix tailTrace_1660885
  have hstable : (prefixWord ++ tailWord_1660885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660885).length < 2 ^ (prefixWord ++ tailWord_1660885).sum := by decide
  have hdescent : baseEnd_1660885 < baseStart_1660885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660888 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 6]
def baseStart_1660888 : Nat := 118140960795 + 1660888 * 2 ^ 59
def prefixEnd_1660888 : Nat := 4983230072969 + 3 ^ 40 * 1660888 * 2
def baseEnd_1660888 : Nat := 94759317476089222417969

theorem tailTrace_1660888 : CollatzResearch.WordTrace tailWord_1660888 prefixEnd_1660888 94759317476089222417969 := by
  unfold tailWord_1660888
  simp only [CollatzResearch.WordTrace]
  refine ⟨30288781003446953966207659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40385041337929271954943545 30288781003446953966207659)
  ·
    refine ⟨45433171505170430949311489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30288781003446953966207659 45433171505170430949311489)
    ·
      refine ⟨34074878628877823211983617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45433171505170430949311489 34074878628877823211983617)
      ·
        refine ⟨25556158971658367408987713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34074878628877823211983617 25556158971658367408987713)
        ·
          refine ⟨19167119228743775556740785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25556158971658367408987713 19167119228743775556740785)
          ·
            refine ⟨14375339421557831667555589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19167119228743775556740785 14375339421557831667555589)
            ·
              refine ⟨2695376141542093437666673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14375339421557831667555589 2695376141542093437666673)
              ·
                refine ⟨2021532106156570078250005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2695376141542093437666673 2021532106156570078250005)
                ·
                  refine ⟨94759317476089222417969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2021532106156570078250005 94759317476089222417969)
                  ·
                    rfl

theorem cell23_1660888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 6].length) (baseStart_1660888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660888 prefixEnd_1660888 := by exact prefixLift 1660888
  have htrace : WordTrace (prefixWord ++ tailWord_1660888) baseStart_1660888 baseEnd_1660888 := by
    simpa [prefixWord, tailWord_1660888, baseEnd_1660888] using wordTrace_append hprefix tailTrace_1660888
  have hstable : (prefixWord ++ tailWord_1660888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660888).length < 2 ^ (prefixWord ++ tailWord_1660888).sum := by decide
  have hdescent : baseEnd_1660888 < baseStart_1660888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660911 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_1660911 : Nat := 118140960795 + 1660911 * 2 ^ 59
def prefixEnd_1660911 : Nat := 4983230072969 + 3 ^ 40 * 1660911 * 2
def baseEnd_1660911 : Nat := 852845667339856411774115

theorem tailTrace_1660911 : CollatzResearch.WordTrace tailWord_1660911 prefixEnd_1660911 852845667339856411774115 := by
  unfold tailWord_1660911
  simp only [CollatzResearch.WordTrace]
  refine ⟨60578400885810582860502587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40385600590540388573668391 60578400885810582860502587)
  ·
    refine ⟨90867601328715874290753881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60578400885810582860502587 90867601328715874290753881)
    ·
      refine ⟨68150700996536905718065411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90867601328715874290753881 68150700996536905718065411)
      ·
        refine ⟨102226051494805358577098117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68150700996536905718065411 102226051494805358577098117)
        ·
          refine ⟨19167384655276004733205897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102226051494805358577098117 19167384655276004733205897)
          ·
            refine ⟨14375538491457003549904423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19167384655276004733205897 14375538491457003549904423)
            ·
              refine ⟨21563307737185505324856635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14375538491457003549904423 21563307737185505324856635)
              ·
                refine ⟨32344961605778257987284953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21563307737185505324856635 32344961605778257987284953)
                ·
                  refine ⟨24258721204333693490463715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32344961605778257987284953 24258721204333693490463715)
                  ·
                    refine ⟨36388081806500540235695573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24258721204333693490463715 36388081806500540235695573)
                    ·
                      refine ⟨852845667339856411774115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36388081806500540235695573 852845667339856411774115)
                      ·
                        rfl

theorem cell23_1660911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_1660911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660911 prefixEnd_1660911 := by exact prefixLift 1660911
  have htrace : WordTrace (prefixWord ++ tailWord_1660911) baseStart_1660911 baseEnd_1660911 := by
    simpa [prefixWord, tailWord_1660911, baseEnd_1660911] using wordTrace_append hprefix tailTrace_1660911
  have hstable : (prefixWord ++ tailWord_1660911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660911).length < 2 ^ (prefixWord ++ tailWord_1660911).sum := by decide
  have hdescent : baseEnd_1660911 < baseStart_1660911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660935 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 1, 5]
def baseStart_1660935 : Nat := 118140960795 + 1660935 * 2 ^ 59
def prefixEnd_1660935 : Nat := 4983230072969 + 3 ^ 40 * 1660935 * 2
def baseEnd_1660935 : Nat := 284285996958521439291335

theorem tailTrace_1660935 : CollatzResearch.WordTrace tailWord_1660935 prefixEnd_1660935 284285996958521439291335 := by
  unfold tailWord_1660935
  simp only [CollatzResearch.WordTrace]
  refine ⟨60579276237723634959376259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40386184158482423306250839 60579276237723634959376259)
  ·
    refine ⟨90868914356585452439064389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60579276237723634959376259 90868914356585452439064389)
    ·
      refine ⟨17037921441859772332324573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90868914356585452439064389 17037921441859772332324573)
      ·
        refine ⟨6389220540697414624621715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17037921441859772332324573 6389220540697414624621715)
        ·
          refine ⟨9583830811046121936932573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6389220540697414624621715 9583830811046121936932573)
          ·
            refine ⟨3593936554142295726349715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9583830811046121936932573 3593936554142295726349715)
            ·
              refine ⟨5390904831213443589524573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593936554142295726349715 5390904831213443589524573)
              ·
                refine ⟨2021589311705041346071715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5390904831213443589524573 2021589311705041346071715)
                ·
                  refine ⟨3032383967557562019107573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021589311705041346071715 3032383967557562019107573)
                  ·
                    refine ⟨284285996958521439291335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3032383967557562019107573 284285996958521439291335)
                    ·
                      rfl

theorem cell23_1660935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_1660935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660935 prefixEnd_1660935 := by exact prefixLift 1660935
  have htrace : WordTrace (prefixWord ++ tailWord_1660935) baseStart_1660935 baseEnd_1660935 := by
    simpa [prefixWord, tailWord_1660935, baseEnd_1660935] using wordTrace_append hprefix tailTrace_1660935
  have hstable : (prefixWord ++ tailWord_1660935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660935).length < 2 ^ (prefixWord ++ tailWord_1660935).sum := by decide
  have hdescent : baseEnd_1660935 < baseStart_1660935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660965 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 1, 6]
def baseStart_1660965 : Nat := 118140960795 + 1660965 * 2 ^ 59
def prefixEnd_1660965 : Nat := 4983230072969 + 3 ^ 40 * 1660965 * 2
def baseEnd_1660965 : Nat := 284291131765066400166289

theorem tailTrace_1660965 : CollatzResearch.WordTrace tailWord_1660965 prefixEnd_1660965 284291131765066400166289 := by
  unfold tailWord_1660965
  simp only [CollatzResearch.WordTrace]
  refine ⟨60580370427614950082968349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40386913618409966721978899 60580370427614950082968349)
  ·
    refine ⟨22717638910355606281113131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60580370427614950082968349 22717638910355606281113131)
    ·
      refine ⟨34076458365533409421669697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22717638910355606281113131 34076458365533409421669697)
      ·
        refine ⟨25557343774150057066252273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34076458365533409421669697 25557343774150057066252273)
        ·
          refine ⟨19168007830612542799689205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25557343774150057066252273 19168007830612542799689205)
          ·
            refine ⟨1797000734119925887470863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19168007830612542799689205 1797000734119925887470863)
            ·
              refine ⟨2695501101179888831206295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797000734119925887470863 2695501101179888831206295)
              ·
                refine ⟨4043251651769833246809443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695501101179888831206295 4043251651769833246809443)
                ·
                  refine ⟨6064877477654749870214165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4043251651769833246809443 6064877477654749870214165)
                  ·
                    refine ⟨284291131765066400166289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6064877477654749870214165 284291131765066400166289)
                    ·
                      rfl

theorem cell23_1660965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_1660965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660965 prefixEnd_1660965 := by exact prefixLift 1660965
  have htrace : WordTrace (prefixWord ++ tailWord_1660965) baseStart_1660965 baseEnd_1660965 := by
    simpa [prefixWord, tailWord_1660965, baseEnd_1660965] using wordTrace_append hprefix tailTrace_1660965
  have hstable : (prefixWord ++ tailWord_1660965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660965).length < 2 ^ (prefixWord ++ tailWord_1660965).sum := by decide
  have hdescent : baseEnd_1660965 < baseStart_1660965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660978 : List Nat := [3, 2, 1, 1, 2, 4, 1, 9]
def baseStart_1660978 : Nat := 118140960795 + 1660978 * 2 ^ 59
def prefixEnd_1660978 : Nat := 4983230072969 + 3 ^ 40 * 1660978 * 2
def baseEnd_1660978 : Nat := 31588150760878061097641

theorem tailTrace_1660978 : CollatzResearch.WordTrace tailWord_1660978 prefixEnd_1660978 31588150760878061097641 := by
  unfold tailWord_1660978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15145211144141963325797897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40387229717711902202127725 15145211144141963325797897)
  ·
    refine ⟨11358908358106472494348423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15145211144141963325797897 11358908358106472494348423)
    ·
      refine ⟨17038362537159708741522635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11358908358106472494348423 17038362537159708741522635)
      ·
        refine ⟨25557543805739563112283953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17038362537159708741522635 25557543805739563112283953)
        ·
          refine ⟨19168157854304672334212965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25557543805739563112283953 19168157854304672334212965)
          ·
            refine ⟨3594029597682126062664931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19168157854304672334212965 3594029597682126062664931)
            ·
              refine ⟨5391044396523189093997397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3594029597682126062664931 5391044396523189093997397)
              ·
                refine ⟨31588150760878061097641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5391044396523189093997397 31588150760878061097641)
                ·
                  rfl

theorem cell23_1660978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 9].length) (baseStart_1660978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1660978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1660978 prefixEnd_1660978 := by exact prefixLift 1660978
  have htrace : WordTrace (prefixWord ++ tailWord_1660978) baseStart_1660978 baseEnd_1660978 := by
    simpa [prefixWord, tailWord_1660978, baseEnd_1660978] using wordTrace_append hprefix tailTrace_1660978
  have hstable : (prefixWord ++ tailWord_1660978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660978).length < 2 ^ (prefixWord ++ tailWord_1660978).sum := by decide
  have hdescent : baseEnd_1660978 < baseStart_1660978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661026 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1661026 : Nat := 118140960795 + 1661026 * 2 ^ 59
def prefixEnd_1661026 : Nat := 4983230072969 + 3 ^ 40 * 1661026 * 2
def baseEnd_1661026 : Nat := 852904717615123461836087

theorem tailTrace_1661026 : CollatzResearch.WordTrace tailWord_1661026 prefixEnd_1661026 852904717615123461836087 := by
  unfold tailWord_1661026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15145648820098489375234733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40388396853595971667292621 15145648820098489375234733)
  ·
    refine ⟨5679618307536933515713025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15145648820098489375234733 5679618307536933515713025)
    ·
      refine ⟨4259713730652700136784769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5679618307536933515713025 4259713730652700136784769)
      ·
        refine ⟨3194785297989525102588577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4259713730652700136784769 3194785297989525102588577)
        ·
          refine ⟨2396088973492143826941433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3194785297989525102588577 2396088973492143826941433)
          ·
            refine ⟨1797066730119107870206075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396088973492143826941433 1797066730119107870206075)
            ·
              refine ⟨2695600095178661805309113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797066730119107870206075 2695600095178661805309113)
              ·
                refine ⟨2021700071383996353981835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2695600095178661805309113 2021700071383996353981835)
                ·
                  refine ⟨3032550107075994530972753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021700071383996353981835 3032550107075994530972753)
                  ·
                    refine ⟨2274412580306995898229565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3032550107075994530972753 2274412580306995898229565)
                    ·
                      refine ⟨852904717615123461836087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2274412580306995898229565 852904717615123461836087)
                      ·
                        rfl

theorem cell23_1661026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1661026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661026 prefixEnd_1661026 := by exact prefixLift 1661026
  have htrace : WordTrace (prefixWord ++ tailWord_1661026) baseStart_1661026 baseEnd_1661026 := by
    simpa [prefixWord, tailWord_1661026, baseEnd_1661026] using wordTrace_append hprefix tailTrace_1661026
  have hstable : (prefixWord ++ tailWord_1661026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661026).length < 2 ^ (prefixWord ++ tailWord_1661026).sum := by decide
  have hdescent : baseEnd_1661026 < baseStart_1661026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661079 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 1, 4, 2]
def baseStart_1661079 : Nat := 118140960795 + 1661079 * 2 ^ 59
def prefixEnd_1661079 : Nat := 4983230072969 + 3 ^ 40 * 1661079 * 2
def baseEnd_1661079 : Nat := 852931932089811754473343

theorem tailTrace_1661079 : CollatzResearch.WordTrace tailWord_1661079 prefixEnd_1661079 852931932089811754473343 := by
  unfold tailWord_1661079
  simp only [CollatzResearch.WordTrace]
  refine ⟨60584528349201947552618291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40389685566134631701745527 60584528349201947552618291)
  ·
    refine ⟨90876792523802921328927437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60584528349201947552618291 90876792523802921328927437)
    ·
      refine ⟨34078797196426095498347789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90876792523802921328927437 34078797196426095498347789)
      ·
        refine ⟨12779548948659785811880421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34078797196426095498347789 12779548948659785811880421)
        ·
          refine ⟨2396165427873709839727579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12779548948659785811880421 2396165427873709839727579)
          ·
            refine ⟨3594248141810564759591369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396165427873709839727579 3594248141810564759591369)
            ·
              refine ⟨2695686106357923569693527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3594248141810564759591369 2695686106357923569693527)
              ·
                refine ⟨4043529159536885354540291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695686106357923569693527 4043529159536885354540291)
                ·
                  refine ⟨6065293739305328031810437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4043529159536885354540291 6065293739305328031810437)
                  ·
                    refine ⟨1137242576119749005964457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6065293739305328031810437 1137242576119749005964457)
                    ·
                      refine ⟨852931932089811754473343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1137242576119749005964457 852931932089811754473343)
                      ·
                        rfl

theorem cell23_1661079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_1661079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661079 prefixEnd_1661079 := by exact prefixLift 1661079
  have htrace : WordTrace (prefixWord ++ tailWord_1661079) baseStart_1661079 baseEnd_1661079 := by
    simpa [prefixWord, tailWord_1661079, baseEnd_1661079] using wordTrace_append hprefix tailTrace_1661079
  have hstable : (prefixWord ++ tailWord_1661079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661079).length < 2 ^ (prefixWord ++ tailWord_1661079).sum := by decide
  have hdescent : baseEnd_1661079 < baseStart_1661079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661085 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 7]
def baseStart_1661085 : Nat := 118140960795 + 1661085 * 2 ^ 59
def prefixEnd_1661085 : Nat := 4983230072969 + 3 ^ 40 * 1661085 * 2
def baseEnd_1661085 : Nat := 94770556997082081222035

theorem tailTrace_1661085 : CollatzResearch.WordTrace tailWord_1661085 prefixEnd_1661085 94770556997082081222035 := by
  unfold tailWord_1661085
  simp only [CollatzResearch.WordTrace]
  refine ⟨60584747187180210577336709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40389831458120140384891139 60584747187180210577336709)
  ·
    refine ⟨11359640097596289483250633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60584747187180210577336709 11359640097596289483250633)
    ·
      refine ⟨8519730073197217112437975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11359640097596289483250633 8519730073197217112437975)
      ·
        refine ⟨12779595109795825668656963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8519730073197217112437975 12779595109795825668656963)
        ·
          refine ⟨19169392664693738502985445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12779595109795825668656963 19169392664693738502985445)
          ·
            refine ⟨3594261124630075969309771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19169392664693738502985445 3594261124630075969309771)
            ·
              refine ⟨5391391686945113953964657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3594261124630075969309771 5391391686945113953964657)
              ·
                refine ⟨4043543765208835465473493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5391391686945113953964657 4043543765208835465473493)
                ·
                  refine ⟨94770556997082081222035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4043543765208835465473493 94770556997082081222035)
                  ·
                    rfl

theorem cell23_1661085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_1661085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661085 prefixEnd_1661085 := by exact prefixLift 1661085
  have htrace : WordTrace (prefixWord ++ tailWord_1661085) baseStart_1661085 baseEnd_1661085 := by
    simpa [prefixWord, tailWord_1661085, baseEnd_1661085] using wordTrace_append hprefix tailTrace_1661085
  have hstable : (prefixWord ++ tailWord_1661085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661085).length < 2 ^ (prefixWord ++ tailWord_1661085).sum := by decide
  have hdescent : baseEnd_1661085 < baseStart_1661085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661192 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 6]
def baseStart_1661192 : Nat := 118140960795 + 1661192 * 2 ^ 59
def prefixEnd_1661192 : Nat := 4983230072969 + 3 ^ 40 * 1661192 * 2
def baseEnd_1661192 : Nat := 94776661711529979151147

theorem tailTrace_1661192 : CollatzResearch.WordTrace tailWord_1661192 prefixEnd_1661192 94776661711529979151147 := by
  unfold tailWord_1661192
  simp only [CollatzResearch.WordTrace]
  refine ⟨30294324898896283925740915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40392433198528378567654553 30294324898896283925740915)
  ·
    refine ⟨45441487348344425888611373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30294324898896283925740915 45441487348344425888611373)
    ·
      refine ⟨17040557755629159708229265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45441487348344425888611373 17040557755629159708229265)
      ·
        refine ⟨12780418316721869781171949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17040557755629159708229265 12780418316721869781171949)
        ·
          refine ⟨4792656868770701167939481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12780418316721869781171949 4792656868770701167939481)
          ·
            refine ⟨3594492651578025875954611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4792656868770701167939481 3594492651578025875954611)
            ·
              refine ⟨5391738977367038813931917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3594492651578025875954611 5391738977367038813931917)
              ·
                refine ⟨2021902116512639555224469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5391738977367038813931917 2021902116512639555224469)
                ·
                  refine ⟨94776661711529979151147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2021902116512639555224469 94776661711529979151147)
                  ·
                    rfl

theorem cell23_1661192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 6].length) (baseStart_1661192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661192 prefixEnd_1661192 := by exact prefixLift 1661192
  have htrace : WordTrace (prefixWord ++ tailWord_1661192) baseStart_1661192 baseEnd_1661192 := by
    simpa [prefixWord, tailWord_1661192, baseEnd_1661192] using wordTrace_append hprefix tailTrace_1661192
  have hstable : (prefixWord ++ tailWord_1661192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661192).length < 2 ^ (prefixWord ++ tailWord_1661192).sum := by decide
  have hdescent : baseEnd_1661192 < baseStart_1661192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661235 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 3, 6]
def baseStart_1661235 : Nat := 118140960795 + 1661235 * 2 ^ 59
def prefixEnd_1661235 : Nat := 4983230072969 + 3 ^ 40 * 1661235 * 2
def baseEnd_1661235 : Nat := 284337345023971048040875

theorem tailTrace_1661235 : CollatzResearch.WordTrace tailWord_1661235 prefixEnd_1661235 284337345023971048040875 := by
  unfold tailWord_1661235
  simp only [CollatzResearch.WordTrace]
  refine ⟨60590218136636786195297159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40393478757757857463531439 60590218136636786195297159)
  ·
    refine ⟨90885327204955179292945739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60590218136636786195297159 90885327204955179292945739)
    ·
      refine ⟨136327990807432768939418609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90885327204955179292945739 136327990807432768939418609)
      ·
        refine ⟨102245993105574576704563957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136327990807432768939418609 102245993105574576704563957)
        ·
          refine ⟨9585561853647616566052871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102245993105574576704563957 9585561853647616566052871)
          ·
            refine ⟨14378342780471424849079307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9585561853647616566052871 14378342780471424849079307)
            ·
              refine ⟨21567514170707137273618961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14378342780471424849079307 21567514170707137273618961)
              ·
                refine ⟨16175635628030352955214221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21567514170707137273618961 16175635628030352955214221)
                ·
                  refine ⟨6065863360511382358205333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16175635628030352955214221 6065863360511382358205333)
                  ·
                    refine ⟨284337345023971048040875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6065863360511382358205333 284337345023971048040875)
                    ·
                      rfl

theorem cell23_1661235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 6].length) (baseStart_1661235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661235 prefixEnd_1661235 := by exact prefixLift 1661235
  have htrace : WordTrace (prefixWord ++ tailWord_1661235) baseStart_1661235 baseEnd_1661235 := by
    simpa [prefixWord, tailWord_1661235, baseEnd_1661235] using wordTrace_append hprefix tailTrace_1661235
  have hstable : (prefixWord ++ tailWord_1661235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661235).length < 2 ^ (prefixWord ++ tailWord_1661235).sum := by decide
  have hdescent : baseEnd_1661235 < baseStart_1661235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661242 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_1661242 : Nat := 118140960795 + 1661242 * 2 ^ 59
def prefixEnd_1661242 : Nat := 4983230072969 + 3 ^ 40 * 1661242 * 2
def baseEnd_1661242 : Nat := 853015629436494616735093

theorem tailTrace_1661242 : CollatzResearch.WordTrace tailWord_1661242 prefixEnd_1661242 853015629436494616735093 := by
  unfold tailWord_1661242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15147618361902856597700495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40393648965074284260534653 15147618361902856597700495)
  ·
    refine ⟨22721427542854284896550743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15147618361902856597700495 22721427542854284896550743)
    ·
      refine ⟨34082141314281427344826115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22721427542854284896550743 34082141314281427344826115)
      ·
        refine ⟨51123211971422141017239173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34082141314281427344826115 51123211971422141017239173)
        ·
          refine ⟨9585602244641651440732345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51123211971422141017239173 9585602244641651440732345)
          ·
            refine ⟨7189201683481238580549259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9585602244641651440732345 7189201683481238580549259)
            ·
              refine ⟨10783802525221857870823889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7189201683481238580549259 10783802525221857870823889)
              ·
                refine ⟨8087851893916393403117917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10783802525221857870823889 8087851893916393403117917)
                ·
                  refine ⟨3032944460218647526169219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8087851893916393403117917 3032944460218647526169219)
                  ·
                    refine ⟨4549416690327971289253829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3032944460218647526169219 4549416690327971289253829)
                    ·
                      refine ⟨853015629436494616735093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4549416690327971289253829 853015629436494616735093)
                      ·
                        rfl

theorem cell23_1661242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_1661242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661242 prefixEnd_1661242 := by exact prefixLift 1661242
  have htrace : WordTrace (prefixWord ++ tailWord_1661242) baseStart_1661242 baseEnd_1661242 := by
    simpa [prefixWord, tailWord_1661242, baseEnd_1661242] using wordTrace_append hprefix tailTrace_1661242
  have hstable : (prefixWord ++ tailWord_1661242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661242).length < 2 ^ (prefixWord ++ tailWord_1661242).sum := by decide
  have hdescent : baseEnd_1661242 < baseStart_1661242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661282 : List Nat := [3, 3, 2, 1, 1, 3, 10]
def baseStart_1661282 : Nat := 118140960795 + 1661282 * 2 ^ 59
def prefixEnd_1661282 : Nat := 4983230072969 + 3 ^ 40 * 1661282 * 2
def baseEnd_1661282 : Nat := 10531310724230548891789

theorem tailTrace_1661282 : CollatzResearch.WordTrace tailWord_1661282 prefixEnd_1661282 10531310724230548891789 := by
  unfold tailWord_1661282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15147983091866628305564525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40394621578311008814838733 15147983091866628305564525)
  ·
    refine ⟨5680493659449985614586697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15147983091866628305564525 5680493659449985614586697)
    ·
      refine ⟨4260370244587489210940023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5680493659449985614586697 4260370244587489210940023)
      ·
        refine ⟨6390555366881233816410035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4260370244587489210940023 6390555366881233816410035)
        ·
          refine ⟨9585833050321850724615053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6390555366881233816410035 9585833050321850724615053)
          ·
            refine ⟨3594687393870694021730645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9585833050321850724615053 3594687393870694021730645)
            ·
              refine ⟨10531310724230548891789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3594687393870694021730645 10531310724230548891789)
              ·
                rfl

theorem cell23_1661282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 10].length) (baseStart_1661282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661282 prefixEnd_1661282 := by exact prefixLift 1661282
  have htrace : WordTrace (prefixWord ++ tailWord_1661282) baseStart_1661282 baseEnd_1661282 := by
    simpa [prefixWord, tailWord_1661282, baseEnd_1661282] using wordTrace_append hprefix tailTrace_1661282
  have hstable : (prefixWord ++ tailWord_1661282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661282).length < 2 ^ (prefixWord ++ tailWord_1661282).sum := by decide
  have hdescent : baseEnd_1661282 < baseStart_1661282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
