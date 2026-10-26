import V185TrunkScan23Chunk0414

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2452612 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_2452612 : Nat := 118140960795 + 2452612 * 2 ^ 59
def prefixEnd_2452612 : Nat := 4983230072969 + 3 ^ 40 * 2452612 * 2
def baseEnd_2452612 : Nat := 1259368814985063377970649

theorem tailTrace_2452612 : CollatzResearch.WordTrace tailWord_2452612 prefixEnd_2452612 1259368814985063377970649 := by
  unfold tailWord_2452612
  simp only [CollatzResearch.WordTrace]
  refine ⟨44727054295306535813272045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59636072393742047751029393 44727054295306535813272045)
  ·
    refine ⟨16772645360739950929977017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44727054295306535813272045 16772645360739950929977017)
    ·
      refine ⟨12579484020554963197482763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16772645360739950929977017 12579484020554963197482763)
      ·
        refine ⟨18869226030832444796224145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12579484020554963197482763 18869226030832444796224145)
        ·
          refine ⟨14151919523124333597168109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18869226030832444796224145 14151919523124333597168109)
          ·
            refine ⟨5306969821171625098938041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14151919523124333597168109 5306969821171625098938041)
            ·
              refine ⟨3980227365878718824203531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5306969821171625098938041 3980227365878718824203531)
              ·
                refine ⟨5970341048818078236305297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980227365878718824203531 5970341048818078236305297)
                ·
                  refine ⟨4477755786613558677228973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5970341048818078236305297 4477755786613558677228973)
                  ·
                    refine ⟨1679158419980084503960865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4477755786613558677228973 1679158419980084503960865)
                    ·
                      refine ⟨1259368814985063377970649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679158419980084503960865 1259368814985063377970649)
                      ·
                        rfl

theorem cell23_2452612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_2452612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452612 prefixEnd_2452612 := by exact prefixLift 2452612
  have htrace : WordTrace (prefixWord ++ tailWord_2452612) baseStart_2452612 baseEnd_2452612 := by
    simpa [prefixWord, tailWord_2452612, baseEnd_2452612] using wordTrace_append hprefix tailTrace_2452612
  have hstable : (prefixWord ++ tailWord_2452612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452612).length < 2 ^ (prefixWord ++ tailWord_2452612).sum := by decide
  have hdescent : baseEnd_2452612 < baseStart_2452612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452618 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_2452618 : Nat := 118140960795 + 2452618 * 2 ^ 59
def prefixEnd_2452618 : Nat := 4983230072969 + 3 ^ 40 * 2452618 * 2
def baseEnd_2452618 : Nat := 419790631956330118165207

theorem tailTrace_2452618 : CollatzResearch.WordTrace tailWord_2452618 prefixEnd_2452618 419790631956330118165207 := by
  unfold tailWord_2452618
  simp only [CollatzResearch.WordTrace]
  refine ⟨22363581857147833662815627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59636218285727556434175005 22363581857147833662815627)
  ·
    refine ⟨33545372785721750494223441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22363581857147833662815627 33545372785721750494223441)
    ·
      refine ⟨25159029589291312870667581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33545372785721750494223441 25159029589291312870667581)
      ·
        refine ⟨9434636095984242326500343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25159029589291312870667581 9434636095984242326500343)
        ·
          refine ⟨14151954143976363489750515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9434636095984242326500343 14151954143976363489750515)
          ·
            refine ⟨21227931215964545234625773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14151954143976363489750515 21227931215964545234625773)
            ·
              refine ⟨7960474205986704462984665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21227931215964545234625773 7960474205986704462984665)
              ·
                refine ⟨5970355654490028347238499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7960474205986704462984665 5970355654490028347238499)
                ·
                  refine ⟨8955533481735042520857749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5970355654490028347238499 8955533481735042520857749)
                  ·
                    refine ⟨419790631956330118165207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8955533481735042520857749 419790631956330118165207)
                    ·
                      rfl

theorem cell23_2452618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_2452618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452618 prefixEnd_2452618 := by exact prefixLift 2452618
  have htrace : WordTrace (prefixWord ++ tailWord_2452618) baseStart_2452618 baseEnd_2452618 := by
    simpa [prefixWord, tailWord_2452618, baseEnd_2452618] using wordTrace_append hprefix tailTrace_2452618
  have hstable : (prefixWord ++ tailWord_2452618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452618).length < 2 ^ (prefixWord ++ tailWord_2452618).sum := by decide
  have hdescent : baseEnd_2452618 < baseStart_2452618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452622 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_2452622 : Nat := 118140960795 + 2452622 * 2 ^ 59
def prefixEnd_2452622 : Nat := 4983230072969 + 3 ^ 40 * 2452622 * 2
def baseEnd_2452622 : Nat := 419791316597202779615201

theorem tailTrace_2452622 : CollatzResearch.WordTrace tailWord_2452622 prefixEnd_2452622 419791316597202779615201 := by
  unfold tailWord_2452622
  simp only [CollatzResearch.WordTrace]
  refine ⟨11181809165072105416801015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59636315547051228889605413 11181809165072105416801015)
  ·
    refine ⟨16772713747608158125201523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11181809165072105416801015 16772713747608158125201523)
    ·
      refine ⟨25159070621412237187802285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16772713747608158125201523 25159070621412237187802285)
      ·
        refine ⟨9434651483029588945425857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25159070621412237187802285 9434651483029588945425857)
        ·
          refine ⟨7075988612272191709069393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9434651483029588945425857 7075988612272191709069393)
          ·
            refine ⟨5306991459204143781802045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7075988612272191709069393 5306991459204143781802045)
            ·
              refine ⟨1990121797201553918175767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5306991459204143781802045 1990121797201553918175767)
              ·
                refine ⟨2985182695802330877263651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990121797201553918175767 2985182695802330877263651)
                ·
                  refine ⟨4477774043703496315895477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2985182695802330877263651 4477774043703496315895477)
                  ·
                    refine ⟨419791316597202779615201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4477774043703496315895477 419791316597202779615201)
                    ·
                      rfl

theorem cell23_2452622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_2452622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452622 prefixEnd_2452622 := by exact prefixLift 2452622
  have htrace : WordTrace (prefixWord ++ tailWord_2452622) baseStart_2452622 baseEnd_2452622 := by
    simpa [prefixWord, tailWord_2452622, baseEnd_2452622] using wordTrace_append hprefix tailTrace_2452622
  have hstable : (prefixWord ++ tailWord_2452622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452622).length < 2 ^ (prefixWord ++ tailWord_2452622).sum := by decide
  have hdescent : baseEnd_2452622 < baseStart_2452622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452631 : List Nat := [1, 1, 3, 3, 3, 12]
def baseStart_2452631 : Nat := 118140960795 + 2452631 * 2 ^ 59
def prefixEnd_2452631 : Nat := 4983230072969 + 3 ^ 40 * 2452631 * 2
def baseEnd_2452631 : Nat := 5182627864681065035527

theorem tailTrace_2452631 : CollatzResearch.WordTrace tailWord_2452631 prefixEnd_2452631 5182627864681065035527 := by
  unfold tailWord_2452631
  simp only [CollatzResearch.WordTrace]
  refine ⟨89454801577544237871485747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59636534385029491914323831 89454801577544237871485747)
  ·
    refine ⟨134182202366316356807228621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89454801577544237871485747 134182202366316356807228621)
    ·
      refine ⟨50318325887368633802710733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134182202366316356807228621 50318325887368633802710733)
      ·
        refine ⟨18869372207763237676016525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50318325887368633802710733 18869372207763237676016525)
        ·
          refine ⟨7076014577911214128506197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18869372207763237676016525 7076014577911214128506197)
          ·
            refine ⟨5182627864681065035527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7076014577911214128506197 5182627864681065035527)
            ·
              rfl

theorem cell23_2452631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 12].length) (baseStart_2452631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452631 prefixEnd_2452631 := by exact prefixLift 2452631
  have htrace : WordTrace (prefixWord ++ tailWord_2452631) baseStart_2452631 baseEnd_2452631 := by
    simpa [prefixWord, tailWord_2452631, baseEnd_2452631] using wordTrace_append hprefix tailTrace_2452631
  have hstable : (prefixWord ++ tailWord_2452631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452631).length < 2 ^ (prefixWord ++ tailWord_2452631).sum := by decide
  have hdescent : baseEnd_2452631 < baseStart_2452631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452636 : List Nat := [2, 2, 3, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_2452636 : Nat := 118140960795 + 2452636 * 2 ^ 59
def prefixEnd_2452636 : Nat := 4983230072969 + 3 ^ 40 * 2452636 * 2
def baseEnd_2452636 : Nat := 1259381138520771284070539

theorem tailTrace_2452636 : CollatzResearch.WordTrace tailWord_2452636 prefixEnd_2452636 1259381138520771284070539 := by
  unfold tailWord_2452636
  simp only [CollatzResearch.WordTrace]
  refine ⟨44727491971263061862708881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59636655961684082483611841 44727491971263061862708881)
  ·
    refine ⟨33545618978447296397031661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44727491971263061862708881 33545618978447296397031661)
    ·
      refine ⟨12579607116917736148886873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33545618978447296397031661 12579607116917736148886873)
      ·
        refine ⟨9434705337688302111665155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12579607116917736148886873 9434705337688302111665155)
        ·
          refine ⟨14152058006532453167497733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9434705337688302111665155 14152058006532453167497733)
          ·
            refine ⟨2653510876224834968905825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14152058006532453167497733 2653510876224834968905825)
            ·
              refine ⟨1990133157168626226679369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2653510876224834968905825 1990133157168626226679369)
              ·
                refine ⟨1492599867876469670009527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1990133157168626226679369 1492599867876469670009527)
                ·
                  refine ⟨2238899801814704505014291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492599867876469670009527 2238899801814704505014291)
                  ·
                    refine ⟨3358349702722056757521437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2238899801814704505014291 3358349702722056757521437)
                    ·
                      refine ⟨1259381138520771284070539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3358349702722056757521437 1259381138520771284070539)
                      ·
                        rfl

theorem cell23_2452636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_2452636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452636 prefixEnd_2452636 := by exact prefixLift 2452636
  have htrace : WordTrace (prefixWord ++ tailWord_2452636) baseStart_2452636 baseEnd_2452636 := by
    simpa [prefixWord, tailWord_2452636, baseEnd_2452636] using wordTrace_append hprefix tailTrace_2452636
  have hstable : (prefixWord ++ tailWord_2452636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452636).length < 2 ^ (prefixWord ++ tailWord_2452636).sum := by decide
  have hdescent : baseEnd_2452636 < baseStart_2452636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452676 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_2452676 : Nat := 118140960795 + 2452676 * 2 ^ 59
def prefixEnd_2452676 : Nat := 4983230072969 + 3 ^ 40 * 2452676 * 2
def baseEnd_2452676 : Nat := 1259401677746951127570355

theorem tailTrace_2452676 : CollatzResearch.WordTrace tailWord_2452676 prefixEnd_2452676 1259401677746951127570355 := by
  unfold tailWord_2452676
  simp only [CollatzResearch.WordTrace]
  refine ⟨44728221431190605278436941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59637628574920807037915921 44728221431190605278436941)
  ·
    refine ⟨16773083036696476979413853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44728221431190605278436941 16773083036696476979413853)
    ·
      refine ⟨6289906138761178867280195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16773083036696476979413853 6289906138761178867280195)
      ·
        refine ⟨9434859208141768300920293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6289906138761178867280195 9434859208141768300920293)
        ·
          refine ⟨1769036101526581556422555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9434859208141768300920293 1769036101526581556422555)
          ·
            refine ⟨2653554152289872334633833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769036101526581556422555 2653554152289872334633833)
            ·
              refine ⟨1990165614217404250975375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2653554152289872334633833 1990165614217404250975375)
              ·
                refine ⟨2985248421326106376463063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990165614217404250975375 2985248421326106376463063)
                ·
                  refine ⟨4477872631989159564694595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2985248421326106376463063 4477872631989159564694595)
                  ·
                    refine ⟨6716808947983739347041893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4477872631989159564694595 6716808947983739347041893)
                    ·
                      refine ⟨1259401677746951127570355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6716808947983739347041893 1259401677746951127570355)
                      ·
                        rfl

theorem cell23_2452676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_2452676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452676 prefixEnd_2452676 := by exact prefixLift 2452676
  have htrace : WordTrace (prefixWord ++ tailWord_2452676) baseStart_2452676 baseEnd_2452676 := by
    simpa [prefixWord, tailWord_2452676, baseEnd_2452676] using wordTrace_append hprefix tailTrace_2452676
  have hstable : (prefixWord ++ tailWord_2452676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452676).length < 2 ^ (prefixWord ++ tailWord_2452676).sum := by decide
  have hdescent : baseEnd_2452676 < baseStart_2452676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452691 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 3, 8]
def baseStart_2452691 : Nat := 118140960795 + 2452691 * 2 ^ 59
def prefixEnd_2452691 : Nat := 4983230072969 + 3 ^ 40 * 2452691 * 2
def baseEnd_2452691 : Nat := 419803126652256189627595

theorem tailTrace_2452691 : CollatzResearch.WordTrace tailWord_2452691 prefixEnd_2452691 419803126652256189627595 := by
  unfold tailWord_2452691
  simp only [CollatzResearch.WordTrace]
  refine ⟨89456989957326868118669927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59637993304884578745779951 89456989957326868118669927)
  ·
    refine ⟨134185484935990302178004891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89456989957326868118669927 134185484935990302178004891)
    ·
      refine ⟨201278227403985453267007337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134185484935990302178004891 201278227403985453267007337)
      ·
        refine ⟨150958670552989089950255503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201278227403985453267007337 150958670552989089950255503)
        ·
          refine ⟨226438005829483634925383255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150958670552989089950255503 226438005829483634925383255)
          ·
            refine ⟨339657008744225452388074883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226438005829483634925383255 339657008744225452388074883)
            ·
              refine ⟨509485513116338178582112325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339657008744225452388074883 509485513116338178582112325)
              ·
                refine ⟨95528533709313408484146061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509485513116338178582112325 95528533709313408484146061)
                ·
                  refine ⟨35823200140992528181554773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95528533709313408484146061 35823200140992528181554773)
                  ·
                    refine ⟨419803126652256189627595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35823200140992528181554773 419803126652256189627595)
                    ·
                      rfl

theorem cell23_2452691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 8].length) (baseStart_2452691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452691 prefixEnd_2452691 := by exact prefixLift 2452691
  have htrace : WordTrace (prefixWord ++ tailWord_2452691) baseStart_2452691 baseEnd_2452691 := by
    simpa [prefixWord, tailWord_2452691, baseEnd_2452691] using wordTrace_append hprefix tailTrace_2452691
  have hstable : (prefixWord ++ tailWord_2452691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452691).length < 2 ^ (prefixWord ++ tailWord_2452691).sum := by decide
  have hdescent : baseEnd_2452691 < baseStart_2452691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452708 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_2452708 : Nat := 118140960795 + 2452708 * 2 ^ 59
def prefixEnd_2452708 : Nat := 4983230072969 + 3 ^ 40 * 2452708 * 2
def baseEnd_2452708 : Nat := 419806036375965000790069

theorem tailTrace_2452708 : CollatzResearch.WordTrace tailWord_2452708 prefixEnd_2452708 419806036375965000790069 := by
  unfold tailWord_2452708
  simp only [CollatzResearch.WordTrace]
  refine ⟨44728804999132640011019389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59638406665510186681359185 44728804999132640011019389)
  ·
    refine ⟨16773301874674740004132271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44728804999132640011019389 16773301874674740004132271)
    ·
      refine ⟨25159952812012110006198407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16773301874674740004132271 25159952812012110006198407)
      ·
        refine ⟨37739929218018165009297611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25159952812012110006198407 37739929218018165009297611)
        ·
          refine ⟨56609893827027247513946417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37739929218018165009297611 56609893827027247513946417)
          ·
            refine ⟨42457420370270435635459813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56609893827027247513946417 42457420370270435635459813)
            ·
              refine ⟨7960766319425706681648715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42457420370270435635459813 7960766319425706681648715)
              ·
                refine ⟨11941149479138560022473073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7960766319425706681648715 11941149479138560022473073)
                ·
                  refine ⟨8955862109353920016854805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11941149479138560022473073 8955862109353920016854805)
                  ·
                    refine ⟨419806036375965000790069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8955862109353920016854805 419806036375965000790069)
                    ·
                      rfl

theorem cell23_2452708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_2452708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452708 prefixEnd_2452708 := by exact prefixLift 2452708
  have htrace : WordTrace (prefixWord ++ tailWord_2452708) baseStart_2452708 baseEnd_2452708 := by
    simpa [prefixWord, tailWord_2452708, baseEnd_2452708] using wordTrace_append hprefix tailTrace_2452708
  have hstable : (prefixWord ++ tailWord_2452708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452708).length < 2 ^ (prefixWord ++ tailWord_2452708).sum := by decide
  have hdescent : baseEnd_2452708 < baseStart_2452708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452709 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 1, 3, 3]
def baseStart_2452709 : Nat := 118140960795 + 2452709 * 2 ^ 59
def prefixEnd_2452709 : Nat := 4983230072969 + 3 ^ 40 * 2452709 * 2
def baseEnd_2452709 : Nat := 1259418622608549498457703

theorem tailTrace_2452709 : CollatzResearch.WordTrace tailWord_2452709 prefixEnd_2452709 1259418622608549498457703 := by
  unfold tailWord_2452709
  simp only [CollatzResearch.WordTrace]
  refine ⟨89457646471261657192825181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59638430980841104795216787 89457646471261657192825181)
  ·
    refine ⟨33546617426723121447309443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89457646471261657192825181 33546617426723121447309443)
    ·
      refine ⟨50319926140084682170964165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33546617426723121447309443 50319926140084682170964165)
      ·
        refine ⟨9434986151265877907055781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50319926140084682170964165 9434986151265877907055781)
        ·
          refine ⟨1769059903362352107572959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9434986151265877907055781 1769059903362352107572959)
          ·
            refine ⟨2653589855043528161359439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769059903362352107572959 2653589855043528161359439)
            ·
              refine ⟨3980384782565292242039159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653589855043528161359439 3980384782565292242039159)
              ·
                refine ⟨5970577173847938363058739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980384782565292242039159 5970577173847938363058739)
                ·
                  refine ⟨8955865760771907544588109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5970577173847938363058739 8955865760771907544588109)
                  ·
                    refine ⟨3358449660289465329220541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8955865760771907544588109 3358449660289465329220541)
                    ·
                      refine ⟨1259418622608549498457703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3358449660289465329220541 1259418622608549498457703)
                      ·
                        rfl

theorem cell23_2452709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_2452709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452709 prefixEnd_2452709 := by exact prefixLift 2452709
  have htrace : WordTrace (prefixWord ++ tailWord_2452709) baseStart_2452709 baseEnd_2452709 := by
    simpa [prefixWord, tailWord_2452709, baseEnd_2452709] using wordTrace_append hprefix tailTrace_2452709
  have hstable : (prefixWord ++ tailWord_2452709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452709).length < 2 ^ (prefixWord ++ tailWord_2452709).sum := by decide
  have hdescent : baseEnd_2452709 < baseStart_2452709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452719 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 1, 3, 2]
def baseStart_2452719 : Nat := 118140960795 + 2452719 * 2 ^ 59
def prefixEnd_2452719 : Nat := 4983230072969 + 3 ^ 40 * 2452719 * 2
def baseEnd_2452719 : Nat := 1259423757415094459332657

theorem tailTrace_2452719 : CollatzResearch.WordTrace tailWord_2452719 prefixEnd_2452719 1259423757415094459332657 := by
  unfold tailWord_2452719
  simp only [CollatzResearch.WordTrace]
  refine ⟨89458011201225428900689211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59638674134150285933792807 89458011201225428900689211)
  ·
    refine ⟨134187016801838143351033817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89458011201225428900689211 134187016801838143351033817)
    ·
      refine ⟨100640262601378607513275363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134187016801838143351033817 100640262601378607513275363)
      ·
        refine ⟨150960393902067911269913045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100640262601378607513275363 150960393902067911269913045)
        ·
          refine ⟨3538134232079716670388587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 150960393902067911269913045 3538134232079716670388587)
          ·
            refine ⟨5307201348119575005582881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3538134232079716670388587 5307201348119575005582881)
            ·
              refine ⟨3980401011089681254187161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5307201348119575005582881 3980401011089681254187161)
              ·
                refine ⟨2985300758317260940640371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3980401011089681254187161 2985300758317260940640371)
                ·
                  refine ⟨4477951137475891410960557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2985300758317260940640371 4477951137475891410960557)
                  ·
                    refine ⟨1679231676553459279110209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4477951137475891410960557 1679231676553459279110209)
                    ·
                      refine ⟨1259423757415094459332657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679231676553459279110209 1259423757415094459332657)
                      ·
                        rfl

theorem cell23_2452719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 3, 2].length) (baseStart_2452719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452719 prefixEnd_2452719 := by exact prefixLift 2452719
  have htrace : WordTrace (prefixWord ++ tailWord_2452719) baseStart_2452719 baseEnd_2452719 := by
    simpa [prefixWord, tailWord_2452719, baseEnd_2452719] using wordTrace_append hprefix tailTrace_2452719
  have hstable : (prefixWord ++ tailWord_2452719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452719).length < 2 ^ (prefixWord ++ tailWord_2452719).sum := by decide
  have hdescent : baseEnd_2452719 < baseStart_2452719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452785 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 2, 5]
def baseStart_2452785 : Nat := 118140960795 + 2452785 * 2 ^ 59
def prefixEnd_2452785 : Nat := 4983230072969 + 3 ^ 40 * 2452785 * 2
def baseEnd_2452785 : Nat := 419819215712763733702451

theorem tailTrace_2452785 : CollatzResearch.WordTrace tailWord_2452785 prefixEnd_2452785 419819215712763733702451 := by
  unfold tailWord_2452785
  simp only [CollatzResearch.WordTrace]
  refine ⟨89460418418986322172591809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59640278945990881448394539 89460418418986322172591809)
  ·
    refine ⟨67095313814239741629443857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89460418418986322172591809 67095313814239741629443857)
    ·
      refine ⟨50321485360679806222082893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67095313814239741629443857 50321485360679806222082893)
      ·
        refine ⟨18870557010254927333281085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50321485360679806222082893 18870557010254927333281085)
        ·
          refine ⟨7076458878845597749980407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18870557010254927333281085 7076458878845597749980407)
          ·
            refine ⟨10614688318268396624970611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7076458878845597749980407 10614688318268396624970611)
            ·
              refine ⟨15922032477402594937455917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10614688318268396624970611 15922032477402594937455917)
              ·
                refine ⟨5970762179025973101545969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15922032477402594937455917 5970762179025973101545969)
                ·
                  refine ⟨4478071634269479826159477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5970762179025973101545969 4478071634269479826159477)
                  ·
                    refine ⟨419819215712763733702451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4478071634269479826159477 419819215712763733702451)
                    ·
                      rfl

theorem cell23_2452785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_2452785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452785 prefixEnd_2452785 := by exact prefixLift 2452785
  have htrace : WordTrace (prefixWord ++ tailWord_2452785) baseStart_2452785 baseEnd_2452785 := by
    simpa [prefixWord, tailWord_2452785, baseEnd_2452785] using wordTrace_append hprefix tailTrace_2452785
  have hstable : (prefixWord ++ tailWord_2452785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452785).length < 2 ^ (prefixWord ++ tailWord_2452785).sum := by decide
  have hdescent : baseEnd_2452785 < baseStart_2452785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452805 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 3, 6, 2]
def baseStart_2452805 : Nat := 118140960795 + 2452805 * 2 ^ 59
def prefixEnd_2452805 : Nat := 4983230072969 + 3 ^ 40 * 2452805 * 2
def baseEnd_2452805 : Nat := 1259467916751381122857261

theorem tailTrace_2452805 : CollatzResearch.WordTrace tailWord_2452805 prefixEnd_2452805 1259467916751381122857261 := by
  unfold tailWord_2452805
  simp only [CollatzResearch.WordTrace]
  refine ⟨89461147878913865588319869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59640765252609243725546579 89461147878913865588319869)
  ·
    refine ⟨33547930454592699595619951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89461147878913865588319869 33547930454592699595619951)
    ·
      refine ⟨50321895681889049393429927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33547930454592699595619951 50321895681889049393429927)
      ·
        refine ⟨75482843522833574090144891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50321895681889049393429927 75482843522833574090144891)
        ·
          refine ⟨113224265284250361135217337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75482843522833574090144891 113224265284250361135217337)
          ·
            refine ⟨84918198963187770851413003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113224265284250361135217337 84918198963187770851413003)
            ·
              refine ⟨127377298444781656277119505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84918198963187770851413003 127377298444781656277119505)
              ·
                refine ⟨95532973833586242207839629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127377298444781656277119505 95532973833586242207839629)
                ·
                  refine ⟨35824865187594840827939861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95532973833586242207839629 35824865187594840827939861)
                  ·
                    refine ⟨1679290555668508163809681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35824865187594840827939861 1679290555668508163809681)
                    ·
                      refine ⟨1259467916751381122857261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679290555668508163809681 1259467916751381122857261)
                      ·
                        rfl

theorem cell23_2452805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 6, 2].length) (baseStart_2452805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452805 prefixEnd_2452805 := by exact prefixLift 2452805
  have htrace : WordTrace (prefixWord ++ tailWord_2452805) baseStart_2452805 baseEnd_2452805 := by
    simpa [prefixWord, tailWord_2452805, baseEnd_2452805] using wordTrace_append hprefix tailTrace_2452805
  have hstable : (prefixWord ++ tailWord_2452805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452805).length < 2 ^ (prefixWord ++ tailWord_2452805).sum := by decide
  have hdescent : baseEnd_2452805 < baseStart_2452805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452808 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_2452808 : Nat := 118140960795 + 2452808 * 2 ^ 59
def prefixEnd_2452808 : Nat := 4983230072969 + 3 ^ 40 * 2452808 * 2
def baseEnd_2452808 : Nat := 1259469457193344611119747

theorem tailTrace_2452808 : CollatzResearch.WordTrace tailWord_2452808 prefixEnd_2452808 1259469457193344611119747 := by
  unfold tailWord_2452808
  simp only [CollatzResearch.WordTrace]
  refine ⟨44730628648951498550339539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59640838198601998067119385 44730628648951498550339539)
  ·
    refine ⟨67095942973427247825509309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44730628648951498550339539 67095942973427247825509309)
    ·
      refine ⟨25160978615035217934565991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67095942973427247825509309 25160978615035217934565991)
      ·
        refine ⟨37741467922552826901848987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25160978615035217934565991 37741467922552826901848987)
        ·
          refine ⟨56612201883829240352773481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37741467922552826901848987 56612201883829240352773481)
          ·
            refine ⟨42459151412871930264580111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56612201883829240352773481 42459151412871930264580111)
            ·
              refine ⟨63688727119307895396870167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42459151412871930264580111 63688727119307895396870167)
              ·
                refine ⟨95533090678961843095305251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63688727119307895396870167 95533090678961843095305251)
                ·
                  refine ⟨143299636018442764642957877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95533090678961843095305251 143299636018442764642957877)
                  ·
                    refine ⟨13434340876729009185277301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 143299636018442764642957877 13434340876729009185277301)
                    ·
                      refine ⟨1259469457193344611119747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13434340876729009185277301 1259469457193344611119747)
                      ·
                        rfl

theorem cell23_2452808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_2452808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452808 prefixEnd_2452808 := by exact prefixLift 2452808
  have htrace : WordTrace (prefixWord ++ tailWord_2452808) baseStart_2452808 baseEnd_2452808 := by
    simpa [prefixWord, tailWord_2452808, baseEnd_2452808] using wordTrace_append hprefix tailTrace_2452808
  have hstable : (prefixWord ++ tailWord_2452808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452808).length < 2 ^ (prefixWord ++ tailWord_2452808).sum := by decide
  have hdescent : baseEnd_2452808 < baseStart_2452808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452825 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 4, 2, 3]
def baseStart_2452825 : Nat := 118140960795 + 2452825 * 2 ^ 59
def prefixEnd_2452825 : Nat := 4983230072969 + 3 ^ 40 * 2452825 * 2
def baseEnd_2452825 : Nat := 1259478186364471044607169

theorem tailTrace_2452825 : CollatzResearch.WordTrace tailWord_2452825 prefixEnd_2452825 1259478186364471044607169 := by
  unfold tailWord_2452825
  simp only [CollatzResearch.WordTrace]
  refine ⟨89461877338841409004047929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59641251559227606002698619 89461877338841409004047929)
  ·
    refine ⟨67096408004131056753035947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89461877338841409004047929 67096408004131056753035947)
    ·
      refine ⟨100644612006196585129553921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67096408004131056753035947 100644612006196585129553921)
      ·
        refine ⟨75483459004647438847165441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100644612006196585129553921 75483459004647438847165441)
        ·
          refine ⟨56612594253485579135374081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75483459004647438847165441 56612594253485579135374081)
          ·
            refine ⟨42459445690114184351530561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56612594253485579135374081 42459445690114184351530561)
            ·
              refine ⟨31844584267585638263647921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42459445690114184351530561 31844584267585638263647921)
              ·
                refine ⟨23883438200689228697735941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31844584267585638263647921 23883438200689228697735941)
                ·
                  refine ⟨4478144662629230380825489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23883438200689228697735941 4478144662629230380825489)
                  ·
                    refine ⟨3358608496971922785619117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4478144662629230380825489 3358608496971922785619117)
                    ·
                      refine ⟨1259478186364471044607169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3358608496971922785619117 1259478186364471044607169)
                      ·
                        rfl

theorem cell23_2452825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_2452825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452825 prefixEnd_2452825 := by exact prefixLift 2452825
  have htrace : WordTrace (prefixWord ++ tailWord_2452825) baseStart_2452825 baseEnd_2452825 := by
    simpa [prefixWord, tailWord_2452825, baseEnd_2452825] using wordTrace_append hprefix tailTrace_2452825
  have hstable : (prefixWord ++ tailWord_2452825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452825).length < 2 ^ (prefixWord ++ tailWord_2452825).sum := by decide
  have hdescent : baseEnd_2452825 < baseStart_2452825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452832 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 3, 4]
def baseStart_2452832 : Nat := 118140960795 + 2452832 * 2 ^ 59
def prefixEnd_2452832 : Nat := 4983230072969 + 3 ^ 40 * 2452832 * 2
def baseEnd_2452832 : Nat := 419827260243017505739879

theorem tailTrace_2452832 : CollatzResearch.WordTrace tailWord_2452832 prefixEnd_2452832 419827260243017505739879 := by
  unfold tailWord_2452832
  simp only [CollatzResearch.WordTrace]
  refine ⟨44731066324908024599776375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59641421766544032799701833 44731066324908024599776375)
  ·
    refine ⟨67096599487362036899664563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44731066324908024599776375 67096599487362036899664563)
    ·
      refine ⟨100644899231043055349496845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67096599487362036899664563 100644899231043055349496845)
      ·
        refine ⟨37741837211641145756061317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100644899231043055349496845 37741837211641145756061317)
        ·
          refine ⟨7076594477182714829261497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37741837211641145756061317 7076594477182714829261497)
          ·
            refine ⟨5307445857887036121946123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7076594477182714829261497 5307445857887036121946123)
            ·
              refine ⟨7961168786830554182919185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5307445857887036121946123 7961168786830554182919185)
              ·
                refine ⟨5970876590122915637189389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7961168786830554182919185 5970876590122915637189389)
                ·
                  refine ⟨2239078721296093363946021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5970876590122915637189389 2239078721296093363946021)
                  ·
                    refine ⟨419827260243017505739879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2239078721296093363946021 419827260243017505739879)
                    ·
                      rfl

theorem cell23_2452832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3, 4].length) (baseStart_2452832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452832 prefixEnd_2452832 := by exact prefixLift 2452832
  have htrace : WordTrace (prefixWord ++ tailWord_2452832) baseStart_2452832 baseEnd_2452832 := by
    simpa [prefixWord, tailWord_2452832, baseEnd_2452832] using wordTrace_append hprefix tailTrace_2452832
  have hstable : (prefixWord ++ tailWord_2452832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452832).length < 2 ^ (prefixWord ++ tailWord_2452832).sum := by decide
  have hdescent : baseEnd_2452832 < baseStart_2452832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452839 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_2452839 : Nat := 118140960795 + 2452839 * 2 ^ 59
def prefixEnd_2452839 : Nat := 4983230072969 + 3 ^ 40 * 2452839 * 2
def baseEnd_2452839 : Nat := 1259485375093633989832105

theorem tailTrace_2452839 : CollatzResearch.WordTrace tailWord_2452839 prefixEnd_2452839 1259485375093633989832105 := by
  unfold tailWord_2452839
  simp only [CollatzResearch.WordTrace]
  refine ⟨89462387960790689395057571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59641591973860459596705047 89462387960790689395057571)
  ·
    refine ⟨134193581941186034092586357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89462387960790689395057571 134193581941186034092586357)
    ·
      refine ⟨12580648306986190696179971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134193581941186034092586357 12580648306986190696179971)
      ·
        refine ⟨18870972460479286044269957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12580648306986190696179971 18870972460479286044269957)
        ·
          refine ⟨3538307336339866133300617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18870972460479286044269957 3538307336339866133300617)
          ·
            refine ⟨2653730502254899599975463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3538307336339866133300617 2653730502254899599975463)
            ·
              refine ⟨3980595753382349399963195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653730502254899599975463 3980595753382349399963195)
              ·
                refine ⟨5970893630073524099944793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980595753382349399963195 5970893630073524099944793)
                ·
                  refine ⟨4478170222555143074958595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5970893630073524099944793 4478170222555143074958595)
                  ·
                    refine ⟨6717255333832714612437893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4478170222555143074958595 6717255333832714612437893)
                    ·
                      refine ⟨1259485375093633989832105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6717255333832714612437893 1259485375093633989832105)
                      ·
                        rfl

theorem cell23_2452839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_2452839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452839 prefixEnd_2452839 := by exact prefixLift 2452839
  have htrace : WordTrace (prefixWord ++ tailWord_2452839) baseStart_2452839 baseEnd_2452839 := by
    simpa [prefixWord, tailWord_2452839, baseEnd_2452839] using wordTrace_append hprefix tailTrace_2452839
  have hstable : (prefixWord ++ tailWord_2452839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452839).length < 2 ^ (prefixWord ++ tailWord_2452839).sum := by decide
  have hdescent : baseEnd_2452839 < baseStart_2452839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452866 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2452866 : Nat := 118140960795 + 2452866 * 2 ^ 59
def prefixEnd_2452866 : Nat := 4983230072969 + 3 ^ 40 * 2452866 * 2
def baseEnd_2452866 : Nat := 419833079690435128064827

theorem tailTrace_2452866 : CollatzResearch.WordTrace tailWord_2452866 prefixEnd_2452866 419833079690435128064827 := by
  unfold tailWord_2452866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22365843182923218251572613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59642248487795248670860301 22365843182923218251572613)
  ·
    refine ⟨4193595596798103422169865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22365843182923218251572613 4193595596798103422169865)
    ·
      refine ⟨3145196697598577566627399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4193595596798103422169865 3145196697598577566627399)
      ·
        refine ⟨4717795046397866349941099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3145196697598577566627399 4717795046397866349941099)
        ·
          refine ⟨7076692569596799524911649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4717795046397866349941099 7076692569596799524911649)
          ·
            refine ⟨5307519427197599643683737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7076692569596799524911649 5307519427197599643683737)
            ·
              refine ⟨3980639570398199732762803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5307519427197599643683737 3980639570398199732762803)
              ·
                refine ⟨5970959355597299599144205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980639570398199732762803 5970959355597299599144205)
                ·
                  refine ⟨2239109758348987349679077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5970959355597299599144205 2239109758348987349679077)
                  ·
                    refine ⟨419833079690435128064827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2239109758348987349679077 419833079690435128064827)
                    ·
                      rfl

theorem cell23_2452866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2452866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452866 prefixEnd_2452866 := by exact prefixLift 2452866
  have htrace : WordTrace (prefixWord ++ tailWord_2452866) baseStart_2452866 baseEnd_2452866 := by
    simpa [prefixWord, tailWord_2452866, baseEnd_2452866] using wordTrace_append hprefix tailTrace_2452866
  have hstable : (prefixWord ++ tailWord_2452866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452866).length < 2 ^ (prefixWord ++ tailWord_2452866).sum := by decide
  have hdescent : baseEnd_2452866 < baseStart_2452866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452909 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2452909 : Nat := 118140960795 + 2452909 * 2 ^ 59
def prefixEnd_2452909 : Nat := 4983230072969 + 3 ^ 40 * 2452909 * 2
def baseEnd_2452909 : Nat := 419840439579816238652261

theorem tailTrace_2452909 : CollatzResearch.WordTrace tailWord_2452909 prefixEnd_2452909 419840439579816238652261 := by
  unfold tailWord_2452909
  simp only [CollatzResearch.WordTrace]
  refine ⟨89464941070537091350105781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59643294047024727566737187 89464941070537091350105781)
  ·
    refine ⟨8387338225362852314072417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89464941070537091350105781 8387338225362852314072417)
    ·
      refine ⟨6290503669022139235554313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8387338225362852314072417 6290503669022139235554313)
      ·
        refine ⟨4717877751766604426665735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6290503669022139235554313 4717877751766604426665735)
        ·
          refine ⟨7076816627649906639998603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4717877751766604426665735 7076816627649906639998603)
          ·
            refine ⟨10615224941474859959997905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7076816627649906639998603 10615224941474859959997905)
            ·
              refine ⟨7961418706106144969998429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10615224941474859959997905 7961418706106144969998429)
              ·
                refine ⟨2985532014789804363749411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7961418706106144969998429 2985532014789804363749411)
                ·
                  refine ⟨4478298022184706545624117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2985532014789804363749411 4478298022184706545624117)
                  ·
                    refine ⟨419840439579816238652261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4478298022184706545624117 419840439579816238652261)
                    ·
                      rfl

theorem cell23_2452909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2452909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452909 prefixEnd_2452909 := by exact prefixLift 2452909
  have htrace : WordTrace (prefixWord ++ tailWord_2452909) baseStart_2452909 baseEnd_2452909 := by
    simpa [prefixWord, tailWord_2452909, baseEnd_2452909] using wordTrace_append hprefix tailTrace_2452909
  have hstable : (prefixWord ++ tailWord_2452909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452909).length < 2 ^ (prefixWord ++ tailWord_2452909).sum := by decide
  have hdescent : baseEnd_2452909 < baseStart_2452909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452925 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2452925 : Nat := 118140960795 + 2452925 * 2 ^ 59
def prefixEnd_2452925 : Nat := 4983230072969 + 3 ^ 40 * 2452925 * 2
def baseEnd_2452925 : Nat := 1259529534429920653356709

theorem tailTrace_2452925 : CollatzResearch.WordTrace tailWord_2452925 prefixEnd_2452925 1259529534429920653356709 := by
  unfold tailWord_2452925
  simp only [CollatzResearch.WordTrace]
  refine ⟨89465524638479126082688229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59643683092319417388458819 89465524638479126082688229)
  ·
    refine ⟨16774785869714836140504043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89465524638479126082688229 16774785869714836140504043)
    ·
      refine ⟨25162178804572254210756065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16774785869714836140504043 25162178804572254210756065)
      ·
        refine ⟨18871634103429190658067049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25162178804572254210756065 18871634103429190658067049)
        ·
          refine ⟨14153725577571892993550287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18871634103429190658067049 14153725577571892993550287)
          ·
            refine ⟨21230588366357839490325431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14153725577571892993550287 21230588366357839490325431)
            ·
              refine ⟨31845882549536759235488147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21230588366357839490325431 31845882549536759235488147)
              ·
                refine ⟨47768823824305138853232221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31845882549536759235488147 47768823824305138853232221)
                ·
                  refine ⟨17913308934114427069962083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47768823824305138853232221 17913308934114427069962083)
                  ·
                    refine ⟨26869963401171640604943125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17913308934114427069962083 26869963401171640604943125)
                    ·
                      refine ⟨1259529534429920653356709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26869963401171640604943125 1259529534429920653356709)
                      ·
                        rfl

theorem cell23_2452925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2452925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452925 prefixEnd_2452925 := by exact prefixLift 2452925
  have htrace : WordTrace (prefixWord ++ tailWord_2452925) baseStart_2452925 baseEnd_2452925 := by
    simpa [prefixWord, tailWord_2452925, baseEnd_2452925] using wordTrace_append hprefix tailTrace_2452925
  have hstable : (prefixWord ++ tailWord_2452925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452925).length < 2 ^ (prefixWord ++ tailWord_2452925).sum := by decide
  have hdescent : baseEnd_2452925 < baseStart_2452925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452935 : List Nat := [1, 1, 4, 1, 1, 3, 4, 8]
def baseStart_2452935 : Nat := 118140960795 + 2452935 * 2 ^ 59
def prefixEnd_2452935 : Nat := 4983230072969 + 3 ^ 40 * 2452935 * 2
def baseEnd_2452935 : Nat := 46649432193943170897469

theorem tailTrace_2452935 : CollatzResearch.WordTrace tailWord_2452935 prefixEnd_2452935 46649432193943170897469 := by
  unfold tailWord_2452935
  simp only [CollatzResearch.WordTrace]
  refine ⟨89465889368442897790552259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59643926245628598527034839 89465889368442897790552259)
  ·
    refine ⟨134198834052664346685828389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89465889368442897790552259 134198834052664346685828389)
    ·
      refine ⟨25162281384874565003592823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134198834052664346685828389 25162281384874565003592823)
      ·
        refine ⟨37743422077311847505389235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25162281384874565003592823 37743422077311847505389235)
        ·
          refine ⟨56615133115967771258083853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37743422077311847505389235 56615133115967771258083853)
          ·
            refine ⟨21230674918487914221781445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56615133115967771258083853 21230674918487914221781445)
            ·
              refine ⟨3980751547216483916584021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21230674918487914221781445 3980751547216483916584021)
              ·
                refine ⟨46649432193943170897469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3980751547216483916584021 46649432193943170897469)
                ·
                  rfl

theorem cell23_2452935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 8].length) (baseStart_2452935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452935 prefixEnd_2452935 := by exact prefixLift 2452935
  have htrace : WordTrace (prefixWord ++ tailWord_2452935) baseStart_2452935 baseEnd_2452935 := by
    simpa [prefixWord, tailWord_2452935, baseEnd_2452935] using wordTrace_append hprefix tailTrace_2452935
  have hstable : (prefixWord ++ tailWord_2452935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452935).length < 2 ^ (prefixWord ++ tailWord_2452935).sum := by decide
  have hdescent : baseEnd_2452935 < baseStart_2452935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452939 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 2, 4]
def baseStart_2452939 : Nat := 118140960795 + 2452939 * 2 ^ 59
def prefixEnd_2452939 : Nat := 4983230072969 + 3 ^ 40 * 2452939 * 2
def baseEnd_2452939 : Nat := 419845574386361199527215

theorem tailTrace_2452939 : CollatzResearch.WordTrace tailWord_2452939 prefixEnd_2452939 419845574386361199527215 := by
  unfold tailWord_2452939
  simp only [CollatzResearch.WordTrace]
  refine ⟨89466035260428406473697871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59644023506952270982465247 89466035260428406473697871)
  ·
    refine ⟨134199052890642609710546807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89466035260428406473697871 134199052890642609710546807)
    ·
      refine ⟨201298579335963914565820211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134199052890642609710546807 201298579335963914565820211)
      ·
        refine ⟨301947869003945871848730317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201298579335963914565820211 301947869003945871848730317)
        ·
          refine ⟨113230450876479701943273869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301947869003945871848730317 113230450876479701943273869)
          ·
            refine ⟨42461419078679888228727701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113230450876479701943273869 42461419078679888228727701)
            ·
              refine ⟨1990379019313119760721611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42461419078679888228727701 1990379019313119760721611)
              ·
                refine ⟨2985568528969679641082417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990379019313119760721611 2985568528969679641082417)
                ·
                  refine ⟨2239176396727259730811813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2985568528969679641082417 2239176396727259730811813)
                  ·
                    refine ⟨419845574386361199527215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2239176396727259730811813 419845574386361199527215)
                    ·
                      rfl

theorem cell23_2452939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 2, 4].length) (baseStart_2452939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452939 prefixEnd_2452939 := by exact prefixLift 2452939
  have htrace : WordTrace (prefixWord ++ tailWord_2452939) baseStart_2452939 baseEnd_2452939 := by
    simpa [prefixWord, tailWord_2452939, baseEnd_2452939] using wordTrace_append hprefix tailTrace_2452939
  have hstable : (prefixWord ++ tailWord_2452939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452939).length < 2 ^ (prefixWord ++ tailWord_2452939).sum := by decide
  have hdescent : baseEnd_2452939 < baseStart_2452939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452975 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_2452975 : Nat := 118140960795 + 2452975 * 2 ^ 59
def prefixEnd_2452975 : Nat := 4983230072969 + 3 ^ 40 * 2452975 * 2
def baseEnd_2452975 : Nat := 1259555208462645457731479

theorem tailTrace_2452975 : CollatzResearch.WordTrace tailWord_2452975 prefixEnd_2452975 1259555208462645457731479 := by
  unfold tailWord_2452975
  simp only [CollatzResearch.WordTrace]
  refine ⟨89467348288297984622008379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59644898858865323081338919 89467348288297984622008379)
  ·
    refine ⟨134201022432446976933012569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89467348288297984622008379 134201022432446976933012569)
    ·
      refine ⟨100650766824335232699759427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134201022432446976933012569 100650766824335232699759427)
      ·
        refine ⟨150976150236502849049639141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100650766824335232699759427 150976150236502849049639141)
        ·
          refine ⟨28308028169344284196807339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150976150236502849049639141 28308028169344284196807339)
          ·
            refine ⟨42462042254016426295211009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28308028169344284196807339 42462042254016426295211009)
            ·
              refine ⟨31846531690512319721408257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42462042254016426295211009 31846531690512319721408257)
              ·
                refine ⟨23884898767884239791056193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31846531690512319721408257 23884898767884239791056193)
                ·
                  refine ⟨17913674075913179843292145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23884898767884239791056193 17913674075913179843292145)
                  ·
                    refine ⟨13435255556934884882469109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17913674075913179843292145 13435255556934884882469109)
                    ·
                      refine ⟨1259555208462645457731479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13435255556934884882469109 1259555208462645457731479)
                      ·
                        rfl

theorem cell23_2452975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_2452975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452975 prefixEnd_2452975 := by exact prefixLift 2452975
  have htrace : WordTrace (prefixWord ++ tailWord_2452975) baseStart_2452975 baseEnd_2452975 := by
    simpa [prefixWord, tailWord_2452975, baseEnd_2452975] using wordTrace_append hprefix tailTrace_2452975
  have hstable : (prefixWord ++ tailWord_2452975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452975).length < 2 ^ (prefixWord ++ tailWord_2452975).sum := by decide
  have hdescent : baseEnd_2452975 < baseStart_2452975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452982 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_2452982 : Nat := 118140960795 + 2452982 * 2 ^ 59
def prefixEnd_2452982 : Nat := 4983230072969 + 3 ^ 40 * 2452982 * 2
def baseEnd_2452982 : Nat := 419852934275742310114649

theorem tailTrace_2452982 : CollatzResearch.WordTrace tailWord_2452982 prefixEnd_2452982 419852934275742310114649 := by
  unfold tailWord_2452982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5591725224954539051094575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59645069066181749878342133 5591725224954539051094575)
  ·
    refine ⟨8387587837431808576641863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5591725224954539051094575 8387587837431808576641863)
    ·
      refine ⟨12581381756147712864962795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8387587837431808576641863 12581381756147712864962795)
      ·
        refine ⟨18872072634221569297444193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12581381756147712864962795 18872072634221569297444193)
        ·
          refine ⟨14154054475666176973083145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18872072634221569297444193 14154054475666176973083145)
          ·
            refine ⟨10615540856749632729812359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14154054475666176973083145 10615540856749632729812359)
            ·
              refine ⟨15923311285124449094718539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10615540856749632729812359 15923311285124449094718539)
              ·
                refine ⟨23884966927686673642077809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15923311285124449094718539 23884966927686673642077809)
                ·
                  refine ⟨17913725195765005231558357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23884966927686673642077809 17913725195765005231558357)
                  ·
                    refine ⟨419852934275742310114649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17913725195765005231558357 419852934275742310114649)
                    ·
                      rfl

theorem cell23_2452982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2452982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452982 prefixEnd_2452982 := by exact prefixLift 2452982
  have htrace : WordTrace (prefixWord ++ tailWord_2452982) baseStart_2452982 baseEnd_2452982 := by
    simpa [prefixWord, tailWord_2452982, baseEnd_2452982] using wordTrace_append hprefix tailTrace_2452982
  have hstable : (prefixWord ++ tailWord_2452982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452982).length < 2 ^ (prefixWord ++ tailWord_2452982).sum := by decide
  have hdescent : baseEnd_2452982 < baseStart_2452982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452989 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 3, 3, 2]
def baseStart_2452989 : Nat := 118140960795 + 2452989 * 2 ^ 59
def prefixEnd_2452989 : Nat := 4983230072969 + 3 ^ 40 * 2452989 * 2
def baseEnd_2452989 : Nat := 1259562397191808402956415

theorem tailTrace_2452989 : CollatzResearch.WordTrace tailWord_2452989 prefixEnd_2452989 1259562397191808402956415 := by
  unfold tailWord_2452989
  simp only [CollatzResearch.WordTrace]
  refine ⟨89467858910247265013018021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59645239273498176675345347 89467858910247265013018021)
  ·
    refine ⟨16775223545671362189940879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89467858910247265013018021 16775223545671362189940879)
    ·
      refine ⟨25162835318507043284911319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16775223545671362189940879 25162835318507043284911319)
      ·
        refine ⟨37744252977760564927366979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25162835318507043284911319 37744252977760564927366979)
        ·
          refine ⟨56616379466640847391050469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37744252977760564927366979 56616379466640847391050469)
          ·
            refine ⟨10615571149995158885821963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56616379466640847391050469 10615571149995158885821963)
            ·
              refine ⟨15923356724992738328732945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10615571149995158885821963 15923356724992738328732945)
              ·
                refine ⟨11942517543744553746549709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15923356724992738328732945 11942517543744553746549709)
                ·
                  refine ⟨4478444078904207654956141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11942517543744553746549709 4478444078904207654956141)
                  ·
                    refine ⟨1679416529589077870608553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4478444078904207654956141 1679416529589077870608553)
                    ·
                      refine ⟨1259562397191808402956415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679416529589077870608553 1259562397191808402956415)
                      ·
                        rfl

theorem cell23_2452989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_2452989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452989 prefixEnd_2452989 := by exact prefixLift 2452989
  have htrace : WordTrace (prefixWord ++ tailWord_2452989) baseStart_2452989 baseEnd_2452989 := by
    simpa [prefixWord, tailWord_2452989, baseEnd_2452989] using wordTrace_append hprefix tailTrace_2452989
  have hstable : (prefixWord ++ tailWord_2452989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452989).length < 2 ^ (prefixWord ++ tailWord_2452989).sum := by decide
  have hdescent : baseEnd_2452989 < baseStart_2452989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452996 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2452996 : Nat := 118140960795 + 2452996 * 2 ^ 59
def prefixEnd_2452996 : Nat := 4983230072969 + 3 ^ 40 * 2452996 * 2
def baseEnd_2452996 : Nat := 1259565991556389875568883

theorem tailTrace_2452996 : CollatzResearch.WordTrace tailWord_2452996 prefixEnd_2452996 1259565991556389875568883 := by
  unfold tailWord_2452996
  simp only [CollatzResearch.WordTrace]
  refine ⟨44734057110610952604261421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59645409480814603472348561 44734057110610952604261421)
  ·
    refine ⟨16775271416479107226598033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44734057110610952604261421 16775271416479107226598033)
    ·
      refine ⟨12581453562359330419948525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16775271416479107226598033 12581453562359330419948525)
      ·
        refine ⟨4718045085884748907480697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12581453562359330419948525 4718045085884748907480697)
        ·
          refine ⟨3538533814413561680610523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4718045085884748907480697 3538533814413561680610523)
          ·
            refine ⟨5307800721620342520915785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3538533814413561680610523 5307800721620342520915785)
            ·
              refine ⟨3980850541215256890686839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5307800721620342520915785 3980850541215256890686839)
              ·
                refine ⟨5971275811822885336030259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980850541215256890686839 5971275811822885336030259)
                ·
                  refine ⟨8956913717734328004045389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5971275811822885336030259 8956913717734328004045389)
                  ·
                    refine ⟨3358842644150373001517021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8956913717734328004045389 3358842644150373001517021)
                    ·
                      refine ⟨1259565991556389875568883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3358842644150373001517021 1259565991556389875568883)
                      ·
                        rfl

theorem cell23_2452996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2452996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452996 prefixEnd_2452996 := by exact prefixLift 2452996
  have htrace : WordTrace (prefixWord ++ tailWord_2452996) baseStart_2452996 baseEnd_2452996 := by
    simpa [prefixWord, tailWord_2452996, baseEnd_2452996] using wordTrace_append hprefix tailTrace_2452996
  have hstable : (prefixWord ++ tailWord_2452996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452996).length < 2 ^ (prefixWord ++ tailWord_2452996).sum := by decide
  have hdescent : baseEnd_2452996 < baseStart_2452996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453053 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 1, 4, 2]
def baseStart_2453053 : Nat := 118140960795 + 2453053 * 2 ^ 59
def prefixEnd_2453053 : Nat := 4983230072969 + 3 ^ 40 * 2453053 * 2
def baseEnd_2453053 : Nat := 1259595259953696152556121

theorem tailTrace_2453053 : CollatzResearch.WordTrace tailWord_2453053 prefixEnd_2453053 1259595259953696152556121 := by
  unfold tailWord_2453053
  simp only [CollatzResearch.WordTrace]
  refine ⟨89470193182015403943347813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59646795454676935962231875 89470193182015403943347813)
  ·
    refine ⟨16775661221627888239377715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89470193182015403943347813 16775661221627888239377715)
    ·
      refine ⟨25163491832441832359066573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16775661221627888239377715 25163491832441832359066573)
      ·
        refine ⟨9436309437165687134649965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25163491832441832359066573 9436309437165687134649965)
        ·
          refine ⟨3538616038937132675493737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9436309437165687134649965 3538616038937132675493737)
          ·
            refine ⟨2653962029202849506620303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3538616038937132675493737 2653962029202849506620303)
            ·
              refine ⟨3980943043804274259930455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653962029202849506620303 3980943043804274259930455)
              ·
                refine ⟨5971414565706411389895683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980943043804274259930455 5971414565706411389895683)
                ·
                  refine ⟨8957121848559617084843525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5971414565706411389895683 8957121848559617084843525)
                  ·
                    refine ⟨1679460346604928203408161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8957121848559617084843525 1679460346604928203408161)
                    ·
                      refine ⟨1259595259953696152556121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679460346604928203408161 1259595259953696152556121)
                      ·
                        rfl

theorem cell23_2453053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_2453053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453053 prefixEnd_2453053 := by exact prefixLift 2453053
  have htrace : WordTrace (prefixWord ++ tailWord_2453053) baseStart_2453053 baseEnd_2453053 := by
    simpa [prefixWord, tailWord_2453053, baseEnd_2453053] using wordTrace_append hprefix tailTrace_2453053
  have hstable : (prefixWord ++ tailWord_2453053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453053).length < 2 ^ (prefixWord ++ tailWord_2453053).sum := by decide
  have hdescent : baseEnd_2453053 < baseStart_2453053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453072 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 2, 5]
def baseStart_2453072 : Nat := 118140960795 + 2453072 * 2 ^ 59
def prefixEnd_2453072 : Nat := 4983230072969 + 3 ^ 40 * 2453072 * 2
def baseEnd_2453072 : Nat := 419868338695377192739511

theorem tailTrace_2453072 : CollatzResearch.WordTrace tailWord_2453072 prefixEnd_2453072 419868338695377192739511 := by
  unfold tailWord_2453072
  simp only [CollatzResearch.WordTrace]
  refine ⟨44735443084473285094144735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59647257445964380125526313 44735443084473285094144735)
  ·
    refine ⟨67103164626709927641217103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44735443084473285094144735 67103164626709927641217103)
    ·
      refine ⟨100654746940064891461825655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67103164626709927641217103 100654746940064891461825655)
      ·
        refine ⟨150982120410097337192738483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100654746940064891461825655 150982120410097337192738483)
        ·
          refine ⟨226473180615146005789107725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150982120410097337192738483 226473180615146005789107725)
          ·
            refine ⟨84927442730679752170915397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226473180615146005789107725 84927442730679752170915397)
            ·
              refine ⟨15923895512002453532046637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84927442730679752170915397 15923895512002453532046637)
              ·
                refine ⟨5971460817000920074517489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15923895512002453532046637 5971460817000920074517489)
                ·
                  refine ⟨4478595612750690055888117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5971460817000920074517489 4478595612750690055888117)
                  ·
                    refine ⟨419868338695377192739511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4478595612750690055888117 419868338695377192739511)
                    ·
                      rfl

theorem cell23_2453072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_2453072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453072 prefixEnd_2453072 := by exact prefixLift 2453072
  have htrace : WordTrace (prefixWord ++ tailWord_2453072) baseStart_2453072 baseEnd_2453072 := by
    simpa [prefixWord, tailWord_2453072, baseEnd_2453072] using wordTrace_append hprefix tailTrace_2453072
  have hstable : (prefixWord ++ tailWord_2453072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453072).length < 2 ^ (prefixWord ++ tailWord_2453072).sum := by decide
  have hdescent : baseEnd_2453072 < baseStart_2453072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453129 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 2, 2, 3]
def baseStart_2453129 : Nat := 118140960795 + 2453129 * 2 ^ 59
def prefixEnd_2453129 : Nat := 4983230072969 + 3 ^ 40 * 2453129 * 2
def baseEnd_2453129 : Nat := 1259634284483437855205771

theorem tailTrace_2453129 : CollatzResearch.WordTrace tailWord_2453129 prefixEnd_2453129 1259634284483437855205771 := by
  unfold tailWord_2453129
  simp only [CollatzResearch.WordTrace]
  refine ⟨89472965129740068923114441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59648643419826712615409627 89472965129740068923114441)
  ·
    refine ⟨67104723847305051692335831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89472965129740068923114441 67104723847305051692335831)
    ·
      refine ⟨100657085770957577538503747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67104723847305051692335831 100657085770957577538503747)
      ·
        refine ⟨150985628656436366307755621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100657085770957577538503747 150985628656436366307755621)
        ·
          refine ⟨28309805373081818682704179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150985628656436366307755621 28309805373081818682704179)
          ·
            refine ⟨42464708059622728024056269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28309805373081818682704179 42464708059622728024056269)
            ·
              refine ⟨15924265522358523009021101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42464708059622728024056269 15924265522358523009021101)
              ·
                refine ⟨5971599570884446128382913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15924265522358523009021101 5971599570884446128382913)
                ·
                  refine ⟨4478699678163334596287185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5971599570884446128382913 4478699678163334596287185)
                  ·
                    refine ⟨3359024758622500947215389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4478699678163334596287185 3359024758622500947215389)
                    ·
                      refine ⟨1259634284483437855205771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3359024758622500947215389 1259634284483437855205771)
                      ·
                        rfl

theorem cell23_2453129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2, 3].length) (baseStart_2453129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453129 prefixEnd_2453129 := by exact prefixLift 2453129
  have htrace : WordTrace (prefixWord ++ tailWord_2453129) baseStart_2453129 baseEnd_2453129 := by
    simpa [prefixWord, tailWord_2453129, baseEnd_2453129] using wordTrace_append hprefix tailTrace_2453129
  have hstable : (prefixWord ++ tailWord_2453129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453129).length < 2 ^ (prefixWord ++ tailWord_2453129).sum := by decide
  have hdescent : baseEnd_2453129 < baseStart_2453129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453153 : List Nat := [1, 2, 3, 3, 2, 2, 1, 4, 1, 4]
def baseStart_2453153 : Nat := 118140960795 + 2453153 * 2 ^ 59
def prefixEnd_2453153 : Nat := 4983230072969 + 3 ^ 40 * 2453153 * 2
def baseEnd_2453153 : Nat := 419882202673048587101887

theorem tailTrace_2453153 : CollatzResearch.WordTrace tailWord_2453153 prefixEnd_2453153 419882202673048587101887 := by
  unfold tailWord_2453153
  simp only [CollatzResearch.WordTrace]
  refine ⟨89473840481653121021988113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59649226987768747347992075 89473840481653121021988113)
  ·
    refine ⟨67105380361239840766491085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89473840481653121021988113 67105380361239840766491085)
    ·
      refine ⟨25164517635464940287434157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67105380361239840766491085 25164517635464940287434157)
      ·
        refine ⟨9436694113299352607787809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25164517635464940287434157 9436694113299352607787809)
        ·
          refine ⟨7077520584974514455840857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9436694113299352607787809 7077520584974514455840857)
          ·
            refine ⟨5308140438730885841880643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7077520584974514455840857 5308140438730885841880643)
            ·
              refine ⟨7962210658096328762820965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5308140438730885841880643 7962210658096328762820965)
              ·
                refine ⟨1492914498393061643028931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7962210658096328762820965 1492914498393061643028931)
                ·
                  refine ⟨2239371747589592464543397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492914498393061643028931 2239371747589592464543397)
                  ·
                    refine ⟨419882202673048587101887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2239371747589592464543397 419882202673048587101887)
                    ·
                      rfl

theorem cell23_2453153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_2453153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453153 prefixEnd_2453153 := by exact prefixLift 2453153
  have htrace : WordTrace (prefixWord ++ tailWord_2453153) baseStart_2453153 baseEnd_2453153 := by
    simpa [prefixWord, tailWord_2453153, baseEnd_2453153] using wordTrace_append hprefix tailTrace_2453153
  have hstable : (prefixWord ++ tailWord_2453153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453153).length < 2 ^ (prefixWord ++ tailWord_2453153).sum := by decide
  have hdescent : baseEnd_2453153 < baseStart_2453153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453199 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 1, 8, 2]
def baseStart_2453199 : Nat := 118140960795 + 2453199 * 2 ^ 59
def prefixEnd_2453199 : Nat := 4983230072969 + 3 ^ 40 * 2453199 * 2
def baseEnd_2453199 : Nat := 1259670228129252581330449

theorem tailTrace_2453199 : CollatzResearch.WordTrace tailWord_2453199 prefixEnd_2453199 1259670228129252581330449 := by
  unfold tailWord_2453199
  simp only [CollatzResearch.WordTrace]
  refine ⟨89475518239486470878162651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59650345492990980585441767 89475518239486470878162651)
  ·
    refine ⟨134213277359229706317243977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89475518239486470878162651 134213277359229706317243977)
    ·
      refine ⟨100659958019422279737932983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134213277359229706317243977 100659958019422279737932983)
      ·
        refine ⟨150989937029133419606899475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100659958019422279737932983 150989937029133419606899475)
        ·
          refine ⟨226484905543700129410349213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150989937029133419606899475 226484905543700129410349213)
          ·
            refine ⟨84931839578887548528880955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226484905543700129410349213 84931839578887548528880955)
            ·
              refine ⟨127397759368331322793321433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84931839578887548528880955 127397759368331322793321433)
              ·
                refine ⟨95548319526248492094991075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127397759368331322793321433 95548319526248492094991075)
                ·
                  refine ⟨143322479289372738142486613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95548319526248492094991075 143322479289372738142486613)
                  ·
                    refine ⟨1679560304172336775107265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 143322479289372738142486613 1679560304172336775107265)
                    ·
                      refine ⟨1259670228129252581330449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679560304172336775107265 1259670228129252581330449)
                      ·
                        rfl

theorem cell23_2453199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 8, 2].length) (baseStart_2453199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453199 prefixEnd_2453199 := by exact prefixLift 2453199
  have htrace : WordTrace (prefixWord ++ tailWord_2453199) baseStart_2453199 baseEnd_2453199 := by
    simpa [prefixWord, tailWord_2453199, baseEnd_2453199] using wordTrace_append hprefix tailTrace_2453199
  have hstable : (prefixWord ++ tailWord_2453199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453199).length < 2 ^ (prefixWord ++ tailWord_2453199).sum := by decide
  have hdescent : baseEnd_2453199 < baseStart_2453199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453226 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 2, 4]
def baseStart_2453226 : Nat := 118140960795 + 2453226 * 2 ^ 59
def prefixEnd_2453226 : Nat := 4983230072969 + 3 ^ 40 * 2453226 * 2
def baseEnd_2453226 : Nat := 419894697368974658564275

theorem tailTrace_2453226 : CollatzResearch.WordTrace tailWord_2453226 prefixEnd_2453226 419894697368974658564275 := by
  unfold tailWord_2453226
  simp only [CollatzResearch.WordTrace]
  refine ⟨22369125752597163622348883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59651002006925769659597021 22369125752597163622348883)
  ·
    refine ⟨33553688628895745433523325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22369125752597163622348883 33553688628895745433523325)
    ·
      refine ⟨12582633235835904537571247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33553688628895745433523325 12582633235835904537571247)
      ·
        refine ⟨18873949853753856806356871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12582633235835904537571247 18873949853753856806356871)
        ·
          refine ⟨28310924780630785209535307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18873949853753856806356871 28310924780630785209535307)
          ·
            refine ⟨42466387170946177814302961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28310924780630785209535307 42466387170946177814302961)
            ·
              refine ⟨31849790378209633360727221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42466387170946177814302961 31849790378209633360727221)
              ·
                refine ⟨2985917847957153127568177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31849790378209633360727221 2985917847957153127568177)
                ·
                  refine ⟨2239438385967864845676133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2985917847957153127568177 2239438385967864845676133)
                  ·
                    refine ⟨419894697368974658564275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2239438385967864845676133 419894697368974658564275)
                    ·
                      rfl

theorem cell23_2453226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_2453226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453226 prefixEnd_2453226 := by exact prefixLift 2453226
  have htrace : WordTrace (prefixWord ++ tailWord_2453226) baseStart_2453226 baseEnd_2453226 := by
    simpa [prefixWord, tailWord_2453226, baseEnd_2453226] using wordTrace_append hprefix tailTrace_2453226
  have hstable : (prefixWord ++ tailWord_2453226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453226).length < 2 ^ (prefixWord ++ tailWord_2453226).sum := by decide
  have hdescent : baseEnd_2453226 < baseStart_2453226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453233 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 3, 2, 2]
def baseStart_2453233 : Nat := 118140960795 + 2453233 * 2 ^ 59
def prefixEnd_2453233 : Nat := 4983230072969 + 3 ^ 40 * 2453233 * 2
def baseEnd_2453233 : Nat := 1259687686471505448305293

theorem tailTrace_2453233 : CollatzResearch.WordTrace tailWord_2453233 prefixEnd_2453233 1259687686471505448305293 := by
  unfold tailWord_2453233
  simp only [CollatzResearch.WordTrace]
  refine ⟨89476758321363294684900353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59651172214242196456600235 89476758321363294684900353)
  ·
    refine ⟨67107568741022471013675265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89476758321363294684900353 67107568741022471013675265)
    ·
      refine ⟨50330676555766853260256449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67107568741022471013675265 50330676555766853260256449)
      ·
        refine ⟨37748007416825139945192337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50330676555766853260256449 37748007416825139945192337)
        ·
          refine ⟨28311005562618854958894253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37748007416825139945192337 28311005562618854958894253)
          ·
            refine ⟨10616627085982070609585345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28311005562618854958894253 10616627085982070609585345)
            ·
              refine ⟨7962470314486552957189009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10616627085982070609585345 7962470314486552957189009)
              ·
                refine ⟨5971852735864914717891757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7962470314486552957189009 5971852735864914717891757)
                ·
                  refine ⟨2239444775949343019209409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5971852735864914717891757 2239444775949343019209409)
                  ·
                    refine ⟨1679583581962007264407057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2239444775949343019209409 1679583581962007264407057)
                    ·
                      refine ⟨1259687686471505448305293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679583581962007264407057 1259687686471505448305293)
                      ·
                        rfl

theorem cell23_2453233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_2453233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453233 prefixEnd_2453233 := by exact prefixLift 2453233
  have htrace : WordTrace (prefixWord ++ tailWord_2453233) baseStart_2453233 baseEnd_2453233 := by
    simpa [prefixWord, tailWord_2453233, baseEnd_2453233] using wordTrace_append hprefix tailTrace_2453233
  have hstable : (prefixWord ++ tailWord_2453233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453233).length < 2 ^ (prefixWord ++ tailWord_2453233).sum := by decide
  have hdescent : baseEnd_2453233 < baseStart_2453233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453239 : List Nat := [1, 1, 3, 1, 1, 1, 8, 7]
def baseStart_2453239 : Nat := 118140960795 + 2453239 * 2 ^ 59
def prefixEnd_2453239 : Nat := 4983230072969 + 3 ^ 40 * 2453239 * 2
def baseEnd_2453239 : Nat := 46655213605756756475195

theorem tailTrace_2453239 : CollatzResearch.WordTrace tailWord_2453239 prefixEnd_2453239 46655213605756756475195 := by
  unfold tailWord_2453239
  simp only [CollatzResearch.WordTrace]
  refine ⟨89476977159341557709618771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59651318106227705139745847 89476977159341557709618771)
  ·
    refine ⟨134215465739012336564428157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89476977159341557709618771 134215465739012336564428157)
    ·
      refine ⟨50330799652129626211660559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134215465739012336564428157 50330799652129626211660559)
      ·
        refine ⟨75496199478194439317490839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50330799652129626211660559 75496199478194439317490839)
        ·
          refine ⟨113244299217291658976236259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75496199478194439317490839 113244299217291658976236259)
          ·
            refine ⟨169866448825937488464354389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113244299217291658976236259 169866448825937488464354389)
            ·
              refine ⟨1990622447178954942941653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 169866448825937488464354389 1990622447178954942941653)
              ·
                refine ⟨46655213605756756475195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1990622447178954942941653 46655213605756756475195)
                ·
                  rfl

theorem cell23_2453239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 7].length) (baseStart_2453239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453239 prefixEnd_2453239 := by exact prefixLift 2453239
  have htrace : WordTrace (prefixWord ++ tailWord_2453239) baseStart_2453239 baseEnd_2453239 := by
    simpa [prefixWord, tailWord_2453239, baseEnd_2453239] using wordTrace_append hprefix tailTrace_2453239
  have hstable : (prefixWord ++ tailWord_2453239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453239).length < 2 ^ (prefixWord ++ tailWord_2453239).sum := by decide
  have hdescent : baseEnd_2453239 < baseStart_2453239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453261 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2453261 : Nat := 118140960795 + 2453261 * 2 ^ 59
def prefixEnd_2453261 : Nat := 4983230072969 + 3 ^ 40 * 2453261 * 2
def baseEnd_2453261 : Nat := 1259702063929831338755165

theorem tailTrace_2453261 : CollatzResearch.WordTrace tailWord_2453261 prefixEnd_2453261 1259702063929831338755165 := by
  unfold tailWord_2453261
  simp only [CollatzResearch.WordTrace]
  refine ⟨89477779565261855466919637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59651853043507903644613091 89477779565261855466919637)
  ·
    refine ⟨2097135458560824737505929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 89477779565261855466919637 2097135458560824737505929)
    ·
      refine ⟨1572851593920618553129447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2097135458560824737505929 1572851593920618553129447)
      ·
        refine ⟨2359277390880927829694171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572851593920618553129447 2359277390880927829694171)
        ·
          refine ⟨3538916086321391744541257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359277390880927829694171 3538916086321391744541257)
          ·
            refine ⟨2654187064741043808405943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3538916086321391744541257 2654187064741043808405943)
            ·
              refine ⟨3981280597111565712608915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654187064741043808405943 3981280597111565712608915)
              ·
                refine ⟨5971920895667348568913373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3981280597111565712608915 5971920895667348568913373)
                ·
                  refine ⟨2239470335875255713342515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5971920895667348568913373 2239470335875255713342515)
                  ·
                    refine ⟨3359205503812883570013773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2239470335875255713342515 3359205503812883570013773)
                    ·
                      refine ⟨1259702063929831338755165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3359205503812883570013773 1259702063929831338755165)
                      ·
                        rfl

theorem cell23_2453261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2453261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453261 prefixEnd_2453261 := by exact prefixLift 2453261
  have htrace : WordTrace (prefixWord ++ tailWord_2453261) baseStart_2453261 baseEnd_2453261 := by
    simpa [prefixWord, tailWord_2453261, baseEnd_2453261] using wordTrace_append hprefix tailTrace_2453261
  have hstable : (prefixWord ++ tailWord_2453261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453261).length < 2 ^ (prefixWord ++ tailWord_2453261).sum := by decide
  have hdescent : baseEnd_2453261 < baseStart_2453261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453318 : List Nat := [6, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_2453318 : Nat := 118140960795 + 2453318 * 2 ^ 59
def prefixEnd_2453318 : Nat := 4983230072969 + 3 ^ 40 * 2453318 * 2
def baseEnd_2453318 : Nat := 1259731332327137615742403

theorem tailTrace_2453318 : CollatzResearch.WordTrace tailWord_2453318 prefixEnd_2453318 1259731332327137615742403 := by
  unfold tailWord_2453318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2796245578939229818804519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59653239017370236134496405 2796245578939229818804519)
  ·
    refine ⟨4194368368408844728206779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2796245578939229818804519 4194368368408844728206779)
    ·
      refine ⟨6291552552613267092310169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4194368368408844728206779 6291552552613267092310169)
      ·
        refine ⟨4718664414459950319232627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6291552552613267092310169 4718664414459950319232627)
        ·
          refine ⟨7077996621689925478848941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4718664414459950319232627 7077996621689925478848941)
          ·
            refine ⟨2654248733133722054568353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7077996621689925478848941 2654248733133722054568353)
            ·
              refine ⟨1990686549850291540926265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2654248733133722054568353 1990686549850291540926265)
              ·
                refine ⟨1493014912387718655694699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1990686549850291540926265 1493014912387718655694699)
                ·
                  refine ⟨2239522368581577983542049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493014912387718655694699 2239522368581577983542049)
                  ·
                    refine ⟨1679641776436183487656537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2239522368581577983542049 1679641776436183487656537)
                    ·
                      refine ⟨1259731332327137615742403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679641776436183487656537 1259731332327137615742403)
                      ·
                        rfl

theorem cell23_2453318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_2453318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453318 prefixEnd_2453318 := by exact prefixLift 2453318
  have htrace : WordTrace (prefixWord ++ tailWord_2453318) baseStart_2453318 baseEnd_2453318 := by
    simpa [prefixWord, tailWord_2453318, baseEnd_2453318] using wordTrace_append hprefix tailTrace_2453318
  have hstable : (prefixWord ++ tailWord_2453318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453318).length < 2 ^ (prefixWord ++ tailWord_2453318).sum := by decide
  have hdescent : baseEnd_2453318 < baseStart_2453318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453346 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 9]
def baseStart_2453346 : Nat := 118140960795 + 2453346 * 2 ^ 59
def prefixEnd_2453346 : Nat := 4983230072969 + 3 ^ 40 * 2453346 * 2
def baseEnd_2453346 : Nat := 139971745531718167354697

theorem tailTrace_2453346 : CollatzResearch.WordTrace tailWord_2453346 prefixEnd_2453346 139971745531718167354697 := by
  unfold tailWord_2453346
  simp only [CollatzResearch.WordTrace]
  refine ⟨22370219942488478745940973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59653919846635943322509261 22370219942488478745940973)
  ·
    refine ⟨8388832478433179529727865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22370219942488478745940973 8388832478433179529727865)
    ·
      refine ⟨6291624358824884647295899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8388832478433179529727865 6291624358824884647295899)
      ·
        refine ⟨9437436538237326970943849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6291624358824884647295899 9437436538237326970943849)
        ·
          refine ⟨7078077403677995228207887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9437436538237326970943849 7078077403677995228207887)
          ·
            refine ⟨10617116105516992842311831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7078077403677995228207887 10617116105516992842311831)
            ·
              refine ⟨15925674158275489263467747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10617116105516992842311831 15925674158275489263467747)
              ·
                refine ⟨23888511237413233895201621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15925674158275489263467747 23888511237413233895201621)
                ·
                  refine ⟨139971745531718167354697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23888511237413233895201621 139971745531718167354697)
                  ·
                    rfl

theorem cell23_2453346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_2453346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453346 prefixEnd_2453346 := by exact prefixLift 2453346
  have htrace : WordTrace (prefixWord ++ tailWord_2453346) baseStart_2453346 baseEnd_2453346 := by
    simpa [prefixWord, tailWord_2453346, baseEnd_2453346] using wordTrace_append hprefix tailTrace_2453346
  have hstable : (prefixWord ++ tailWord_2453346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453346).length < 2 ^ (prefixWord ++ tailWord_2453346).sum := by decide
  have hdescent : baseEnd_2453346 < baseStart_2453346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453374 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2453374 : Nat := 118140960795 + 2453374 * 2 ^ 59
def prefixEnd_2453374 : Nat := 4983230072969 + 3 ^ 40 * 2453374 * 2
def baseEnd_2453374 : Nat := 1259760087243789396642145

theorem tailTrace_2453374 : CollatzResearch.WordTrace tailWord_2453374 prefixEnd_2453374 1259760087243789396642145 := by
  unfold tailWord_2453374
  simp only [CollatzResearch.WordTrace]
  refine ⟨11185237626731559470722897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59654600675901650510522117 11185237626731559470722897)
  ·
    refine ⟨8388928220048669603042173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11185237626731559470722897 8388928220048669603042173)
    ·
      refine ⟨3145848082518251101140815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8388928220048669603042173 3145848082518251101140815)
      ·
        refine ⟨4718772123777376651711223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3145848082518251101140815 4718772123777376651711223)
        ·
          refine ⟨7078158185666064977566835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4718772123777376651711223 7078158185666064977566835)
          ·
            refine ⟨10617237278499097466350253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7078158185666064977566835 10617237278499097466350253)
            ·
              refine ⟨3981463979437161549881345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10617237278499097466350253 3981463979437161549881345)
              ·
                refine ⟨2986097984577871162411009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3981463979437161549881345 2986097984577871162411009)
                ·
                  refine ⟨2239573488433403371808257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2986097984577871162411009 2239573488433403371808257)
                  ·
                    refine ⟨1679680116325052528856193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2239573488433403371808257 1679680116325052528856193)
                    ·
                      refine ⟨1259760087243789396642145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679680116325052528856193 1259760087243789396642145)
                      ·
                        rfl

theorem cell23_2453374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2453374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453374 prefixEnd_2453374 := by exact prefixLift 2453374
  have htrace : WordTrace (prefixWord ++ tailWord_2453374) baseStart_2453374 baseEnd_2453374 := by
    simpa [prefixWord, tailWord_2453374, baseEnd_2453374] using wordTrace_append hprefix tailTrace_2453374
  have hstable : (prefixWord ++ tailWord_2453374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453374).length < 2 ^ (prefixWord ++ tailWord_2453374).sum := by decide
  have hdescent : baseEnd_2453374 < baseStart_2453374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453433 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 2, 2, 3]
def baseStart_2453433 : Nat := 118140960795 + 2453433 * 2 ^ 59
def prefixEnd_2453433 : Nat := 4983230072969 + 3 ^ 40 * 2453433 * 2
def baseEnd_2453433 : Nat := 1259790382602404665804373

theorem tailTrace_2453433 : CollatzResearch.WordTrace tailWord_2453433 prefixEnd_2453433 1259790382602404665804373 := by
  unfold tailWord_2453433
  simp only [CollatzResearch.WordTrace]
  refine ⟨89484052920638728842180953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59656035280425819228120635 89484052920638728842180953)
  ·
    refine ⟨67113039690479046631635715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89484052920638728842180953 67113039690479046631635715)
    ·
      refine ⟨100669559535718569947453573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67113039690479046631635715 100669559535718569947453573)
      ·
        refine ⟨18875542412947231865147545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100669559535718569947453573 18875542412947231865147545)
        ·
          refine ⟨14156656809710423898860659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18875542412947231865147545 14156656809710423898860659)
          ·
            refine ⟨21234985214565635848290989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14156656809710423898860659 21234985214565635848290989)
            ·
              refine ⟨7963119455462113443109121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21234985214565635848290989 7963119455462113443109121)
              ·
                refine ⟨5972339591596585082331841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7963119455462113443109121 5972339591596585082331841)
                ·
                  refine ⟨4479254693697438811748881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5972339591596585082331841 4479254693697438811748881)
                  ·
                    refine ⟨3359441020273079108811661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4479254693697438811748881 3359441020273079108811661)
                    ·
                      refine ⟨1259790382602404665804373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3359441020273079108811661 1259790382602404665804373)
                      ·
                        rfl

theorem cell23_2453433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_2453433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453433 prefixEnd_2453433 := by exact prefixLift 2453433
  have htrace : WordTrace (prefixWord ++ tailWord_2453433) baseStart_2453433 baseEnd_2453433 := by
    simpa [prefixWord, tailWord_2453433, baseEnd_2453433] using wordTrace_append hprefix tailTrace_2453433
  have hstable : (prefixWord ++ tailWord_2453433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453433).length < 2 ^ (prefixWord ++ tailWord_2453433).sum := by decide
  have hdescent : baseEnd_2453433 < baseStart_2453433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453463 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 5, 1, 3]
def baseStart_2453463 : Nat := 118140960795 + 2453463 * 2 ^ 59
def prefixEnd_2453463 : Nat := 4983230072969 + 3 ^ 40 * 2453463 * 2
def baseEnd_2453463 : Nat := 1259805787022039548429235

theorem tailTrace_2453463 : CollatzResearch.WordTrace tailWord_2453463 prefixEnd_2453463 1259805787022039548429235 := by
  unfold tailWord_2453463
  simp only [CollatzResearch.WordTrace]
  refine ⟨89485147110530043965773043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59656764740353362643848695 89485147110530043965773043)
  ·
    refine ⟨134227720665795065948659565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89485147110530043965773043 134227720665795065948659565)
    ·
      refine ⟨50335395249673149730747337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134227720665795065948659565 50335395249673149730747337)
      ·
        refine ⟨37751546437254862298060503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50335395249673149730747337 37751546437254862298060503)
        ·
          refine ⟨56627319655882293447090755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37751546437254862298060503 56627319655882293447090755)
          ·
            refine ⟨84940979483823440170636133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56627319655882293447090755 84940979483823440170636133)
            ·
              refine ⟨15926433653216895031994275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84940979483823440170636133 15926433653216895031994275)
              ·
                refine ⟨23889650479825342547991413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15926433653216895031994275 23889650479825342547991413)
                ·
                  refine ⟨2239654732483625863874195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23889650479825342547991413 2239654732483625863874195)
                  ·
                    refine ⟨3359482098725438795811293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2239654732483625863874195 3359482098725438795811293)
                    ·
                      refine ⟨1259805787022039548429235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3359482098725438795811293 1259805787022039548429235)
                      ·
                        rfl

theorem cell23_2453463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_2453463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453463 prefixEnd_2453463 := by exact prefixLift 2453463
  have htrace : WordTrace (prefixWord ++ tailWord_2453463) baseStart_2453463 baseEnd_2453463 := by
    simpa [prefixWord, tailWord_2453463, baseEnd_2453463] using wordTrace_append hprefix tailTrace_2453463
  have hstable : (prefixWord ++ tailWord_2453463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453463).length < 2 ^ (prefixWord ++ tailWord_2453463).sum := by decide
  have hdescent : baseEnd_2453463 < baseStart_2453463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453473 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 1, 5, 2]
def baseStart_2453473 : Nat := 118140960795 + 2453473 * 2 ^ 59
def prefixEnd_2453473 : Nat := 4983230072969 + 3 ^ 40 * 2453473 * 2
def baseEnd_2453473 : Nat := 1259810921828584509304189

theorem tailTrace_2453473 : CollatzResearch.WordTrace tailWord_2453473 prefixEnd_2453473 1259810921828584509304189 := by
  unfold tailWord_2453473
  simp only [CollatzResearch.WordTrace]
  refine ⟨89485511840493815673637073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59657007893662543782424715 89485511840493815673637073)
  ·
    refine ⟨67114133880370361755227805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89485511840493815673637073 67114133880370361755227805)
    ·
      refine ⟨25167800205138885658210427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67114133880370361755227805 25167800205138885658210427)
      ·
        refine ⟨37751700307708328487315641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25167800205138885658210427 37751700307708328487315641)
        ·
          refine ⟨28313775230781246365486731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37751700307708328487315641 28313775230781246365486731)
          ·
            refine ⟨42470662846171869548230097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28313775230781246365486731 42470662846171869548230097)
            ·
              refine ⟨31852997134628902161172573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42470662846171869548230097 31852997134628902161172573)
              ·
                refine ⟨11944873925485838310439715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31852997134628902161172573 11944873925485838310439715)
                ·
                  refine ⟨17917310888228757465659573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11944873925485838310439715 17917310888228757465659573)
                  ·
                    refine ⟨1679747895771446012405585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17917310888228757465659573 1679747895771446012405585)
                    ·
                      refine ⟨1259810921828584509304189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679747895771446012405585 1259810921828584509304189)
                      ·
                        rfl

theorem cell23_2453473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_2453473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453473 prefixEnd_2453473 := by exact prefixLift 2453473
  have htrace : WordTrace (prefixWord ++ tailWord_2453473) baseStart_2453473 baseEnd_2453473 := by
    simpa [prefixWord, tailWord_2453473, baseEnd_2453473] using wordTrace_append hprefix tailTrace_2453473
  have hstable : (prefixWord ++ tailWord_2453473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453473).length < 2 ^ (prefixWord ++ tailWord_2453473).sum := by decide
  have hdescent : baseEnd_2453473 < baseStart_2453473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453497 : List Nat := [1, 2, 1, 3, 1, 5, 1, 4, 1, 1, 3]
def baseStart_2453497 : Nat := 118140960795 + 2453497 * 2 ^ 59
def prefixEnd_2453497 : Nat := 4983230072969 + 3 ^ 40 * 2453497 * 2
def baseEnd_2453497 : Nat := 1259823245364292415404079

theorem tailTrace_2453497 : CollatzResearch.WordTrace tailWord_2453497 prefixEnd_2453497 1259823245364292415404079 := by
  unfold tailWord_2453497
  simp only [CollatzResearch.WordTrace]
  refine ⟨89486387192406867772510745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59657591461604578515007163 89486387192406867772510745)
  ·
    refine ⟨67114790394305150829383059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89486387192406867772510745 67114790394305150829383059)
    ·
      refine ⟨100672185591457726244074589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67114790394305150829383059 100672185591457726244074589)
      ·
        refine ⟨37752069596796647341527971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100672185591457726244074589 37752069596796647341527971)
        ·
          refine ⟨56628104395194971012291957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37752069596796647341527971 56628104395194971012291957)
          ·
            refine ⟨5308884787049528532402371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56628104395194971012291957 5308884787049528532402371)
            ·
              refine ⟨7963327180574292798603557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5308884787049528532402371 7963327180574292798603557)
              ·
                refine ⟨1493123846357679899738167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7963327180574292798603557 1493123846357679899738167)
                ·
                  refine ⟨2239685769536519849607251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493123846357679899738167 2239685769536519849607251)
                  ·
                    refine ⟨3359528654304779774410877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2239685769536519849607251 3359528654304779774410877)
                    ·
                      refine ⟨1259823245364292415404079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3359528654304779774410877 1259823245364292415404079)
                      ·
                        rfl

theorem cell23_2453497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_2453497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453497 prefixEnd_2453497 := by exact prefixLift 2453497
  have htrace : WordTrace (prefixWord ++ tailWord_2453497) baseStart_2453497 baseEnd_2453497 := by
    simpa [prefixWord, tailWord_2453497, baseEnd_2453497] using wordTrace_append hprefix tailTrace_2453497
  have hstable : (prefixWord ++ tailWord_2453497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453497).length < 2 ^ (prefixWord ++ tailWord_2453497).sum := by decide
  have hdescent : baseEnd_2453497 < baseStart_2453497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453520 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 3, 2, 2]
def baseStart_2453520 : Nat := 118140960795 + 2453520 * 2 ^ 59
def prefixEnd_2453520 : Nat := 4983230072969 + 3 ^ 40 * 2453520 * 2
def baseEnd_2453520 : Nat := 1259835055419345825416473

theorem tailTrace_2453520 : CollatzResearch.WordTrace tailWord_2453520 prefixEnd_2453520 1259835055419345825416473 := by
  unfold tailWord_2453520
  simp only [CollatzResearch.WordTrace]
  refine ⟨44743613035661771350299007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59658150714215695133732009 44743613035661771350299007)
  ·
    refine ⟨67115419553492657025448511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44743613035661771350299007 67115419553492657025448511)
    ·
      refine ⟨100673129330238985538172767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67115419553492657025448511 100673129330238985538172767)
      ·
        refine ⟨151009693995358478307259151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100673129330238985538172767 151009693995358478307259151)
        ·
          refine ⟨226514540993037717460888727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151009693995358478307259151 226514540993037717460888727)
          ·
            refine ⟨339771811489556576191333091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226514540993037717460888727 339771811489556576191333091)
            ·
              refine ⟨509657717234334864286999637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339771811489556576191333091 509657717234334864286999637)
              ·
                refine ⟨5972551373839861690863277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 509657717234334864286999637 5972551373839861690863277)
                ·
                  refine ⟨2239706765189948134073729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5972551373839861690863277 2239706765189948134073729)
                  ·
                    refine ⟨1679780073892461100555297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2239706765189948134073729 1679780073892461100555297)
                    ·
                      refine ⟨1259835055419345825416473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679780073892461100555297 1259835055419345825416473)
                      ·
                        rfl

theorem cell23_2453520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3, 2, 2].length) (baseStart_2453520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453520 prefixEnd_2453520 := by exact prefixLift 2453520
  have htrace : WordTrace (prefixWord ++ tailWord_2453520) baseStart_2453520 baseEnd_2453520 := by
    simpa [prefixWord, tailWord_2453520, baseEnd_2453520] using wordTrace_append hprefix tailTrace_2453520
  have hstable : (prefixWord ++ tailWord_2453520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453520).length < 2 ^ (prefixWord ++ tailWord_2453520).sum := by decide
  have hdescent : baseEnd_2453520 < baseStart_2453520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453523 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 3]
def baseStart_2453523 : Nat := 118140960795 + 2453523 * 2 ^ 59
def prefixEnd_2453523 : Nat := 4983230072969 + 3 ^ 40 * 2453523 * 2
def baseEnd_2453523 : Nat := 1259836595861309313678959

theorem tailTrace_2453523 : CollatzResearch.WordTrace tailWord_2453523 prefixEnd_2453523 1259836595861309313678959 := by
  unfold tailWord_2453523
  simp only [CollatzResearch.WordTrace]
  refine ⟨89487335490312674212957223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59658223660208449475304815 89487335490312674212957223)
  ·
    refine ⟨134231003235469011319435835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89487335490312674212957223 134231003235469011319435835)
    ·
      refine ⟨201346504853203516979153753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134231003235469011319435835 201346504853203516979153753)
      ·
        refine ⟨151009878639902637734365315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201346504853203516979153753 151009878639902637734365315)
        ·
          refine ⟨226514817959853956601547973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151009878639902637734365315 226514817959853956601547973)
          ·
            refine ⟨42471528367472616862790245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226514817959853956601547973 42471528367472616862790245)
            ·
              refine ⟨7963411568901115661773171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42471528367472616862790245 7963411568901115661773171)
              ·
                refine ⟨11945117353351673492659757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7963411568901115661773171 11945117353351673492659757)
                ·
                  refine ⟨4479419007506877559747409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11945117353351673492659757 4479419007506877559747409)
                  ·
                    refine ⟨3359564255630158169810557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4479419007506877559747409 3359564255630158169810557)
                    ·
                      refine ⟨1259836595861309313678959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3359564255630158169810557 1259836595861309313678959)
                      ·
                        rfl

theorem cell23_2453523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 3].length) (baseStart_2453523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453523 prefixEnd_2453523 := by exact prefixLift 2453523
  have htrace : WordTrace (prefixWord ++ tailWord_2453523) baseStart_2453523 baseEnd_2453523 := by
    simpa [prefixWord, tailWord_2453523, baseEnd_2453523] using wordTrace_append hprefix tailTrace_2453523
  have hstable : (prefixWord ++ tailWord_2453523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453523).length < 2 ^ (prefixWord ++ tailWord_2453523).sum := by decide
  have hdescent : baseEnd_2453523 < baseStart_2453523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453524 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_2453524 : Nat := 118140960795 + 2453524 * 2 ^ 59
def prefixEnd_2453524 : Nat := 4983230072969 + 3 ^ 40 * 2453524 * 2
def baseEnd_2453524 : Nat := 1259837109341963809766455

theorem tailTrace_2453524 : CollatzResearch.WordTrace tailWord_2453524 prefixEnd_2453524 1259837109341963809766455 := by
  unfold tailWord_2453524
  simp only [CollatzResearch.WordTrace]
  refine ⟨44743685981654525691871813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59658247975539367589162417 44743685981654525691871813)
  ·
    refine ⟨8389441121560223567225965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44743685981654525691871813 8389441121560223567225965)
    ·
      refine ⟨3146040420585083837709737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8389441121560223567225965 3146040420585083837709737)
      ·
        refine ⟨2359530315438812878282303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3146040420585083837709737 2359530315438812878282303)
        ·
          refine ⟨3539295473158219317423455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359530315438812878282303 3539295473158219317423455)
          ·
            refine ⟨5308943209737328976135183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3539295473158219317423455 5308943209737328976135183)
            ·
              refine ⟨7963414814605993464202775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5308943209737328976135183 7963414814605993464202775)
              ·
                refine ⟨11945122221908990196304163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7963414814605993464202775 11945122221908990196304163)
                ·
                  refine ⟨17917683332863485294456245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11945122221908990196304163 17917683332863485294456245)
                  ·
                    refine ⟨1679782812455951746355273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17917683332863485294456245 1679782812455951746355273)
                    ·
                      refine ⟨1259837109341963809766455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679782812455951746355273 1259837109341963809766455)
                      ·
                        rfl

theorem cell23_2453524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_2453524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453524 prefixEnd_2453524 := by exact prefixLift 2453524
  have htrace : WordTrace (prefixWord ++ tailWord_2453524) baseStart_2453524 baseEnd_2453524 := by
    simpa [prefixWord, tailWord_2453524, baseEnd_2453524] using wordTrace_append hprefix tailTrace_2453524
  have hstable : (prefixWord ++ tailWord_2453524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453524).length < 2 ^ (prefixWord ++ tailWord_2453524).sum := by decide
  have hdescent : baseEnd_2453524 < baseStart_2453524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453554 : List Nat := [3, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2]
def baseStart_2453554 : Nat := 118140960795 + 2453554 * 2 ^ 59
def prefixEnd_2453554 : Nat := 4983230072969 + 3 ^ 40 * 2453554 * 2
def baseEnd_2453554 : Nat := 1259852513761598692391317

theorem tailTrace_2453554 : CollatzResearch.WordTrace tailWord_2453554 prefixEnd_2453554 1259852513761598692391317 := by
  unfold tailWord_2453554
  simp only [CollatzResearch.WordTrace]
  refine ⟨22372116538300091626833929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59658977435466911004890477 22372116538300091626833929)
  ·
    refine ⟨16779087403725068720125447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22372116538300091626833929 16779087403725068720125447)
    ·
      refine ⟨25168631105587603080188171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16779087403725068720125447 25168631105587603080188171)
      ·
        refine ⟨37752946658381404620282257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25168631105587603080188171 37752946658381404620282257)
        ·
          refine ⟨28314709993786053465211693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37752946658381404620282257 28314709993786053465211693)
          ·
            refine ⟨10618016247669770049454385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28314709993786053465211693 10618016247669770049454385)
            ·
              refine ⟨7963512185752327537090789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10618016247669770049454385 7963512185752327537090789)
              ·
                refine ⟨1493158534828561413204523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7963512185752327537090789 1493158534828561413204523)
                ·
                  refine ⟨2239737802242842119806785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493158534828561413204523 2239737802242842119806785)
                  ·
                    refine ⟨1679803351682131589855089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2239737802242842119806785 1679803351682131589855089)
                    ·
                      refine ⟨1259852513761598692391317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679803351682131589855089 1259852513761598692391317)
                      ·
                        rfl

theorem cell23_2453554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_2453554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453554 prefixEnd_2453554 := by exact prefixLift 2453554
  have htrace : WordTrace (prefixWord ++ tailWord_2453554) baseStart_2453554 baseEnd_2453554 := by
    simpa [prefixWord, tailWord_2453554, baseEnd_2453554] using wordTrace_append hprefix tailTrace_2453554
  have hstable : (prefixWord ++ tailWord_2453554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453554).length < 2 ^ (prefixWord ++ tailWord_2453554).sum := by decide
  have hdescent : baseEnd_2453554 < baseStart_2453554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453574 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2453574 : Nat := 118140960795 + 2453574 * 2 ^ 59
def prefixEnd_2453574 : Nat := 4983230072969 + 3 ^ 40 * 2453574 * 2
def baseEnd_2453574 : Nat := 1259862783374688614141225

theorem tailTrace_2453574 : CollatzResearch.WordTrace tailWord_2453574 prefixEnd_2453574 1259862783374688614141225 := by
  unfold tailWord_2453574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2796537362910247185095743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59659463742085273282042517 2796537362910247185095743)
  ·
    refine ⟨4194806044365370777643615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2796537362910247185095743 4194806044365370777643615)
    ·
      refine ⟨6292209066548056166465423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4194806044365370777643615 6292209066548056166465423)
      ·
        refine ⟨9438313599822084249698135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6292209066548056166465423 9438313599822084249698135)
        ·
          refine ⟨14157470399733126374547203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9438313599822084249698135 14157470399733126374547203)
          ·
            refine ⟨21236205599599689561820805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14157470399733126374547203 21236205599599689561820805)
            ·
              refine ⟨3981788549924941792841401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21236205599599689561820805 3981788549924941792841401)
              ·
                refine ⟨2986341412443706344631051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3981788549924941792841401 2986341412443706344631051)
                ·
                  refine ⟨4479512118665559516946577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986341412443706344631051 4479512118665559516946577)
                  ·
                    refine ⟨3359634088999169637709933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4479512118665559516946577 3359634088999169637709933)
                    ·
                      refine ⟨1259862783374688614141225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3359634088999169637709933 1259862783374688614141225)
                      ·
                        rfl

theorem cell23_2453574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2453574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453574 prefixEnd_2453574 := by exact prefixLift 2453574
  have htrace : WordTrace (prefixWord ++ tailWord_2453574) baseStart_2453574 baseEnd_2453574 := by
    simpa [prefixWord, tailWord_2453574, baseEnd_2453574] using wordTrace_append hprefix tailTrace_2453574
  have hstable : (prefixWord ++ tailWord_2453574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453574).length < 2 ^ (prefixWord ++ tailWord_2453574).sum := by decide
  have hdescent : baseEnd_2453574 < baseStart_2453574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453576 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_2453576 : Nat := 118140960795 + 2453576 * 2 ^ 59
def prefixEnd_2453576 : Nat := 4983230072969 + 3 ^ 40 * 2453576 * 2
def baseEnd_2453576 : Nat := 1259863810335997606316215

theorem tailTrace_2453576 : CollatzResearch.WordTrace tailWord_2453576 prefixEnd_2453576 1259863810335997606316215 := by
  unfold tailWord_2453576
  simp only [CollatzResearch.WordTrace]
  refine ⟨44744634279560332132318291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59659512372747109509757721 44744634279560332132318291)
  ·
    refine ⟨67116951419340498198477437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44744634279560332132318291 67116951419340498198477437)
    ·
      refine ⟨25168856782252686824429039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67116951419340498198477437 25168856782252686824429039)
      ·
        refine ⟨37753285173379030236643559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25168856782252686824429039 37753285173379030236643559)
        ·
          refine ⟨56629927760068545354965339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37753285173379030236643559 56629927760068545354965339)
          ·
            refine ⟨84944891640102818032448009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56629927760068545354965339 84944891640102818032448009)
            ·
              refine ⟨63708668730077113524336007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84944891640102818032448009 63708668730077113524336007)
              ·
                refine ⟨95563003095115670286504011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63708668730077113524336007 95563003095115670286504011)
                ·
                  refine ⟨143344504642673505429756017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95563003095115670286504011 143344504642673505429756017)
                  ·
                    refine ⟨107508378482005129072317013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 143344504642673505429756017 107508378482005129072317013)
                    ·
                      refine ⟨1259863810335997606316215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 107508378482005129072317013 1259863810335997606316215)
                      ·
                        rfl

theorem cell23_2453576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_2453576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453576 prefixEnd_2453576 := by exact prefixLift 2453576
  have htrace : WordTrace (prefixWord ++ tailWord_2453576) baseStart_2453576 baseEnd_2453576 := by
    simpa [prefixWord, tailWord_2453576, baseEnd_2453576] using wordTrace_append hprefix tailTrace_2453576
  have hstable : (prefixWord ++ tailWord_2453576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453576).length < 2 ^ (prefixWord ++ tailWord_2453576).sum := by decide
  have hdescent : baseEnd_2453576 < baseStart_2453576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453580 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 3, 3, 2]
def baseStart_2453580 : Nat := 118140960795 + 2453580 * 2 ^ 59
def prefixEnd_2453580 : Nat := 4983230072969 + 3 ^ 40 * 2453580 * 2
def baseEnd_2453580 : Nat := 1259865864258615590666197

theorem tailTrace_2453580 : CollatzResearch.WordTrace tailWord_2453580 prefixEnd_2453580 1259865864258615590666197 := by
  unfold tailWord_2453580
  simp only [CollatzResearch.WordTrace]
  refine ⟨44744707225553086473891097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59659609634070781965188129 44744707225553086473891097)
  ·
    refine ⟨33558530419164814855418323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44744707225553086473891097 33558530419164814855418323)
    ·
      refine ⟨50337795628747222283127485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33558530419164814855418323 50337795628747222283127485)
      ·
        refine ⟨18876673360780208356172807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50337795628747222283127485 18876673360780208356172807)
        ·
          refine ⟨28315010041170312534259211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18876673360780208356172807 28315010041170312534259211)
          ·
            refine ⟨42472515061755468801388817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28315010041170312534259211 42472515061755468801388817)
            ·
              refine ⟨31854386296316601601041613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42472515061755468801388817 31854386296316601601041613)
              ·
                refine ⟨11945394861118725600390605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31854386296316601601041613 11945394861118725600390605)
                ·
                  refine ⟨4479523072919522100146477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11945394861118725600390605 4479523072919522100146477)
                  ·
                    refine ⟨1679821152344820787554929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4479523072919522100146477 1679821152344820787554929)
                    ·
                      refine ⟨1259865864258615590666197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679821152344820787554929 1259865864258615590666197)
                      ·
                        rfl

theorem cell23_2453580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_2453580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453580 prefixEnd_2453580 := by exact prefixLift 2453580
  have htrace : WordTrace (prefixWord ++ tailWord_2453580) baseStart_2453580 baseEnd_2453580 := by
    simpa [prefixWord, tailWord_2453580, baseEnd_2453580] using wordTrace_append hprefix tailTrace_2453580
  have hstable : (prefixWord ++ tailWord_2453580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453580).length < 2 ^ (prefixWord ++ tailWord_2453580).sum := by decide
  have hdescent : baseEnd_2453580 < baseStart_2453580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453613 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2453613 : Nat := 118140960795 + 2453613 * 2 ^ 59
def prefixEnd_2453613 : Nat := 4983230072969 + 3 ^ 40 * 2453613 * 2
def baseEnd_2453613 : Nat := 1259882809120213961553545

theorem tailTrace_2453613 : CollatzResearch.WordTrace tailWord_2453613 prefixEnd_2453613 1259882809120213961553545 := by
  unfold tailWord_2453613
  simp only [CollatzResearch.WordTrace]
  refine ⟨89490618059986619583733493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59660412039991079722488995 89490618059986619583733493)
  ·
    refine ⟨8389745443123745585975015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89490618059986619583733493 8389745443123745585975015)
    ·
      refine ⟨12584618164685618378962523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8389745443123745585975015 12584618164685618378962523)
      ·
        refine ⟨18876927247028427568443785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12584618164685618378962523 18876927247028427568443785)
        ·
          refine ⟨14157695435271320676332839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18876927247028427568443785 14157695435271320676332839)
          ·
            refine ⟨21236543152906981014499259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14157695435271320676332839 21236543152906981014499259)
            ·
              refine ⟨31854814729360471521748889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21236543152906981014499259 31854814729360471521748889)
              ·
                refine ⟨23891111047020353641311667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31854814729360471521748889 23891111047020353641311667)
                ·
                  refine ⟨35836666570530530461967501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23891111047020353641311667 35836666570530530461967501)
                  ·
                    refine ⟨13438749963948948923237813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35836666570530530461967501 13438749963948948923237813)
                    ·
                      refine ⟨1259882809120213961553545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13438749963948948923237813 1259882809120213961553545)
                      ·
                        rfl

theorem cell23_2453613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2453613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453613 prefixEnd_2453613 := by exact prefixLift 2453613
  have htrace : WordTrace (prefixWord ++ tailWord_2453613) baseStart_2453613 baseEnd_2453613 := by
    simpa [prefixWord, tailWord_2453613, baseEnd_2453613] using wordTrace_append hprefix tailTrace_2453613
  have hstable : (prefixWord ++ tailWord_2453613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453613).length < 2 ^ (prefixWord ++ tailWord_2453613).sum := by decide
  have hdescent : baseEnd_2453613 < baseStart_2453613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453643 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 3]
def baseStart_2453643 : Nat := 118140960795 + 2453643 * 2 ^ 59
def prefixEnd_2453643 : Nat := 4983230072969 + 3 ^ 40 * 2453643 * 2
def baseEnd_2453643 : Nat := 1259898213539848844178407

theorem tailTrace_2453643 : CollatzResearch.WordTrace tailWord_2453643 prefixEnd_2453643 1259898213539848844178407 := by
  unfold tailWord_2453643
  simp only [CollatzResearch.WordTrace]
  refine ⟨89491712249877934707325583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59661141499918623138217055 89491712249877934707325583)
  ·
    refine ⟨134237568374816902060988375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89491712249877934707325583 134237568374816902060988375)
    ·
      refine ⟨201356352562225353091482563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134237568374816902060988375 201356352562225353091482563)
      ·
        refine ⟨302034528843338029637223845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201356352562225353091482563 302034528843338029637223845)
        ·
          refine ⟨56631474158125880556979471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302034528843338029637223845 56631474158125880556979471)
          ·
            refine ⟨84947211237188820835469207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56631474158125880556979471 84947211237188820835469207)
            ·
              refine ⟨127420816855783231253203811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84947211237188820835469207 127420816855783231253203811)
              ·
                refine ⟨191131225283674846879805717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127420816855783231253203811 191131225283674846879805717)
                ·
                  refine ⟨8959276185172258447490893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 191131225283674846879805717 8959276185172258447490893)
                  ·
                    refine ⟨3359728569439596917809085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8959276185172258447490893 3359728569439596917809085)
                    ·
                      refine ⟨1259898213539848844178407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3359728569439596917809085 1259898213539848844178407)
                      ·
                        rfl

theorem cell23_2453643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 3].length) (baseStart_2453643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453643 prefixEnd_2453643 := by exact prefixLift 2453643
  have htrace : WordTrace (prefixWord ++ tailWord_2453643) baseStart_2453643 baseEnd_2453643 := by
    simpa [prefixWord, tailWord_2453643, baseEnd_2453643] using wordTrace_append hprefix tailTrace_2453643
  have hstable : (prefixWord ++ tailWord_2453643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453643).length < 2 ^ (prefixWord ++ tailWord_2453643).sum := by decide
  have hdescent : baseEnd_2453643 < baseStart_2453643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453660 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2453660 : Nat := 118140960795 + 2453660 * 2 ^ 59
def prefixEnd_2453660 : Nat := 4983230072969 + 3 ^ 40 * 2453660 * 2
def baseEnd_2453660 : Nat := 1259906942710975277665829

theorem tailTrace_2453660 : CollatzResearch.WordTrace tailWord_2453660 prefixEnd_2453660 1259906942710975277665829 := by
  unfold tailWord_2453660
  simp only [CollatzResearch.WordTrace]
  refine ⟨44746166145408173305347217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59661554860544231073796289 44746166145408173305347217)
  ·
    refine ⟨33559624609056129979010413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44746166145408173305347217 33559624609056129979010413)
    ·
      refine ⟨12584859228396048742128905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33559624609056129979010413 12584859228396048742128905)
      ·
        refine ⟨9438644421297036556596679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12584859228396048742128905 9438644421297036556596679)
        ·
          refine ⟨14157966631945554834895019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9438644421297036556596679 14157966631945554834895019)
          ·
            refine ⟨21236949947918332252342529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14157966631945554834895019 21236949947918332252342529)
            ·
              refine ⟨15927712460938749189256897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21236949947918332252342529 15927712460938749189256897)
              ·
                refine ⟨11945784345704061891942673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15927712460938749189256897 11945784345704061891942673)
                ·
                  refine ⟨8959338259278046418957005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11945784345704061891942673 8959338259278046418957005)
                  ·
                    refine ⟨3359751847229267407108877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8959338259278046418957005 3359751847229267407108877)
                    ·
                      refine ⟨1259906942710975277665829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3359751847229267407108877 1259906942710975277665829)
                      ·
                        rfl

theorem cell23_2453660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2453660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453660 prefixEnd_2453660 := by exact prefixLift 2453660
  have htrace : WordTrace (prefixWord ++ tailWord_2453660) baseStart_2453660 baseEnd_2453660 := by
    simpa [prefixWord, tailWord_2453660, baseEnd_2453660] using wordTrace_append hprefix tailTrace_2453660
  have hstable : (prefixWord ++ tailWord_2453660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453660).length < 2 ^ (prefixWord ++ tailWord_2453660).sum := by decide
  have hdescent : baseEnd_2453660 < baseStart_2453660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453677 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_2453677 : Nat := 118140960795 + 2453677 * 2 ^ 59
def prefixEnd_2453677 : Nat := 4983230072969 + 3 ^ 40 * 2453677 * 2
def baseEnd_2453677 : Nat := 1259915671882101711153251

theorem tailTrace_2453677 : CollatzResearch.WordTrace tailWord_2453677 prefixEnd_2453677 1259915671882101711153251 := by
  unfold tailWord_2453677
  simp only [CollatzResearch.WordTrace]
  refine ⟨89492952331754758514063285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59661968221169839009375523 89492952331754758514063285)
  ·
    refine ⟨8389964281102008610693433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89492952331754758514063285 8389964281102008610693433)
    ·
      refine ⟨6292473210826506458020075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8389964281102008610693433 6292473210826506458020075)
      ·
        refine ⟨9438709816239759687030113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6292473210826506458020075 9438709816239759687030113)
        ·
          refine ⟨7079032362179819765272585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9438709816239759687030113 7079032362179819765272585)
          ·
            refine ⟨5309274271634864823954439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7079032362179819765272585 5309274271634864823954439)
            ·
              refine ⟨7963911407452297235931659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5309274271634864823954439 7963911407452297235931659)
              ·
                refine ⟨11945867111178445853897489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7963911407452297235931659 11945867111178445853897489)
                ·
                  refine ⟨8959400333383834390423117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11945867111178445853897489 8959400333383834390423117)
                  ·
                    refine ⟨3359775125018937896408669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8959400333383834390423117 3359775125018937896408669)
                    ·
                      refine ⟨1259915671882101711153251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3359775125018937896408669 1259915671882101711153251)
                      ·
                        rfl

theorem cell23_2453677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_2453677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453677 prefixEnd_2453677 := by exact prefixLift 2453677
  have htrace : WordTrace (prefixWord ++ tailWord_2453677) baseStart_2453677 baseEnd_2453677 := by
    simpa [prefixWord, tailWord_2453677, baseEnd_2453677] using wordTrace_append hprefix tailTrace_2453677
  have hstable : (prefixWord ++ tailWord_2453677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453677).length < 2 ^ (prefixWord ++ tailWord_2453677).sum := by decide
  have hdescent : baseEnd_2453677 < baseStart_2453677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453683 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 4]
def baseStart_2453683 : Nat := 118140960795 + 2453683 * 2 ^ 59
def prefixEnd_2453683 : Nat := 4983230072969 + 3 ^ 40 * 2453683 * 2
def baseEnd_2453683 : Nat := 1259918752766028687678223

theorem tailTrace_2453683 : CollatzResearch.WordTrace tailWord_2453683 prefixEnd_2453683 1259918752766028687678223 := by
  unfold tailWord_2453683
  simp only [CollatzResearch.WordTrace]
  refine ⟨89493171169733021538781703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59662114113155347692521135 89493171169733021538781703)
  ·
    refine ⟨134239756754599532308172555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89493171169733021538781703 134239756754599532308172555)
    ·
      refine ⟨201359635131899298462258833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134239756754599532308172555 201359635131899298462258833)
      ·
        refine ⟨151019726348924473846694125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201359635131899298462258833 151019726348924473846694125)
        ·
          refine ⟨56632397380846677692510297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151019726348924473846694125 56632397380846677692510297)
          ·
            refine ⟨42474298035635008269382723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56632397380846677692510297 42474298035635008269382723)
            ·
              refine ⟨63711447053452512404074085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42474298035635008269382723 63711447053452512404074085)
              ·
                refine ⟨11945896322522346075763891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63711447053452512404074085 11945896322522346075763891)
                ·
                  refine ⟨17918844483783519113645837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11945896322522346075763891 17918844483783519113645837)
                  ·
                    refine ⟨6719566681418819667617189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17918844483783519113645837 6719566681418819667617189)
                    ·
                      refine ⟨1259918752766028687678223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6719566681418819667617189 1259918752766028687678223)
                      ·
                        rfl

theorem cell23_2453683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_2453683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453683 prefixEnd_2453683 := by exact prefixLift 2453683
  have htrace : WordTrace (prefixWord ++ tailWord_2453683) baseStart_2453683 baseEnd_2453683 := by
    simpa [prefixWord, tailWord_2453683, baseEnd_2453683] using wordTrace_append hprefix tailTrace_2453683
  have hstable : (prefixWord ++ tailWord_2453683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453683).length < 2 ^ (prefixWord ++ tailWord_2453683).sum := by decide
  have hdescent : baseEnd_2453683 < baseStart_2453683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453697 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2453697 : Nat := 118140960795 + 2453697 * 2 ^ 59
def prefixEnd_2453697 : Nat := 4983230072969 + 3 ^ 40 * 2453697 * 2
def baseEnd_2453697 : Nat := 419975313831730544301053

theorem tailTrace_2453697 : CollatzResearch.WordTrace tailWord_2453697 prefixEnd_2453697 419975313831730544301053 := by
  unfold tailWord_2453697
  simp only [CollatzResearch.WordTrace]
  refine ⟨89493681791682301929791345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59662454527788201286527563 89493681791682301929791345)
  ·
    refine ⟨67120261343761726447343509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89493681791682301929791345 67120261343761726447343509)
    ·
      refine ⟨3146262250488830927219227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67120261343761726447343509 3146262250488830927219227)
      ·
        refine ⟨4719393375733246390828841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3146262250488830927219227 4719393375733246390828841)
        ·
          refine ⟨3539545031799934793121631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4719393375733246390828841 3539545031799934793121631)
          ·
            refine ⟨5309317547699902189682447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3539545031799934793121631 5309317547699902189682447)
            ·
              refine ⟨7963976321549853284523671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5309317547699902189682447 7963976321549853284523671)
              ·
                refine ⟨11945964482324779926785507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7963976321549853284523671 11945964482324779926785507)
                ·
                  refine ⟨17918946723487169890178261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11945964482324779926785507 17918946723487169890178261)
                  ·
                    refine ⟨419975313831730544301053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17918946723487169890178261 419975313831730544301053)
                    ·
                      rfl

theorem cell23_2453697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2453697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453697 prefixEnd_2453697 := by exact prefixLift 2453697
  have htrace : WordTrace (prefixWord ++ tailWord_2453697) baseStart_2453697 baseEnd_2453697 := by
    simpa [prefixWord, tailWord_2453697, baseEnd_2453697] using wordTrace_append hprefix tailTrace_2453697
  have hstable : (prefixWord ++ tailWord_2453697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453697).length < 2 ^ (prefixWord ++ tailWord_2453697).sum := by decide
  have hdescent : baseEnd_2453697 < baseStart_2453697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453713 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_2453713 : Nat := 118140960795 + 2453713 * 2 ^ 59
def prefixEnd_2453713 : Nat := 4983230072969 + 3 ^ 40 * 2453713 * 2
def baseEnd_2453713 : Nat := 1259934157185663570303085

theorem tailTrace_2453713 : CollatzResearch.WordTrace tailWord_2453713 prefixEnd_2453713 1259934157185663570303085 := by
  unfold tailWord_2453713
  simp only [CollatzResearch.WordTrace]
  refine ⟨89494265359624336662373793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59662843573082891108249195 89494265359624336662373793)
  ·
    refine ⟨67120699019718252496780345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89494265359624336662373793 67120699019718252496780345)
    ·
      refine ⟨50340524264788689372585259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67120699019718252496780345 50340524264788689372585259)
      ·
        refine ⟨75510786397183034058877889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50340524264788689372585259 75510786397183034058877889)
        ·
          refine ⟨56633089797887275544158417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75510786397183034058877889 56633089797887275544158417)
          ·
            refine ⟨42474817348415456658118813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56633089797887275544158417 42474817348415456658118813)
            ·
              refine ⟨15928056505655796246794555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42474817348415456658118813 15928056505655796246794555)
              ·
                refine ⟨23892084758483694370191833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15928056505655796246794555 23892084758483694370191833)
                ·
                  refine ⟨17919063568862770777643875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23892084758483694370191833 17919063568862770777643875)
                  ·
                    refine ⟨26878595353294156166465813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17919063568862770777643875 26878595353294156166465813)
                    ·
                      refine ⟨1259934157185663570303085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26878595353294156166465813 1259934157185663570303085)
                      ·
                        rfl

theorem cell23_2453713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_2453713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453713 prefixEnd_2453713 := by exact prefixLift 2453713
  have htrace : WordTrace (prefixWord ++ tailWord_2453713) baseStart_2453713 baseEnd_2453713 := by
    simpa [prefixWord, tailWord_2453713, baseEnd_2453713] using wordTrace_append hprefix tailTrace_2453713
  have hstable : (prefixWord ++ tailWord_2453713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453713).length < 2 ^ (prefixWord ++ tailWord_2453713).sum := by decide
  have hdescent : baseEnd_2453713 < baseStart_2453713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453777 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 4, 3, 2]
def baseStart_2453777 : Nat := 118140960795 + 2453777 * 2 ^ 59
def prefixEnd_2453777 : Nat := 4983230072969 + 3 ^ 40 * 2453777 * 2
def baseEnd_2453777 : Nat := 1259967019947551319902791

theorem tailTrace_2453777 : CollatzResearch.WordTrace tailWord_2453777 prefixEnd_2453777 1259967019947551319902791 := by
  unfold tailWord_2453777
  simp only [CollatzResearch.WordTrace]
  refine ⟨89496599631392475592703585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59664399754261650395135723 89496599631392475592703585)
  ·
    refine ⟨67122449723544356694527689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89496599631392475592703585 67122449723544356694527689)
    ·
      refine ⟨50341837292658267520895767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67122449723544356694527689 50341837292658267520895767)
      ·
        refine ⟨75512755938987401281343651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50341837292658267520895767 75512755938987401281343651)
        ·
          refine ⟨113269133908481101922015477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75512755938987401281343651 113269133908481101922015477)
          ·
            refine ⟨10618981303920103305188951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113269133908481101922015477 10618981303920103305188951)
            ·
              refine ⟨15928471955880154957783427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10618981303920103305188951 15928471955880154957783427)
              ·
                refine ⟨23892707933820232436675141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15928471955880154957783427 23892707933820232436675141)
                ·
                  refine ⟨4479882737591293581876589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23892707933820232436675141 4479882737591293581876589)
                  ·
                    refine ⟨1679956026596735093203721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4479882737591293581876589 1679956026596735093203721)
                    ·
                      refine ⟨1259967019947551319902791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679956026596735093203721 1259967019947551319902791)
                      ·
                        rfl

theorem cell23_2453777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 3, 2].length) (baseStart_2453777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453777 prefixEnd_2453777 := by exact prefixLift 2453777
  have htrace : WordTrace (prefixWord ++ tailWord_2453777) baseStart_2453777 baseEnd_2453777 := by
    simpa [prefixWord, tailWord_2453777, baseEnd_2453777] using wordTrace_append hprefix tailTrace_2453777
  have hstable : (prefixWord ++ tailWord_2453777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453777).length < 2 ^ (prefixWord ++ tailWord_2453777).sum := by decide
  have hdescent : baseEnd_2453777 < baseStart_2453777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453807 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 4]
def baseStart_2453807 : Nat := 118140960795 + 2453807 * 2 ^ 59
def prefixEnd_2453807 : Nat := 4983230072969 + 3 ^ 40 * 2453807 * 2
def baseEnd_2453807 : Nat := 1259982424367186202527653

theorem tailTrace_2453807 : CollatzResearch.WordTrace tailWord_2453807 prefixEnd_2453807 1259982424367186202527653 := by
  unfold tailWord_2453807
  simp only [CollatzResearch.WordTrace]
  refine ⟨89497693821283790716295675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59665129214189193810863783 89497693821283790716295675)
  ·
    refine ⟨134246540731925686074443513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89497693821283790716295675 134246540731925686074443513)
    ·
      refine ⟨100684905548944264555832635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134246540731925686074443513 100684905548944264555832635)
      ·
        refine ⟨151027358323416396833748953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100684905548944264555832635 151027358323416396833748953)
        ·
          refine ⟨113270518742562297625311715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151027358323416396833748953 113270518742562297625311715)
          ·
            refine ⟨169905778113843446437967573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113270518742562297625311715 169905778113843446437967573)
            ·
              refine ⟨3982166674543205775889865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 169905778113843446437967573 3982166674543205775889865)
              ·
                refine ⟨2986625005907404331917399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3982166674543205775889865 2986625005907404331917399)
                ·
                  refine ⟨4479937508861106497876099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986625005907404331917399 4479937508861106497876099)
                  ·
                    refine ⟨6719906263291659746814149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4479937508861106497876099 6719906263291659746814149)
                    ·
                      refine ⟨1259982424367186202527653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6719906263291659746814149 1259982424367186202527653)
                      ·
                        rfl

theorem cell23_2453807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 4].length) (baseStart_2453807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453807 prefixEnd_2453807 := by exact prefixLift 2453807
  have htrace : WordTrace (prefixWord ++ tailWord_2453807) baseStart_2453807 baseEnd_2453807 := by
    simpa [prefixWord, tailWord_2453807, baseEnd_2453807] using wordTrace_append hprefix tailTrace_2453807
  have hstable : (prefixWord ++ tailWord_2453807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453807).length < 2 ^ (prefixWord ++ tailWord_2453807).sum := by decide
  have hdescent : baseEnd_2453807 < baseStart_2453807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453817 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 1, 6]
def baseStart_2453817 : Nat := 118140960795 + 2453817 * 2 ^ 59
def prefixEnd_2453817 : Nat := 4983230072969 + 3 ^ 40 * 2453817 * 2
def baseEnd_2453817 : Nat := 419995853057910387800869

theorem tailTrace_2453817 : CollatzResearch.WordTrace tailWord_2453817 prefixEnd_2453817 419995853057910387800869 := by
  unfold tailWord_2453817
  simp only [CollatzResearch.WordTrace]
  refine ⟨89498058551247562424159705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59665372367498374949439803 89498058551247562424159705)
  ·
    refine ⟨67123543913435671818119779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89498058551247562424159705 67123543913435671818119779)
    ·
      refine ⟨100685315870153507727179669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67123543913435671818119779 100685315870153507727179669)
      ·
        refine ⟨4719624181413445674711547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100685315870153507727179669 4719624181413445674711547)
        ·
          refine ⟨7079436272120168512067321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4719624181413445674711547 7079436272120168512067321)
          ·
            refine ⟨5309577204090126384050491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7079436272120168512067321 5309577204090126384050491)
            ·
              refine ⟨7964365806135189576075737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5309577204090126384050491 7964365806135189576075737)
              ·
                refine ⟨5973274354601392182056803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7964365806135189576075737 5973274354601392182056803)
                ·
                  refine ⟨8959911531902088273085205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5973274354601392182056803 8959911531902088273085205)
                  ·
                    refine ⟨419995853057910387800869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8959911531902088273085205 419995853057910387800869)
                    ·
                      rfl

theorem cell23_2453817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_2453817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453817 prefixEnd_2453817 := by exact prefixLift 2453817
  have htrace : WordTrace (prefixWord ++ tailWord_2453817) baseStart_2453817 baseEnd_2453817 := by
    simpa [prefixWord, tailWord_2453817, baseEnd_2453817] using wordTrace_append hprefix tailTrace_2453817
  have hstable : (prefixWord ++ tailWord_2453817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453817).length < 2 ^ (prefixWord ++ tailWord_2453817).sum := by decide
  have hdescent : baseEnd_2453817 < baseStart_2453817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453827 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 3]
def baseStart_2453827 : Nat := 118140960795 + 2453827 * 2 ^ 59
def prefixEnd_2453827 : Nat := 4983230072969 + 3 ^ 40 * 2453827 * 2
def baseEnd_2453827 : Nat := 1259992693980276124277561

theorem tailTrace_2453827 : CollatzResearch.WordTrace tailWord_2453827 prefixEnd_2453827 1259992693980276124277561 := by
  unfold tailWord_2453827
  simp only [CollatzResearch.WordTrace]
  refine ⟨89498423281211334132023735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59665615520807556088015823 89498423281211334132023735)
  ·
    refine ⟨134247634921817001198035603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89498423281211334132023735 134247634921817001198035603)
    ·
      refine ⟨201371452382725501797053405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134247634921817001198035603 201371452382725501797053405)
      ·
        refine ⟨75514294643522063173895027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201371452382725501797053405 75514294643522063173895027)
        ·
          refine ⟨113271441965283094760842541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75514294643522063173895027 113271441965283094760842541)
          ·
            refine ⟨42476790736981160535315953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113271441965283094760842541 42476790736981160535315953)
            ·
              refine ⟨31857593052735870401486965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42476790736981160535315953 31857593052735870401486965)
              ·
                refine ⟨2986649348693987850139403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31857593052735870401486965 2986649348693987850139403)
                ·
                  refine ⟨4479974023040981775209105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986649348693987850139403 4479974023040981775209105)
                  ·
                    refine ⟨3359980517280736331406829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4479974023040981775209105 3359980517280736331406829)
                    ·
                      refine ⟨1259992693980276124277561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3359980517280736331406829 1259992693980276124277561)
                      ·
                        rfl

theorem cell23_2453827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_2453827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453827 prefixEnd_2453827 := by exact prefixLift 2453827
  have htrace : WordTrace (prefixWord ++ tailWord_2453827) baseStart_2453827 baseEnd_2453827 := by
    simpa [prefixWord, tailWord_2453827, baseEnd_2453827] using wordTrace_append hprefix tailTrace_2453827
  have hstable : (prefixWord ++ tailWord_2453827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453827).length < 2 ^ (prefixWord ++ tailWord_2453827).sum := by decide
  have hdescent : baseEnd_2453827 < baseStart_2453827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453857 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_2453857 : Nat := 118140960795 + 2453857 * 2 ^ 59
def prefixEnd_2453857 : Nat := 4983230072969 + 3 ^ 40 * 2453857 * 2
def baseEnd_2453857 : Nat := 1260008098399911006902423

theorem tailTrace_2453857 : CollatzResearch.WordTrace tailWord_2453857 prefixEnd_2453857 1260008098399911006902423 := by
  unfold tailWord_2453857
  simp only [CollatzResearch.WordTrace]
  refine ⟨89499517471102649255615825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59666344980735099503743883 89499517471102649255615825)
  ·
    refine ⟨67124638103326986941711869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89499517471102649255615825 67124638103326986941711869)
    ·
      refine ⟨25171739288747620103141951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67124638103326986941711869 25171739288747620103141951)
      ·
        refine ⟨37757608933121430154712927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25171739288747620103141951 37757608933121430154712927)
        ·
          refine ⟨56636413399682145232069391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37757608933121430154712927 56636413399682145232069391)
          ·
            refine ⟨84954620099523217848104087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56636413399682145232069391 84954620099523217848104087)
            ·
              refine ⟨127431930149284826772156131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84954620099523217848104087 127431930149284826772156131)
              ·
                refine ⟨191147895223927240158234197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127431930149284826772156131 191147895223927240158234197)
                ·
                  refine ⟨2240014397155397345604307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 191147895223927240158234197 2240014397155397345604307)
                  ·
                    refine ⟨3360021595733096018406461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2240014397155397345604307 3360021595733096018406461)
                    ·
                      refine ⟨1260008098399911006902423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3360021595733096018406461 1260008098399911006902423)
                      ·
                        rfl

theorem cell23_2453857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_2453857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453857 prefixEnd_2453857 := by exact prefixLift 2453857
  have htrace : WordTrace (prefixWord ++ tailWord_2453857) baseStart_2453857 baseEnd_2453857 := by
    simpa [prefixWord, tailWord_2453857, baseEnd_2453857] using wordTrace_append hprefix tailTrace_2453857
  have hstable : (prefixWord ++ tailWord_2453857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453857).length < 2 ^ (prefixWord ++ tailWord_2453857).sum := by decide
  have hdescent : baseEnd_2453857 < baseStart_2453857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453860 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_2453860 : Nat := 118140960795 + 2453860 * 2 ^ 59
def prefixEnd_2453860 : Nat := 4983230072969 + 3 ^ 40 * 2453860 * 2
def baseEnd_2453860 : Nat := 420003212947291498388303

theorem tailTrace_2453860 : CollatzResearch.WordTrace tailWord_2453860 prefixEnd_2453860 420003212947291498388303 := by
  unfold tailWord_2453860
  simp only [CollatzResearch.WordTrace]
  refine ⟨44749813445045890383987517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59666417926727853845316689 44749813445045890383987517)
  ·
    refine ⟨16781180041892208893995319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44749813445045890383987517 16781180041892208893995319)
    ·
      refine ⟨25171770062838313340992979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16781180041892208893995319 25171770062838313340992979)
      ·
        refine ⟨37757655094257470011489469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25171770062838313340992979 37757655094257470011489469)
        ·
          refine ⟨14159120660346551254308551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37757655094257470011489469 14159120660346551254308551)
          ·
            refine ⟨21238680990519826881462827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14159120660346551254308551 21238680990519826881462827)
            ·
              refine ⟨31858021485779740322194241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21238680990519826881462827 31858021485779740322194241)
              ·
                refine ⟨23893516114334805241645681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31858021485779740322194241 23893516114334805241645681)
                ·
                  refine ⟨17920137085751103931234261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23893516114334805241645681 17920137085751103931234261)
                  ·
                    refine ⟨420003212947291498388303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17920137085751103931234261 420003212947291498388303)
                    ·
                      rfl

theorem cell23_2453860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_2453860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453860 prefixEnd_2453860 := by exact prefixLift 2453860
  have htrace : WordTrace (prefixWord ++ tailWord_2453860) baseStart_2453860 baseEnd_2453860 := by
    simpa [prefixWord, tailWord_2453860, baseEnd_2453860] using wordTrace_append hprefix tailTrace_2453860
  have hstable : (prefixWord ++ tailWord_2453860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453860).length < 2 ^ (prefixWord ++ tailWord_2453860).sum := by decide
  have hdescent : baseEnd_2453860 < baseStart_2453860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453878 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2453878 : Nat := 118140960795 + 2453878 * 2 ^ 59
def prefixEnd_2453878 : Nat := 4983230072969 + 3 ^ 40 * 2453878 * 2
def baseEnd_2453878 : Nat := 1260018881493655424739827

theorem tailTrace_2453878 : CollatzResearch.WordTrace tailWord_2453878 prefixEnd_2453878 1260018881493655424739827 := by
  unfold tailWord_2453878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5593767712751660615133143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59666855602684379894753525 5593767712751660615133143)
  ·
    refine ⟨8390651569127490922699715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5593767712751660615133143 8390651569127490922699715)
    ·
      refine ⟨12585977353691236384049573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8390651569127490922699715 12585977353691236384049573)
      ·
        refine ⟨2359870753817106822009295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12585977353691236384049573 2359870753817106822009295)
        ·
          refine ⟨3539806130725660233013943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359870753817106822009295 3539806130725660233013943)
          ·
            refine ⟨5309709196088490349520915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3539806130725660233013943 5309709196088490349520915)
            ·
              refine ⟨7964563794132735524281373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5309709196088490349520915 7964563794132735524281373)
              ·
                refine ⟨2986711422799775821605515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7964563794132735524281373 2986711422799775821605515)
                ·
                  refine ⟨4480067134199663732408273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986711422799775821605515 4480067134199663732408273)
                  ·
                    refine ⟨3360050350649747799306205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4480067134199663732408273 3360050350649747799306205)
                    ·
                      refine ⟨1260018881493655424739827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3360050350649747799306205 1260018881493655424739827)
                      ·
                        rfl

theorem cell23_2453878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2453878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453878 prefixEnd_2453878 := by exact prefixLift 2453878
  have htrace : WordTrace (prefixWord ++ tailWord_2453878) baseStart_2453878 baseEnd_2453878 := by
    simpa [prefixWord, tailWord_2453878, baseEnd_2453878] using wordTrace_append hprefix tailTrace_2453878
  have hstable : (prefixWord ++ tailWord_2453878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453878).length < 2 ^ (prefixWord ++ tailWord_2453878).sum := by decide
  have hdescent : baseEnd_2453878 < baseStart_2453878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453908 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_2453908 : Nat := 118140960795 + 2453908 * 2 ^ 59
def prefixEnd_2453908 : Nat := 4983230072969 + 3 ^ 40 * 2453908 * 2
def baseEnd_2453908 : Nat := 1260034285913290307364689

theorem tailTrace_2453908 : CollatzResearch.WordTrace tailWord_2453908 prefixEnd_2453908 1260034285913290307364689 := by
  unfold tailWord_2453908
  simp only [CollatzResearch.WordTrace]
  refine ⟨44750688796958942482861189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59667585062611923310481585 44750688796958942482861189)
  ·
    refine ⟨8390754149429801715536473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44750688796958942482861189 8390754149429801715536473)
    ·
      refine ⟨6293065612072351286652355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8390754149429801715536473 6293065612072351286652355)
      ·
        refine ⟨9439598418108526929978533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6293065612072351286652355 9439598418108526929978533)
        ·
          refine ⟨1769924703395348799370975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9439598418108526929978533 1769924703395348799370975)
          ·
            refine ⟨2654887055093023199056463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769924703395348799370975 2654887055093023199056463)
            ·
              refine ⟨3982330582639534798584695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654887055093023199056463 3982330582639534798584695)
              ·
                refine ⟨5973495873959302197877043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3982330582639534798584695 5973495873959302197877043)
                ·
                  refine ⟨8960243810938953296815565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5973495873959302197877043 8960243810938953296815565)
                  ·
                    refine ⟨3360091429102107486305837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8960243810938953296815565 3360091429102107486305837)
                    ·
                      refine ⟨1260034285913290307364689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3360091429102107486305837 1260034285913290307364689)
                      ·
                        rfl

theorem cell23_2453908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_2453908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453908 prefixEnd_2453908 := by exact prefixLift 2453908
  have htrace : WordTrace (prefixWord ++ tailWord_2453908) baseStart_2453908 baseEnd_2453908 := by
    simpa [prefixWord, tailWord_2453908, baseEnd_2453908] using wordTrace_append hprefix tailTrace_2453908
  have hstable : (prefixWord ++ tailWord_2453908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453908).length < 2 ^ (prefixWord ++ tailWord_2453908).sum := by decide
  have hdescent : baseEnd_2453908 < baseStart_2453908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453918 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_2453918 : Nat := 118140960795 + 2453918 * 2 ^ 59
def prefixEnd_2453918 : Nat := 4983230072969 + 3 ^ 40 * 2453918 * 2
def baseEnd_2453918 : Nat := 1260039420719835268239643

theorem tailTrace_2453918 : CollatzResearch.WordTrace tailWord_2453918 prefixEnd_2453918 1260039420719835268239643 := by
  unfold tailWord_2453918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11187717790485207084198301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59667828215921104449057605 11187717790485207084198301)
  ·
    refine ⟨4195394171431952656574363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11187717790485207084198301 4195394171431952656574363)
    ·
      refine ⟨6293091257147928984861545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4195394171431952656574363 6293091257147928984861545)
      ·
        refine ⟨4719818442860946738646159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6293091257147928984861545 4719818442860946738646159)
        ·
          refine ⟨7079727664291420107969239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4719818442860946738646159 7079727664291420107969239)
          ·
            refine ⟨10619591496437130161953859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7079727664291420107969239 10619591496437130161953859)
            ·
              refine ⟨15929387244655695242930789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10619591496437130161953859 15929387244655695242930789)
              ·
                refine ⟨2986760108372942858049523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15929387244655695242930789 2986760108372942858049523)
                ·
                  refine ⟨4480140162559414287074285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986760108372942858049523 4480140162559414287074285)
                  ·
                    refine ⟨1680052560959780357652857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4480140162559414287074285 1680052560959780357652857)
                    ·
                      refine ⟨1260039420719835268239643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680052560959780357652857 1260039420719835268239643)
                      ·
                        rfl

theorem cell23_2453918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_2453918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2453918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2453918 prefixEnd_2453918 := by exact prefixLift 2453918
  have htrace : WordTrace (prefixWord ++ tailWord_2453918) baseStart_2453918 baseEnd_2453918 := by
    simpa [prefixWord, tailWord_2453918, baseEnd_2453918] using wordTrace_append hprefix tailTrace_2453918
  have hstable : (prefixWord ++ tailWord_2453918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453918).length < 2 ^ (prefixWord ++ tailWord_2453918).sum := by decide
  have hdescent : baseEnd_2453918 < baseStart_2453918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454005 : List Nat := [1, 3, 5, 1, 2, 2, 2, 2, 5]
def baseStart_2454005 : Nat := 118140960795 + 2454005 * 2 ^ 59
def prefixEnd_2454005 : Nat := 4983230072969 + 3 ^ 40 * 2454005 * 2
def baseEnd_2454005 : Nat := 140009343726308491983527

theorem tailTrace_2454005 : CollatzResearch.WordTrace tailWord_2454005 prefixEnd_2454005 140009343726308491983527 := by
  unfold tailWord_2454005
  simp only [CollatzResearch.WordTrace]
  refine ⟨89504915474566470532003469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59669943649710980354668979 89504915474566470532003469)
  ·
    refine ⟨33564343302962426449501301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89504915474566470532003469 33564343302962426449501301)
    ·
      refine ⟨3146657184652727479640747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33564343302962426449501301 3146657184652727479640747)
      ·
        refine ⟨4719985776979091219461121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3146657184652727479640747 4719985776979091219461121)
        ·
          refine ⟨3539989332734318414595841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4719985776979091219461121 3539989332734318414595841)
          ·
            refine ⟨2654991999550738810946881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3539989332734318414595841 2654991999550738810946881)
            ·
              refine ⟨1991243999663054108210161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2654991999550738810946881 1991243999663054108210161)
              ·
                refine ⟨1493432999747290581157621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1991243999663054108210161 1493432999747290581157621)
                ·
                  refine ⟨140009343726308491983527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1493432999747290581157621 140009343726308491983527)
                  ·
                    rfl

theorem cell23_2454005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_2454005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454005 prefixEnd_2454005 := by exact prefixLift 2454005
  have htrace : WordTrace (prefixWord ++ tailWord_2454005) baseStart_2454005 baseEnd_2454005 := by
    simpa [prefixWord, tailWord_2454005, baseEnd_2454005] using wordTrace_append hprefix tailTrace_2454005
  have hstable : (prefixWord ++ tailWord_2454005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454005).length < 2 ^ (prefixWord ++ tailWord_2454005).sum := by decide
  have hdescent : baseEnd_2454005 < baseStart_2454005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454071 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 3, 1, 3]
def baseStart_2454071 : Nat := 118140960795 + 2454071 * 2 ^ 59
def prefixEnd_2454071 : Nat := 4983230072969 + 3 ^ 40 * 2454071 * 2
def baseEnd_2454071 : Nat := 1260117983259973169626439

theorem tailTrace_2454071 : CollatzResearch.WordTrace tailWord_2454071 prefixEnd_2454071 1260117983259973169626439 := by
  unfold tailWord_2454071
  simp only [CollatzResearch.WordTrace]
  refine ⟨89507322692327363803906067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59671548461551575869270711 89507322692327363803906067)
  ·
    refine ⟨134260984038491045705859101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89507322692327363803906067 134260984038491045705859101)
    ·
      refine ⟨50347869014434142139697163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134260984038491045705859101 50347869014434142139697163)
      ·
        refine ⟨75521803521651213209545745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50347869014434142139697163 75521803521651213209545745)
        ·
          refine ⟨56641352641238409907159309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75521803521651213209545745 56641352641238409907159309)
          ·
            refine ⟨21240507240464403715184741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56641352641238409907159309 21240507240464403715184741)
            ·
              refine ⟨3982595107587075696597139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21240507240464403715184741 3982595107587075696597139)
              ·
                refine ⟨5973892661380613544895709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3982595107587075696597139 5973892661380613544895709)
                ·
                  refine ⟨2240209748017730079335891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5973892661380613544895709 2240209748017730079335891)
                  ·
                    refine ⟨3360314622026595119003837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2240209748017730079335891 3360314622026595119003837)
                    ·
                      refine ⟨1260117983259973169626439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3360314622026595119003837 1260117983259973169626439)
                      ·
                        rfl

theorem cell23_2454071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_2454071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454071 prefixEnd_2454071 := by exact prefixLift 2454071
  have htrace : WordTrace (prefixWord ++ tailWord_2454071) baseStart_2454071 baseEnd_2454071 := by
    simpa [prefixWord, tailWord_2454071, baseEnd_2454071] using wordTrace_append hprefix tailTrace_2454071
  have hstable : (prefixWord ++ tailWord_2454071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454071).length < 2 ^ (prefixWord ++ tailWord_2454071).sum := by decide
  have hdescent : baseEnd_2454071 < baseStart_2454071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454081 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_2454081 : Nat := 118140960795 + 2454081 * 2 ^ 59
def prefixEnd_2454081 : Nat := 4983230072969 + 3 ^ 40 * 2454081 * 2
def baseEnd_2454081 : Nat := 1260123118066518130501393

theorem tailTrace_2454081 : CollatzResearch.WordTrace tailWord_2454081 prefixEnd_2454081 1260123118066518130501393 := by
  unfold tailWord_2454081
  simp only [CollatzResearch.WordTrace]
  refine ⟨89507687422291135511770097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59671791614860757007846731 89507687422291135511770097)
  ·
    refine ⟨67130765566718351633827573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89507687422291135511770097 67130765566718351633827573)
    ·
      refine ⟨6293509271879845465671335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67130765566718351633827573 6293509271879845465671335)
      ·
        refine ⟨9440263907819768198507003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6293509271879845465671335 9440263907819768198507003)
        ·
          refine ⟨14160395861729652297760505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9440263907819768198507003 14160395861729652297760505)
          ·
            refine ⟨10620296896297239223320379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14160395861729652297760505 10620296896297239223320379)
            ·
              refine ⟨15930445344445858834980569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10620296896297239223320379 15930445344445858834980569)
              ·
                refine ⟨11947834008334394126235427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15930445344445858834980569 11947834008334394126235427)
                ·
                  refine ⟨17921751012501591189353141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11947834008334394126235427 17921751012501591189353141)
                  ·
                    refine ⟨1680164157422024174001857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17921751012501591189353141 1680164157422024174001857)
                    ·
                      refine ⟨1260123118066518130501393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680164157422024174001857 1260123118066518130501393)
                      ·
                        rfl

theorem cell23_2454081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_2454081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454081 prefixEnd_2454081 := by exact prefixLift 2454081
  have htrace : WordTrace (prefixWord ++ tailWord_2454081) baseStart_2454081 baseEnd_2454081 := by
    simpa [prefixWord, tailWord_2454081, baseEnd_2454081] using wordTrace_append hprefix tailTrace_2454081
  have hstable : (prefixWord ++ tailWord_2454081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454081).length < 2 ^ (prefixWord ++ tailWord_2454081).sum := by decide
  have hdescent : baseEnd_2454081 < baseStart_2454081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454094 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_2454094 : Nat := 118140960795 + 2454094 * 2 ^ 59
def prefixEnd_2454094 : Nat := 4983230072969 + 3 ^ 40 * 2454094 * 2
def baseEnd_2454094 : Nat := 1260129793315026579638833

theorem tailTrace_2454094 : CollatzResearch.WordTrace tailWord_2454094 prefixEnd_2454094 1260129793315026579638833 := by
  unfold tailWord_2454094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11188520196405504841499167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59672107714162692487995557 11188520196405504841499167)
  ·
    refine ⟨16782780294608257262248751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11188520196405504841499167 16782780294608257262248751)
    ·
      refine ⟨25174170441912385893373127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16782780294608257262248751 25174170441912385893373127)
      ·
        refine ⟨37761255662868578840059691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25174170441912385893373127 37761255662868578840059691)
        ·
          refine ⟨56641883494302868260089537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37761255662868578840059691 56641883494302868260089537)
          ·
            refine ⟨42481412620727151195067153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56641883494302868260089537 42481412620727151195067153)
            ·
              refine ⟨31861059465545363396300365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42481412620727151195067153 31861059465545363396300365)
              ·
                refine ⟨11947897299579511273612637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31861059465545363396300365 11947897299579511273612637)
                ·
                  refine ⟨4480461487342316727604739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11947897299579511273612637 4480461487342316727604739)
                  ·
                    refine ⟨6720692231013475091407109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4480461487342316727604739 6720692231013475091407109)
                    ·
                      refine ⟨1260129793315026579638833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6720692231013475091407109 1260129793315026579638833)
                      ·
                        rfl

theorem cell23_2454094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_2454094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454094 prefixEnd_2454094 := by exact prefixLift 2454094
  have htrace : WordTrace (prefixWord ++ tailWord_2454094) baseStart_2454094 baseEnd_2454094 := by
    simpa [prefixWord, tailWord_2454094, baseEnd_2454094] using wordTrace_append hprefix tailTrace_2454094
  have hstable : (prefixWord ++ tailWord_2454094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454094).length < 2 ^ (prefixWord ++ tailWord_2454094).sum := by decide
  have hdescent : baseEnd_2454094 < baseStart_2454094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454104 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 4, 4]
def baseStart_2454104 : Nat := 118140960795 + 2454104 * 2 ^ 59
def prefixEnd_2454104 : Nat := 4983230072969 + 3 ^ 40 * 2454104 * 2
def baseEnd_2454104 : Nat := 420044976040523846837929

theorem tailTrace_2454104 : CollatzResearch.WordTrace tailWord_2454104 prefixEnd_2454104 420044976040523846837929 := by
  unfold tailWord_2454104
  simp only [CollatzResearch.WordTrace]
  refine ⟨44754263150603905219928683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59672350867471873626571577 44754263150603905219928683)
  ·
    refine ⟨67131394725905857829893025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44754263150603905219928683 67131394725905857829893025)
    ·
      refine ⟨50348546044429393372419769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67131394725905857829893025 50348546044429393372419769)
      ·
        refine ⟨37761409533322045029314827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50348546044429393372419769 37761409533322045029314827)
        ·
          refine ⟨56642114299983067543972241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37761409533322045029314827 56642114299983067543972241)
          ·
            refine ⟨42481585724987300657979181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56642114299983067543972241 42481585724987300657979181)
            ·
              refine ⟨15930594646870237746742193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42481585724987300657979181 15930594646870237746742193)
              ·
                refine ⟨11947945985152678310056645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15930594646870237746742193 11947945985152678310056645)
                ·
                  refine ⟨2240239872216127183135621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11947945985152678310056645 2240239872216127183135621)
                  ·
                    refine ⟨420044976040523846837929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2240239872216127183135621 420044976040523846837929)
                    ·
                      rfl

theorem cell23_2454104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_2454104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454104 prefixEnd_2454104 := by exact prefixLift 2454104
  have htrace : WordTrace (prefixWord ++ tailWord_2454104) baseStart_2454104 baseEnd_2454104 := by
    simpa [prefixWord, tailWord_2454104, baseEnd_2454104] using wordTrace_append hprefix tailTrace_2454104
  have hstable : (prefixWord ++ tailWord_2454104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454104).length < 2 ^ (prefixWord ++ tailWord_2454104).sum := by decide
  have hdescent : baseEnd_2454104 < baseStart_2454104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454111 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 5, 2, 2]
def baseStart_2454111 : Nat := 118140960795 + 2454111 * 2 ^ 59
def prefixEnd_2454111 : Nat := 4983230072969 + 3 ^ 40 * 2454111 * 2
def baseEnd_2454111 : Nat := 1260138522486153013126255

theorem tailTrace_2454111 : CollatzResearch.WordTrace tailWord_2454111 prefixEnd_2454111 1260138522486153013126255 := by
  unfold tailWord_2454111
  simp only [CollatzResearch.WordTrace]
  refine ⟨89508781612182450635362187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59672521074788300423574791 89508781612182450635362187)
  ·
    refine ⟨134263172418273675953043281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89508781612182450635362187 134263172418273675953043281)
    ·
      refine ⟨100697379313705256964782461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134263172418273675953043281 100697379313705256964782461)
      ·
        refine ⟨37761517242639471361793423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100697379313705256964782461 37761517242639471361793423)
        ·
          refine ⟨56642275863959207042690135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37761517242639471361793423 56642275863959207042690135)
          ·
            refine ⟨84963413795938810564035203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56642275863959207042690135 84963413795938810564035203)
            ·
              refine ⟨127445120693908215846052805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84963413795938810564035203 127445120693908215846052805)
              ·
                refine ⟨23895960130107790471134901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127445120693908215846052805 23895960130107790471134901)
                ·
                  refine ⟨2240246262197605356668897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23895960130107790471134901 2240246262197605356668897)
                  ·
                    refine ⟨1680184696648204017501673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2240246262197605356668897 1680184696648204017501673)
                    ·
                      refine ⟨1260138522486153013126255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680184696648204017501673 1260138522486153013126255)
                      ·
                        rfl

theorem cell23_2454111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_2454111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454111 prefixEnd_2454111 := by exact prefixLift 2454111
  have htrace : WordTrace (prefixWord ++ tailWord_2454111) baseStart_2454111 baseEnd_2454111 := by
    simpa [prefixWord, tailWord_2454111, baseEnd_2454111] using wordTrace_append hprefix tailTrace_2454111
  have hstable : (prefixWord ++ tailWord_2454111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454111).length < 2 ^ (prefixWord ++ tailWord_2454111).sum := by decide
  have hdescent : baseEnd_2454111 < baseStart_2454111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454148 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_2454148 : Nat := 118140960795 + 2454148 * 2 ^ 59
def prefixEnd_2454148 : Nat := 4983230072969 + 3 ^ 40 * 2454148 * 2
def baseEnd_2454148 : Nat := 1260157521270369368363585

theorem tailTrace_2454148 : CollatzResearch.WordTrace tailWord_2454148 prefixEnd_2454148 1260157521270369368363585 := by
  unfold tailWord_2454148
  simp only [CollatzResearch.WordTrace]
  refine ⟨44755065556524202977229549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59673420742032270636306065 44755065556524202977229549)
  ·
    refine ⟨16783149583696576116461081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44755065556524202977229549 16783149583696576116461081)
    ·
      refine ⟨12587362187772432087345811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16783149583696576116461081 12587362187772432087345811)
      ·
        refine ⟨18881043281658648131018717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12587362187772432087345811 18881043281658648131018717)
        ·
          refine ⟨7080391230621993049132019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18881043281658648131018717 7080391230621993049132019)
          ·
            refine ⟨10620586845932989573698029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080391230621993049132019 10620586845932989573698029)
            ·
              refine ⟨3982720067224871090136761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10620586845932989573698029 3982720067224871090136761)
              ·
                refine ⟨2987040050418653317602571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3982720067224871090136761 2987040050418653317602571)
                ·
                  refine ⟨4480560075627979976403857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2987040050418653317602571 4480560075627979976403857)
                  ·
                    refine ⟨3360420056720984982302893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4480560075627979976403857 3360420056720984982302893)
                    ·
                      refine ⟨1260157521270369368363585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3360420056720984982302893 1260157521270369368363585)
                      ·
                        rfl

theorem cell23_2454148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_2454148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454148 prefixEnd_2454148 := by exact prefixLift 2454148
  have htrace : WordTrace (prefixWord ++ tailWord_2454148) baseStart_2454148 baseEnd_2454148 := by
    simpa [prefixWord, tailWord_2454148, baseEnd_2454148] using wordTrace_append hprefix tailTrace_2454148
  have hstable : (prefixWord ++ tailWord_2454148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454148).length < 2 ^ (prefixWord ++ tailWord_2454148).sum := by decide
  have hdescent : baseEnd_2454148 < baseStart_2454148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454218 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2]
def baseStart_2454218 : Nat := 118140960795 + 2454218 * 2 ^ 59
def prefixEnd_2454218 : Nat := 4983230072969 + 3 ^ 40 * 2454218 * 2
def baseEnd_2454218 : Nat := 1260193464916184094488263

theorem tailTrace_2454218 : CollatzResearch.WordTrace tailWord_2454218 prefixEnd_2454218 1260193464916184094488263 := by
  unfold tailWord_2454218
  simp only [CollatzResearch.WordTrace]
  refine ⟨22378171055698701977376827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59675122815196538606338205 22378171055698701977376827)
  ·
    refine ⟨33567256583548052966065241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22378171055698701977376827 33567256583548052966065241)
    ·
      refine ⟨25175442437661039724548931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33567256583548052966065241 25175442437661039724548931)
      ·
        refine ⟨37763163656491559586823397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25175442437661039724548931 37763163656491559586823397)
        ·
          refine ⟨7080593185592167422529387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37763163656491559586823397 7080593185592167422529387)
          ·
            refine ⟨10620889778388251133794081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080593185592167422529387 10620889778388251133794081)
            ·
              refine ⟨7965667333791188350345561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10620889778388251133794081 7965667333791188350345561)
              ·
                refine ⟨5974250500343391262759171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7965667333791188350345561 5974250500343391262759171)
                ·
                  refine ⟨8961375750515086894138757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974250500343391262759171 8961375750515086894138757)
                  ·
                    refine ⟨1680257953221578792651017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8961375750515086894138757 1680257953221578792651017)
                    ·
                      refine ⟨1260193464916184094488263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680257953221578792651017 1260193464916184094488263)
                      ·
                        rfl

theorem cell23_2454218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_2454218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454218 prefixEnd_2454218 := by exact prefixLift 2454218
  have htrace : WordTrace (prefixWord ++ tailWord_2454218) baseStart_2454218 baseEnd_2454218 := by
    simpa [prefixWord, tailWord_2454218, baseEnd_2454218] using wordTrace_append hprefix tailTrace_2454218
  have hstable : (prefixWord ++ tailWord_2454218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454218).length < 2 ^ (prefixWord ++ tailWord_2454218).sum := by decide
  have hdescent : baseEnd_2454218 < baseStart_2454218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454222 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2]
def baseStart_2454222 : Nat := 118140960795 + 2454222 * 2 ^ 59
def prefixEnd_2454222 : Nat := 4983230072969 + 3 ^ 40 * 2454222 * 2
def baseEnd_2454222 : Nat := 1260195518838802078838245

theorem tailTrace_2454222 : CollatzResearch.WordTrace tailWord_2454222 prefixEnd_2454222 1260195518838802078838245 := by
  unfold tailWord_2454222
  simp only [CollatzResearch.WordTrace]
  refine ⟨11189103764347539574081615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59675220076520211061768613 11189103764347539574081615)
  ·
    refine ⟨16783655646521309361122423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11189103764347539574081615 16783655646521309361122423)
    ·
      refine ⟨25175483469781964041683635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16783655646521309361122423 25175483469781964041683635)
      ·
        refine ⟨37763225204672946062525453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25175483469781964041683635 37763225204672946062525453)
        ·
          refine ⟨14161209451752354773447045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37763225204672946062525453 14161209451752354773447045)
          ·
            refine ⟨2655226772203566520021321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14161209451752354773447045 2655226772203566520021321)
            ·
              refine ⟨1991420079152674890015991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2655226772203566520021321 1991420079152674890015991)
              ·
                refine ⟨2987130118729012335023987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1991420079152674890015991 2987130118729012335023987)
                ·
                  refine ⟨4480695178093518502535981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2987130118729012335023987 4480695178093518502535981)
                  ·
                    refine ⟨1680260691785069438450993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4480695178093518502535981 1680260691785069438450993)
                    ·
                      refine ⟨1260195518838802078838245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680260691785069438450993 1260195518838802078838245)
                      ·
                        rfl

theorem cell23_2454222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_2454222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454222 prefixEnd_2454222 := by exact prefixLift 2454222
  have htrace : WordTrace (prefixWord ++ tailWord_2454222) baseStart_2454222 baseEnd_2454222 := by
    simpa [prefixWord, tailWord_2454222, baseEnd_2454222] using wordTrace_append hprefix tailTrace_2454222
  have hstable : (prefixWord ++ tailWord_2454222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454222).length < 2 ^ (prefixWord ++ tailWord_2454222).sum := by decide
  have hdescent : baseEnd_2454222 < baseStart_2454222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454229 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2454229 : Nat := 118140960795 + 2454229 * 2 ^ 59
def prefixEnd_2454229 : Nat := 4983230072969 + 3 ^ 40 * 2454229 * 2
def baseEnd_2454229 : Nat := 1260199113203383551450713

theorem tailTrace_2454229 : CollatzResearch.WordTrace tailWord_2454229 prefixEnd_2454229 1260199113203383551450713 := by
  unfold tailWord_2454229
  simp only [CollatzResearch.WordTrace]
  refine ⟨89513085425754956788157741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59675390283836637858771827 89513085425754956788157741)
  ·
    refine ⟨33567407034658108795559153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89513085425754956788157741 33567407034658108795559153)
    ·
      refine ⟨25175555275993581596669365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33567407034658108795559153 25175555275993581596669365)
      ·
        refine ⟨2360208307124398274687753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25175555275993581596669365 2360208307124398274687753)
        ·
          refine ⟨1770156230343298706015815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2360208307124398274687753 1770156230343298706015815)
          ·
            refine ⟨2655234345514948059023723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770156230343298706015815 2655234345514948059023723)
            ·
              refine ⟨3982851518272422088535585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2655234345514948059023723 3982851518272422088535585)
              ·
                refine ⟨2987138638704316566401689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3982851518272422088535585 2987138638704316566401689)
                ·
                  refine ⟨2240353979028237424801267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2987138638704316566401689 2240353979028237424801267)
                  ·
                    refine ⟨3360530968542356137201901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2240353979028237424801267 3360530968542356137201901)
                    ·
                      refine ⟨1260199113203383551450713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3360530968542356137201901 1260199113203383551450713)
                      ·
                        rfl

theorem cell23_2454229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2454229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454229 prefixEnd_2454229 := by exact prefixLift 2454229
  have htrace : WordTrace (prefixWord ++ tailWord_2454229) baseStart_2454229 baseEnd_2454229 := by
    simpa [prefixWord, tailWord_2454229, baseEnd_2454229] using wordTrace_append hprefix tailTrace_2454229
  have hstable : (prefixWord ++ tailWord_2454229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454229).length < 2 ^ (prefixWord ++ tailWord_2454229).sum := by decide
  have hdescent : baseEnd_2454229 < baseStart_2454229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454241 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 7]
def baseStart_2454241 : Nat := 118140960795 + 2454241 * 2 ^ 59
def prefixEnd_2454241 : Nat := 4983230072969 + 3 ^ 40 * 2454241 * 2
def baseEnd_2454241 : Nat := 140022808330137500500073

theorem tailTrace_2454241 : CollatzResearch.WordTrace tailWord_2454241 prefixEnd_2454241 140022808330137500500073 := by
  unfold tailWord_2454241
  simp only [CollatzResearch.WordTrace]
  refine ⟨89513523101711482837594577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59675682067807655225063051 89513523101711482837594577)
  ·
    refine ⟨67135142326283612128195933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89513523101711482837594577 67135142326283612128195933)
    ·
      refine ⟨25175678372356354548073475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67135142326283612128195933 25175678372356354548073475)
      ·
        refine ⟨37763517558534531822110213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25175678372356354548073475 37763517558534531822110213)
        ·
          refine ⟨7080659542225224716645665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37763517558534531822110213 7080659542225224716645665)
          ·
            refine ⟨5310494656668918537484249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7080659542225224716645665 5310494656668918537484249)
            ·
              refine ⟨3982870992501688903113187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5310494656668918537484249 3982870992501688903113187)
              ·
                refine ⟨5974306488752533354669781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3982870992501688903113187 5974306488752533354669781)
                ·
                  refine ⟨140022808330137500500073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5974306488752533354669781 140022808330137500500073)
                  ·
                    rfl

theorem cell23_2454241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 7].length) (baseStart_2454241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454241 prefixEnd_2454241 := by exact prefixLift 2454241
  have htrace : WordTrace (prefixWord ++ tailWord_2454241) baseStart_2454241 baseEnd_2454241 := by
    simpa [prefixWord, tailWord_2454241, baseEnd_2454241] using wordTrace_append hprefix tailTrace_2454241
  have hstable : (prefixWord ++ tailWord_2454241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454241).length < 2 ^ (prefixWord ++ tailWord_2454241).sum := by decide
  have hdescent : baseEnd_2454241 < baseStart_2454241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454291 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 4]
def baseStart_2454291 : Nat := 118140960795 + 2454291 * 2 ^ 59
def prefixEnd_2454291 : Nat := 4983230072969 + 3 ^ 40 * 2454291 * 2
def baseEnd_2454291 : Nat := 1260230949003962308875427

theorem tailTrace_2454291 : CollatzResearch.WordTrace tailWord_2454291 prefixEnd_2454291 1260230949003962308875427 := by
  unfold tailWord_2454291
  simp only [CollatzResearch.WordTrace]
  refine ⟨89515346751530341376914727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59676897834353560917943151 89515346751530341376914727)
  ·
    refine ⟨134273020127295512065372091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89515346751530341376914727 134273020127295512065372091)
    ·
      refine ⟨201409530190943268098058137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134273020127295512065372091 201409530190943268098058137)
      ·
        refine ⟨151057147643207451073543603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201409530190943268098058137 151057147643207451073543603)
        ·
          refine ⟨226585721464811176610315405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151057147643207451073543603 226585721464811176610315405)
          ·
            refine ⟨84969645549304191228868277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226585721464811176610315405 84969645549304191228868277)
            ·
              refine ⟨7965904270247267927706401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84969645549304191228868277 7965904270247267927706401)
              ·
                refine ⟨5974428202685450945779801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7965904270247267927706401 5974428202685450945779801)
                ·
                  refine ⟨4480821152014088209334851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5974428202685450945779801 4480821152014088209334851)
                  ·
                    refine ⟨6721231728021132314002277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4480821152014088209334851 6721231728021132314002277)
                    ·
                      refine ⟨1260230949003962308875427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6721231728021132314002277 1260230949003962308875427)
                      ·
                        rfl

theorem cell23_2454291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_2454291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454291 prefixEnd_2454291 := by exact prefixLift 2454291
  have htrace : WordTrace (prefixWord ++ tailWord_2454291) baseStart_2454291 baseEnd_2454291 := by
    simpa [prefixWord, tailWord_2454291, baseEnd_2454291] using wordTrace_append hprefix tailTrace_2454291
  have hstable : (prefixWord ++ tailWord_2454291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454291).length < 2 ^ (prefixWord ++ tailWord_2454291).sum := by decide
  have hdescent : baseEnd_2454291 < baseStart_2454291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454328 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 2, 2, 3]
def baseStart_2454328 : Nat := 118140960795 + 2454328 * 2 ^ 59
def prefixEnd_2454328 : Nat := 4983230072969 + 3 ^ 40 * 2454328 * 2
def baseEnd_2454328 : Nat := 1260249947788178664112757

theorem tailTrace_2454328 : CollatzResearch.WordTrace tailWord_2454328 prefixEnd_2454328 1260249947788178664112757 := by
  unfold tailWord_2454328
  simp only [CollatzResearch.WordTrace]
  refine ⟨44758348126198148348005819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59677797501597531130674425 44758348126198148348005819)
  ·
    refine ⟨67137522189297222522008729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44758348126198148348005819 67137522189297222522008729)
    ·
      refine ⟨50353141641972916891506547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67137522189297222522008729 50353141641972916891506547)
      ·
        refine ⟨75529712462959375337259821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50353141641972916891506547 75529712462959375337259821)
        ·
          refine ⟨28323642173609765751472433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75529712462959375337259821 28323642173609765751472433)
          ·
            refine ⟨21242731630207324313604325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28323642173609765751472433 21242731630207324313604325)
            ·
              refine ⟨3983012180663873308800811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21242731630207324313604325 3983012180663873308800811)
              ·
                refine ⟨5974518270995809963201217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983012180663873308800811 5974518270995809963201217)
                ·
                  refine ⟨4480888703246857472400913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5974518270995809963201217 4480888703246857472400913)
                  ·
                    refine ⟨3360666527435143104300685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4480888703246857472400913 3360666527435143104300685)
                    ·
                      refine ⟨1260249947788178664112757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3360666527435143104300685 1260249947788178664112757)
                      ·
                        rfl

theorem cell23_2454328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_2454328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454328 prefixEnd_2454328 := by exact prefixLift 2454328
  have htrace : WordTrace (prefixWord ++ tailWord_2454328) baseStart_2454328 baseEnd_2454328 := by
    simpa [prefixWord, tailWord_2454328, baseEnd_2454328] using wordTrace_append hprefix tailTrace_2454328
  have hstable : (prefixWord ++ tailWord_2454328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454328).length < 2 ^ (prefixWord ++ tailWord_2454328).sum := by decide
  have hdescent : baseEnd_2454328 < baseStart_2454328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454348 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 6]
def baseStart_2454348 : Nat := 118140960795 + 2454348 * 2 ^ 59
def prefixEnd_2454348 : Nat := 4983230072969 + 3 ^ 40 * 2454348 * 2
def baseEnd_2454348 : Nat := 140028913044585398429185

theorem tailTrace_2454348 : CollatzResearch.WordTrace tailWord_2454348 prefixEnd_2454348 140028913044585398429185 := by
  unfold tailWord_2454348
  simp only [CollatzResearch.WordTrace]
  refine ⟨44758712856161920055869849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59678283808215893407826465 44758712856161920055869849)
  ·
    refine ⟨33569034642121440041902387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44758712856161920055869849 33569034642121440041902387)
    ·
      refine ⟨50353551963182160062853581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33569034642121440041902387 50353551963182160062853581)
      ·
        refine ⟨18882581986193310023570093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50353551963182160062853581 18882581986193310023570093)
        ·
          refine ⟨7080968244822491258838785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18882581986193310023570093 7080968244822491258838785)
          ·
            refine ⟨5310726183616868444129089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7080968244822491258838785 5310726183616868444129089)
            ·
              refine ⟨3983044637712651333096817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5310726183616868444129089 3983044637712651333096817)
              ·
                refine ⟨2987283478284488499822613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3983044637712651333096817 2987283478284488499822613)
                ·
                  refine ⟨140028913044585398429185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2987283478284488499822613 140028913044585398429185)
                  ·
                    rfl

theorem cell23_2454348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_2454348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454348 prefixEnd_2454348 := by exact prefixLift 2454348
  have htrace : WordTrace (prefixWord ++ tailWord_2454348) baseStart_2454348 baseEnd_2454348 := by
    simpa [prefixWord, tailWord_2454348, baseEnd_2454348] using wordTrace_append hprefix tailTrace_2454348
  have hstable : (prefixWord ++ tailWord_2454348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454348).length < 2 ^ (prefixWord ++ tailWord_2454348).sum := by decide
  have hdescent : baseEnd_2454348 < baseStart_2454348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454361 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 3, 5]
def baseStart_2454361 : Nat := 118140960795 + 2454361 * 2 ^ 59
def prefixEnd_2454361 : Nat := 4983230072969 + 3 ^ 40 * 2454361 * 2
def baseEnd_2454361 : Nat := 420088964216592345000035

theorem tailTrace_2454361 : CollatzResearch.WordTrace tailWord_2454361 prefixEnd_2454361 420088964216592345000035 := by
  unfold tailWord_2454361
  simp only [CollatzResearch.WordTrace]
  refine ⟨89517899861276743331962937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59678599907517828887975291 89517899861276743331962937)
  ·
    refine ⟨67138424895957557498972203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89517899861276743331962937 67138424895957557498972203)
    ·
      refine ⟨100707637343936336248458305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67138424895957557498972203 100707637343936336248458305)
      ·
        refine ⟨75530728007952252186343729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100707637343936336248458305 75530728007952252186343729)
        ·
          refine ⟨56648046005964189139757797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75530728007952252186343729 56648046005964189139757797)
          ·
            refine ⟨10621508626118285463704587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56648046005964189139757797 10621508626118285463704587)
            ·
              refine ⟨15932262939177428195556881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10621508626118285463704587 15932262939177428195556881)
              ·
                refine ⟨11949197204383071146667661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15932262939177428195556881 11949197204383071146667661)
                ·
                  refine ⟨4480948951643651680000373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11949197204383071146667661 4480948951643651680000373)
                  ·
                    refine ⟨420088964216592345000035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4480948951643651680000373 420088964216592345000035)
                    ·
                      rfl

theorem cell23_2454361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_2454361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454361 prefixEnd_2454361 := by exact prefixLift 2454361
  have htrace : WordTrace (prefixWord ++ tailWord_2454361) baseStart_2454361 baseEnd_2454361 := by
    simpa [prefixWord, tailWord_2454361, baseEnd_2454361] using wordTrace_append hprefix tailTrace_2454361
  have hstable : (prefixWord ++ tailWord_2454361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454361).length < 2 ^ (prefixWord ++ tailWord_2454361).sum := by decide
  have hdescent : baseEnd_2454361 < baseStart_2454361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454368 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 1, 5, 2]
def baseStart_2454368 : Nat := 118140960795 + 2454368 * 2 ^ 59
def prefixEnd_2454368 : Nat := 4983230072969 + 3 ^ 40 * 2454368 * 2
def baseEnd_2454368 : Nat := 1260270487014358507612573

theorem tailTrace_2454368 : CollatzResearch.WordTrace tailWord_2454368 prefixEnd_2454368 1260270487014358507612573 := by
  unfold tailWord_2454368
  simp only [CollatzResearch.WordTrace]
  refine ⟨44759077586125691763733879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59678770114834255684978505 44759077586125691763733879)
  ·
    refine ⟨67138616379188537645600819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44759077586125691763733879 67138616379188537645600819)
    ·
      refine ⟨100707924568782806468401229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67138616379188537645600819 100707924568782806468401229)
      ·
        refine ⟨37765471713293552425650461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100707924568782806468401229 37765471713293552425650461)
        ·
          refine ⟨14162051892485082159618923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37765471713293552425650461 14162051892485082159618923)
          ·
            refine ⟨21243077838727623239428385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14162051892485082159618923 21243077838727623239428385)
            ·
              refine ⟨15932308379045717429571289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21243077838727623239428385 15932308379045717429571289)
              ·
                refine ⟨11949231284284288072178467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15932308379045717429571289 11949231284284288072178467)
                ·
                  refine ⟨17923846926426432108267701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11949231284284288072178467 17923846926426432108267701)
                  ·
                    refine ⟨1680360649352478010150097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17923846926426432108267701 1680360649352478010150097)
                    ·
                      refine ⟨1260270487014358507612573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680360649352478010150097 1260270487014358507612573)
                      ·
                        rfl

theorem cell23_2454368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_2454368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454368 prefixEnd_2454368 := by exact prefixLift 2454368
  have htrace : WordTrace (prefixWord ++ tailWord_2454368) baseStart_2454368 baseEnd_2454368 := by
    simpa [prefixWord, tailWord_2454368, baseEnd_2454368] using wordTrace_append hprefix tailTrace_2454368
  have hstable : (prefixWord ++ tailWord_2454368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454368).length < 2 ^ (prefixWord ++ tailWord_2454368).sum := by decide
  have hdescent : baseEnd_2454368 < baseStart_2454368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454375 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_2454375 : Nat := 118140960795 + 2454375 * 2 ^ 59
def prefixEnd_2454375 : Nat := 4983230072969 + 3 ^ 40 * 2454375 * 2
def baseEnd_2454375 : Nat := 1260274081378939980225041

theorem tailTrace_2454375 : CollatzResearch.WordTrace tailWord_2454375 prefixEnd_2454375 1260274081378939980225041 := by
  unfold tailWord_2454375
  simp only [CollatzResearch.WordTrace]
  refine ⟨89518410483226023722972579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59678940322150682481981719 89518410483226023722972579)
  ·
    refine ⟨134277615724839035584458869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89518410483226023722972579 134277615724839035584458869)
    ·
      refine ⟨12588526474203659586043019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134277615724839035584458869 12588526474203659586043019)
      ·
        refine ⟨18882789711305489379064529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12588526474203659586043019 18882789711305489379064529)
        ·
          refine ⟨14162092283479117034298397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18882789711305489379064529 14162092283479117034298397)
          ·
            refine ⟨5310784606304668887861899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14162092283479117034298397 5310784606304668887861899)
            ·
              refine ⟨7966176909457003331792849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5310784606304668887861899 7966176909457003331792849)
              ·
                refine ⟨5974632682092752498844637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7966176909457003331792849 5974632682092752498844637)
                ·
                  refine ⟨2240487255784782187066739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5974632682092752498844637 2240487255784782187066739)
                  ·
                    refine ⟨3360730883677173280600109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2240487255784782187066739 3360730883677173280600109)
                    ·
                      refine ⟨1260274081378939980225041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3360730883677173280600109 1260274081378939980225041)
                      ·
                        rfl

theorem cell23_2454375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_2454375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454375 prefixEnd_2454375 := by exact prefixLift 2454375
  have htrace : WordTrace (prefixWord ++ tailWord_2454375) baseStart_2454375 baseEnd_2454375 := by
    simpa [prefixWord, tailWord_2454375, baseEnd_2454375] using wordTrace_append hprefix tailTrace_2454375
  have hstable : (prefixWord ++ tailWord_2454375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454375).length < 2 ^ (prefixWord ++ tailWord_2454375).sum := by decide
  have hdescent : baseEnd_2454375 < baseStart_2454375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454385 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 2, 3, 2]
def baseStart_2454385 : Nat := 118140960795 + 2454385 * 2 ^ 59
def prefixEnd_2454385 : Nat := 4983230072969 + 3 ^ 40 * 2454385 * 2
def baseEnd_2454385 : Nat := 1260279216185484941099995

theorem tailTrace_2454385 : CollatzResearch.WordTrace tailWord_2454385 prefixEnd_2454385 1260279216185484941099995 := by
  unfold tailWord_2454385
  simp only [CollatzResearch.WordTrace]
  refine ⟨89518775213189795430836609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59679183475459863620557739 89518775213189795430836609)
  ·
    refine ⟨67139081409892346573127457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89518775213189795430836609 67139081409892346573127457)
    ·
      refine ⟨50354311057419259929845593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67139081409892346573127457 50354311057419259929845593)
      ·
        refine ⟨37765733293064444947384195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50354311057419259929845593 37765733293064444947384195)
        ·
          refine ⟨56648599939596667421076293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37765733293064444947384195 56648599939596667421076293)
          ·
            refine ⟨10621612488674375141451805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56648599939596667421076293 10621612488674375141451805)
            ·
              refine ⟨3983104683252890678044427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10621612488674375141451805 3983104683252890678044427)
              ·
                refine ⟨5974657024879336017066641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983104683252890678044427 5974657024879336017066641)
                ·
                  refine ⟨4480992768659502012799981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5974657024879336017066641 4480992768659502012799981)
                  ·
                    refine ⟨1680372288247313254799993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4480992768659502012799981 1680372288247313254799993)
                    ·
                      refine ⟨1260279216185484941099995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680372288247313254799993 1260279216185484941099995)
                      ·
                        rfl

theorem cell23_2454385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_2454385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454385 prefixEnd_2454385 := by exact prefixLift 2454385
  have htrace : WordTrace (prefixWord ++ tailWord_2454385) baseStart_2454385 baseEnd_2454385 := by
    simpa [prefixWord, tailWord_2454385, baseEnd_2454385] using wordTrace_append hprefix tailTrace_2454385
  have hstable : (prefixWord ++ tailWord_2454385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454385).length < 2 ^ (prefixWord ++ tailWord_2454385).sum := by decide
  have hdescent : baseEnd_2454385 < baseStart_2454385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454411 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 4]
def baseStart_2454411 : Nat := 118140960795 + 2454411 * 2 ^ 59
def prefixEnd_2454411 : Nat := 4983230072969 + 3 ^ 40 * 2454411 * 2
def baseEnd_2454411 : Nat := 1260292566682501839374875

theorem tailTrace_2454411 : CollatzResearch.WordTrace tailWord_2454411 prefixEnd_2454411 1260292566682501839374875 := by
  unfold tailWord_2454411
  simp only [CollatzResearch.WordTrace]
  refine ⟨89519723511095601871283087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59679815674063734580855391 89519723511095601871283087)
  ·
    refine ⟨134279585266643402806924631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89519723511095601871283087 134279585266643402806924631)
    ·
      refine ⟨201419377899965104210386947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134279585266643402806924631 201419377899965104210386947)
      ·
        refine ⟨302129066849947656315580421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201419377899965104210386947 302129066849947656315580421)
        ·
          refine ⟨56649200034365185559171329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302129066849947656315580421 56649200034365185559171329)
          ·
            refine ⟨42486900025773889169378497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56649200034365185559171329 42486900025773889169378497)
            ·
              refine ⟨31865175019330416877033873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42486900025773889169378497 31865175019330416877033873)
              ·
                refine ⟨23898881264497812657775405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31865175019330416877033873 23898881264497812657775405)
                ·
                  refine ⟨8962080474186679746665777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23898881264497812657775405 8962080474186679746665777)
                  ·
                    refine ⟨6721560355640009809999333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8962080474186679746665777 6721560355640009809999333)
                    ·
                      refine ⟨1260292566682501839374875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6721560355640009809999333 1260292566682501839374875)
                      ·
                        rfl

theorem cell23_2454411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 4].length) (baseStart_2454411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454411 prefixEnd_2454411 := by exact prefixLift 2454411
  have htrace : WordTrace (prefixWord ++ tailWord_2454411) baseStart_2454411 baseEnd_2454411 := by
    simpa [prefixWord, tailWord_2454411, baseEnd_2454411] using wordTrace_append hprefix tailTrace_2454411
  have hstable : (prefixWord ++ tailWord_2454411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454411).length < 2 ^ (prefixWord ++ tailWord_2454411).sum := by decide
  have hdescent : baseEnd_2454411 < baseStart_2454411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454452 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2454452 : Nat := 118140960795 + 2454452 * 2 ^ 59
def prefixEnd_2454452 : Nat := 4983230072969 + 3 ^ 40 * 2454452 * 2
def baseEnd_2454452 : Nat := 1260313619389336178962187

theorem tailTrace_2454452 : CollatzResearch.WordTrace tailWord_2454452 prefixEnd_2454452 1260313619389336178962187 := by
  unfold tailWord_2454452
  simp only [CollatzResearch.WordTrace]
  refine ⟨44760609451973532936762805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59680812602631377249017073 44760609451973532936762805)
  ·
    refine ⟨4196307136122518712821513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44760609451973532936762805 4196307136122518712821513)
    ·
      refine ⟨3147230352091889034616135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4196307136122518712821513 3147230352091889034616135)
      ·
        refine ⟨4720845528137833551924203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3147230352091889034616135 4720845528137833551924203)
        ·
          refine ⟨7081268292206750327886305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4720845528137833551924203 7081268292206750327886305)
          ·
            refine ⟨5310951219155062745914729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7081268292206750327886305 5310951219155062745914729)
            ·
              refine ⟨3983213414366297059436047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5310951219155062745914729 3983213414366297059436047)
              ·
                refine ⟨5974820121549445589154071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983213414366297059436047 5974820121549445589154071)
                ·
                  refine ⟨8962230182324168383731107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974820121549445589154071 8962230182324168383731107)
                  ·
                    refine ⟨13443345273486252575596661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8962230182324168383731107 13443345273486252575596661)
                    ·
                      refine ⟨1260313619389336178962187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13443345273486252575596661 1260313619389336178962187)
                      ·
                        rfl

theorem cell23_2454452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2454452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454452 prefixEnd_2454452 := by exact prefixLift 2454452
  have htrace : WordTrace (prefixWord ++ tailWord_2454452) baseStart_2454452 baseEnd_2454452 := by
    simpa [prefixWord, tailWord_2454452, baseEnd_2454452] using wordTrace_append hprefix tailTrace_2454452
  have hstable : (prefixWord ++ tailWord_2454452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454452).length < 2 ^ (prefixWord ++ tailWord_2454452).sum := by decide
  have hdescent : baseEnd_2454452 < baseStart_2454452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454481 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 1, 8]
def baseStart_2454481 : Nat := 118140960795 + 2454481 * 2 ^ 59
def prefixEnd_2454481 : Nat := 4983230072969 + 3 ^ 40 * 2454481 * 2
def baseEnd_2454481 : Nat := 420109503442772188499851

theorem tailTrace_2454481 : CollatzResearch.WordTrace tailWord_2454481 prefixEnd_2454481 420109503442772188499851 := by
  unfold tailWord_2454481
  simp only [CollatzResearch.WordTrace]
  refine ⟨89522276620842003826331297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59681517747228002550887531 89522276620842003826331297)
  ·
    refine ⟨67141707465631502869748473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89522276620842003826331297 67141707465631502869748473)
    ·
      refine ⟨50356280599223627152311355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67141707465631502869748473 50356280599223627152311355)
      ·
        refine ⟨75534420898835440728467033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50356280599223627152311355 75534420898835440728467033)
        ·
          refine ⟨56650815674126580546350275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75534420898835440728467033 56650815674126580546350275)
          ·
            refine ⟨84976223511189870819525413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56650815674126580546350275 84976223511189870819525413)
            ·
              refine ⟨15933041908348100778661015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84976223511189870819525413 15933041908348100778661015)
              ·
                refine ⟨23899562862522151167991523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15933041908348100778661015 23899562862522151167991523)
                ·
                  refine ⟨35849344293783226751987285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23899562862522151167991523 35849344293783226751987285)
                  ·
                    refine ⟨420109503442772188499851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35849344293783226751987285 420109503442772188499851)
                    ·
                      rfl

theorem cell23_2454481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_2454481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454481 prefixEnd_2454481 := by exact prefixLift 2454481
  have htrace : WordTrace (prefixWord ++ tailWord_2454481) baseStart_2454481 baseEnd_2454481 := by
    simpa [prefixWord, tailWord_2454481, baseEnd_2454481] using wordTrace_append hprefix tailTrace_2454481
  have hstable : (prefixWord ++ tailWord_2454481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454481).length < 2 ^ (prefixWord ++ tailWord_2454481).sum := by decide
  have hdescent : baseEnd_2454481 < baseStart_2454481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454517 : List Nat := [1, 3, 5, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2454517 : Nat := 118140960795 + 2454517 * 2 ^ 59
def prefixEnd_2454517 : Nat := 4983230072969 + 3 ^ 40 * 2454517 * 2
def baseEnd_2454517 : Nat := 1260346995631878424649389

theorem tailTrace_2454517 : CollatzResearch.WordTrace tailWord_2454517 prefixEnd_2454517 1260346995631878424649389 := by
  unfold tailWord_2454517
  simp only [CollatzResearch.WordTrace]
  refine ⟨89523589648711581974641805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59682393099141054649761203 89523589648711581974641805)
  ·
    refine ⟨33571346118266843240490677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89523589648711581974641805 33571346118266843240490677)
    ·
      refine ⟨3147313698587516553796001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33571346118266843240490677 3147313698587516553796001)
      ·
        refine ⟨2360485273940637415347001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3147313698587516553796001 2360485273940637415347001)
        ·
          refine ⟨1770363955455478061510251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2360485273940637415347001 1770363955455478061510251)
          ·
            refine ⟨2655545933183217092265377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770363955455478061510251 2655545933183217092265377)
            ·
              refine ⟨1991659449887412819199033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2655545933183217092265377 1991659449887412819199033)
              ·
                refine ⟨1493744587415559614399275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1991659449887412819199033 1493744587415559614399275)
                ·
                  refine ⟨2240616881123339421598913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493744587415559614399275 2240616881123339421598913)
                  ·
                    refine ⟨1680462660842504566199185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2240616881123339421598913 1680462660842504566199185)
                    ·
                      refine ⟨1260346995631878424649389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680462660842504566199185 1260346995631878424649389)
                      ·
                        rfl

theorem cell23_2454517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2454517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454517 prefixEnd_2454517 := by exact prefixLift 2454517
  have htrace : WordTrace (prefixWord ++ tailWord_2454517) baseStart_2454517 baseEnd_2454517 := by
    simpa [prefixWord, tailWord_2454517, baseEnd_2454517] using wordTrace_append hprefix tailTrace_2454517
  have hstable : (prefixWord ++ tailWord_2454517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454517).length < 2 ^ (prefixWord ++ tailWord_2454517).sum := by decide
  have hdescent : baseEnd_2454517 < baseStart_2454517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454531 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 8]
def baseStart_2454531 : Nat := 118140960795 + 2454531 * 2 ^ 59
def prefixEnd_2454531 : Nat := 4983230072969 + 3 ^ 40 * 2454531 * 2
def baseEnd_2454531 : Nat := 1260354184361041369874323

theorem tailTrace_2454531 : CollatzResearch.WordTrace tailWord_2454531 prefixEnd_2454531 1260354184361041369874323 := by
  unfold tailWord_2454531
  simp only [CollatzResearch.WordTrace]
  refine ⟨89524100270660862365651447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59682733513773908243767631 89524100270660862365651447)
  ·
    refine ⟨134286150405991293548477171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89524100270660862365651447 134286150405991293548477171)
    ·
      refine ⟨201429225608986940322715757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134286150405991293548477171 201429225608986940322715757)
      ·
        refine ⟨75535959603370102621018409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201429225608986940322715757 75535959603370102621018409)
        ·
          refine ⟨56651969702527576965763807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75535959603370102621018409 56651969702527576965763807)
          ·
            refine ⟨84977954553791365448645711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56651969702527576965763807 84977954553791365448645711)
            ·
              refine ⟨127466931830687048172968567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84977954553791365448645711 127466931830687048172968567)
              ·
                refine ⟨191200397746030572259452851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127466931830687048172968567 191200397746030572259452851)
                ·
                  refine ⟨286800596619045858389179277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191200397746030572259452851 286800596619045858389179277)
                  ·
                    refine ⟨107550223732142196895942229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286800596619045858389179277 107550223732142196895942229)
                    ·
                      refine ⟨1260354184361041369874323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 107550223732142196895942229 1260354184361041369874323)
                      ·
                        rfl

theorem cell23_2454531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_2454531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454531 prefixEnd_2454531 := by exact prefixLift 2454531
  have htrace : WordTrace (prefixWord ++ tailWord_2454531) baseStart_2454531 baseEnd_2454531 := by
    simpa [prefixWord, tailWord_2454531, baseEnd_2454531] using wordTrace_append hprefix tailTrace_2454531
  have hstable : (prefixWord ++ tailWord_2454531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454531).length < 2 ^ (prefixWord ++ tailWord_2454531).sum := by decide
  have hdescent : baseEnd_2454531 < baseStart_2454531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454562 : List Nat := [3, 3, 1, 1, 1, 4, 2, 3, 5]
def baseStart_2454562 : Nat := 118140960795 + 2454562 * 2 ^ 59
def prefixEnd_2454562 : Nat := 4983230072969 + 3 ^ 40 * 2454562 * 2
def baseEnd_2454562 : Nat := 140041122473481194287409

theorem tailTrace_2454562 : CollatzResearch.WordTrace tailWord_2454562 prefixEnd_2454562 140041122473481194287409 := by
  unfold tailWord_2454562
  simp only [CollatzResearch.WordTrace]
  refine ⟨22381307733387138665007485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59683487289032369773353293 22381307733387138665007485)
  ·
    refine ⟨8392990400020176999377807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22381307733387138665007485 8392990400020176999377807)
    ·
      refine ⟨12589485600030265499066711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8392990400020176999377807 12589485600030265499066711)
      ·
        refine ⟨18884228400045398248600067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12589485600030265499066711 18884228400045398248600067)
        ·
          refine ⟨28326342600068097372900101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18884228400045398248600067 28326342600068097372900101)
          ·
            refine ⟨5311189237512768257418769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28326342600068097372900101 5311189237512768257418769)
            ·
              refine ⟨3983391928134576193064077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5311189237512768257418769 3983391928134576193064077)
              ·
                refine ⟨1493771973050466072399029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3983391928134576193064077 1493771973050466072399029)
                ·
                  refine ⟨140041122473481194287409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1493771973050466072399029 140041122473481194287409)
                  ·
                    rfl

theorem cell23_2454562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_2454562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454562 prefixEnd_2454562 := by exact prefixLift 2454562
  have htrace : WordTrace (prefixWord ++ tailWord_2454562) baseStart_2454562 baseEnd_2454562 := by
    simpa [prefixWord, tailWord_2454562, baseEnd_2454562] using wordTrace_append hprefix tailTrace_2454562
  have hstable : (prefixWord ++ tailWord_2454562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454562).length < 2 ^ (prefixWord ++ tailWord_2454562).sum := by decide
  have hdescent : baseEnd_2454562 < baseStart_2454562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454595 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 2, 4, 2]
def baseStart_2454595 : Nat := 118140960795 + 2454595 * 2 ^ 59
def prefixEnd_2454595 : Nat := 4983230072969 + 3 ^ 40 * 2454595 * 2
def baseEnd_2454595 : Nat := 1260387047122929119474029

theorem tailTrace_2454595 : CollatzResearch.WordTrace tailWord_2454595 prefixEnd_2454595 1260387047122929119474029 := by
  unfold tailWord_2454595
  simp only [CollatzResearch.WordTrace]
  refine ⟨89526434542429001295981239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59684289694952667530654159 89526434542429001295981239)
  ·
    refine ⟨134289651813643501943971859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89526434542429001295981239 134289651813643501943971859)
    ·
      refine ⟨201434477720465252915957789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134289651813643501943971859 201434477720465252915957789)
      ·
        refine ⟨75537929145174469843484171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201434477720465252915957789 75537929145174469843484171)
        ·
          refine ⟨113306893717761704765226257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75537929145174469843484171 113306893717761704765226257)
          ·
            refine ⟨84980170288321278573919693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113306893717761704765226257 84980170288321278573919693)
            ·
              refine ⟨31867563858120479465219885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84980170288321278573919693 31867563858120479465219885)
              ·
                refine ⟨11950336446795179799457457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31867563858120479465219885 11950336446795179799457457)
                ·
                  refine ⟨8962752335096384849593093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11950336446795179799457457 8962752335096384849593093)
                  ·
                    refine ⟨1680516062830572159298705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8962752335096384849593093 1680516062830572159298705)
                    ·
                      refine ⟨1260387047122929119474029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680516062830572159298705 1260387047122929119474029)
                      ·
                        rfl

theorem cell23_2454595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 4, 2].length) (baseStart_2454595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454595 prefixEnd_2454595 := by exact prefixLift 2454595
  have htrace : WordTrace (prefixWord ++ tailWord_2454595) baseStart_2454595 baseEnd_2454595 := by
    simpa [prefixWord, tailWord_2454595, baseEnd_2454595] using wordTrace_append hprefix tailTrace_2454595
  have hstable : (prefixWord ++ tailWord_2454595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454595).length < 2 ^ (prefixWord ++ tailWord_2454595).sum := by decide
  have hdescent : baseEnd_2454595 < baseStart_2454595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454615 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 3]
def baseStart_2454615 : Nat := 118140960795 + 2454615 * 2 ^ 59
def prefixEnd_2454615 : Nat := 4983230072969 + 3 ^ 40 * 2454615 * 2
def baseEnd_2454615 : Nat := 1260397316736019041223937

theorem tailTrace_2454615 : CollatzResearch.WordTrace tailWord_2454615 prefixEnd_2454615 1260397316736019041223937 := by
  unfold tailWord_2454615
  simp only [CollatzResearch.WordTrace]
  refine ⟨89527164002356544711709299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59684776001571029807806199 89527164002356544711709299)
  ·
    refine ⟨134290746003534817067563949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89527164002356544711709299 134290746003534817067563949)
    ·
      refine ⟨50359029751325556400336481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134290746003534817067563949 50359029751325556400336481)
      ·
        refine ⟨37769272313494167300252361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50359029751325556400336481 37769272313494167300252361)
        ·
          refine ⟨28326954235120625475189271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37769272313494167300252361 28326954235120625475189271)
          ·
            refine ⟨42490431352680938212783907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28326954235120625475189271 42490431352680938212783907)
            ·
              refine ⟨63735647029021407319175861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42490431352680938212783907 63735647029021407319175861)
              ·
                refine ⟨5975216908970756936172737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63735647029021407319175861 5975216908970756936172737)
                ·
                  refine ⟨4481412681728067702129553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5975216908970756936172737 4481412681728067702129553)
                  ·
                    refine ⟨3361059511296050776597165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4481412681728067702129553 3361059511296050776597165)
                    ·
                      refine ⟨1260397316736019041223937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3361059511296050776597165 1260397316736019041223937)
                      ·
                        rfl

theorem cell23_2454615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_2454615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454615 prefixEnd_2454615 := by exact prefixLift 2454615
  have htrace : WordTrace (prefixWord ++ tailWord_2454615) baseStart_2454615 baseEnd_2454615 := by
    simpa [prefixWord, tailWord_2454615, baseEnd_2454615] using wordTrace_append hprefix tailTrace_2454615
  have hstable : (prefixWord ++ tailWord_2454615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454615).length < 2 ^ (prefixWord ++ tailWord_2454615).sum := by decide
  have hdescent : baseEnd_2454615 < baseStart_2454615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454639 : List Nat := [1, 1, 2, 1, 3, 3, 5, 2, 1, 4]
def baseStart_2454639 : Nat := 118140960795 + 2454639 * 2 ^ 59
def prefixEnd_2454639 : Nat := 4983230072969 + 3 ^ 40 * 2454639 * 2
def baseEnd_2454639 : Nat := 420136546757242315774609

theorem tailTrace_2454639 : CollatzResearch.WordTrace tailWord_2454639 prefixEnd_2454639 420136546757242315774609 := by
  unfold tailWord_2454639
  simp only [CollatzResearch.WordTrace]
  refine ⟨89528039354269596810582971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59685359569513064540388647 89528039354269596810582971)
  ·
    refine ⟨134292059031404395215874457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89528039354269596810582971 134292059031404395215874457)
    ·
      refine ⟨100719044273553296411905843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134292059031404395215874457 100719044273553296411905843)
      ·
        refine ⟨151078566410329944617858765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100719044273553296411905843 151078566410329944617858765)
        ·
          refine ⟨56654462403873729231697037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151078566410329944617858765 56654462403873729231697037)
          ·
            refine ⟨21245423401452648461886389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56654462403873729231697037 21245423401452648461886389)
            ·
              refine ⟨1991758443886185793301849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21245423401452648461886389 1991758443886185793301849)
              ·
                refine ⟨1493818832914639344976387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1991758443886185793301849 1493818832914639344976387)
                ·
                  refine ⟨2240728249371959017464581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493818832914639344976387 2240728249371959017464581)
                  ·
                    refine ⟨420136546757242315774609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2240728249371959017464581 420136546757242315774609)
                    ·
                      rfl

theorem cell23_2454639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 1, 4].length) (baseStart_2454639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454639 prefixEnd_2454639 := by exact prefixLift 2454639
  have htrace : WordTrace (prefixWord ++ tailWord_2454639) baseStart_2454639 baseEnd_2454639 := by
    simpa [prefixWord, tailWord_2454639, baseEnd_2454639] using wordTrace_append hprefix tailTrace_2454639
  have hstable : (prefixWord ++ tailWord_2454639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454639).length < 2 ^ (prefixWord ++ tailWord_2454639).sum := by decide
  have hdescent : baseEnd_2454639 < baseStart_2454639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454665 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 3, 5]
def baseStart_2454665 : Nat := 118140960795 + 2454665 * 2 ^ 59
def prefixEnd_2454665 : Nat := 4983230072969 + 3 ^ 40 * 2454665 * 2
def baseEnd_2454665 : Nat := 420140996922914615199569

theorem tailTrace_2454665 : CollatzResearch.WordTrace tailWord_2454665 prefixEnd_2454665 420140996922914615199569 := by
  unfold tailWord_2454665
  simp only [CollatzResearch.WordTrace]
  refine ⟨89528987652175403251029449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59685991768116935500686299 89528987652175403251029449)
  ·
    refine ⟨67146740739131552438272087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89528987652175403251029449 67146740739131552438272087)
    ·
      refine ⟨100720111108697328657408131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67146740739131552438272087 100720111108697328657408131)
      ·
        refine ⟨151080166663045992986112197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100720111108697328657408131 151080166663045992986112197)
        ·
          refine ⟨28327531249321123684896037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151080166663045992986112197 28327531249321123684896037)
          ·
            refine ⟨5311412109247710690918007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28327531249321123684896037 5311412109247710690918007)
            ·
              refine ⟨7967118163871566036377011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311412109247710690918007 7967118163871566036377011)
              ·
                refine ⟨11950677245807349054565517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7967118163871566036377011 11950677245807349054565517)
                ·
                  refine ⟨4481503967177755895462069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11950677245807349054565517 4481503967177755895462069)
                  ·
                    refine ⟨420140996922914615199569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4481503967177755895462069 420140996922914615199569)
                    ·
                      rfl

theorem cell23_2454665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_2454665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454665 prefixEnd_2454665 := by exact prefixLift 2454665
  have htrace : WordTrace (prefixWord ++ tailWord_2454665) baseStart_2454665 baseEnd_2454665 := by
    simpa [prefixWord, tailWord_2454665, baseEnd_2454665] using wordTrace_append hprefix tailTrace_2454665
  have hstable : (prefixWord ++ tailWord_2454665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454665).length < 2 ^ (prefixWord ++ tailWord_2454665).sum := by decide
  have hdescent : baseEnd_2454665 < baseStart_2454665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454690 : List Nat := [3, 3, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_2454690 : Nat := 118140960795 + 2454690 * 2 ^ 59
def prefixEnd_2454690 : Nat := 4983230072969 + 3 ^ 40 * 2454690 * 2
def baseEnd_2454690 : Nat := 420145275928368749262031

theorem tailTrace_2454690 : CollatzResearch.WordTrace tailWord_2454690 prefixEnd_2454690 420145275928368749262031 := by
  unfold tailWord_2454690
  simp only [CollatzResearch.WordTrace]
  refine ⟨22382474869271208130172381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59686599651389888347126349 22382474869271208130172381)
  ·
    refine ⟨8393428075976703048814643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22382474869271208130172381 8393428075976703048814643)
    ·
      refine ⟨12590142113965054573221965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8393428075976703048814643 12590142113965054573221965)
      ·
        refine ⟨4721303292736895464958237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12590142113965054573221965 4721303292736895464958237)
        ·
          refine ⟨1770488734776335799359339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4721303292736895464958237 1770488734776335799359339)
          ·
            refine ⟨2655733102164503699039009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770488734776335799359339 2655733102164503699039009)
            ·
              refine ⟨1991799826623377774279257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2655733102164503699039009 1991799826623377774279257)
              ·
                refine ⟨1493849869967533330709443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1991799826623377774279257 1493849869967533330709443)
                ·
                  refine ⟨2240774804951299996064165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493849869967533330709443 2240774804951299996064165)
                  ·
                    refine ⟨420145275928368749262031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2240774804951299996064165 420145275928368749262031)
                    ·
                      rfl

theorem cell23_2454690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_2454690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454690 prefixEnd_2454690 := by exact prefixLift 2454690
  have htrace : WordTrace (prefixWord ++ tailWord_2454690) baseStart_2454690 baseEnd_2454690 := by
    simpa [prefixWord, tailWord_2454690, baseEnd_2454690] using wordTrace_append hprefix tailTrace_2454690
  have hstable : (prefixWord ++ tailWord_2454690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454690).length < 2 ^ (prefixWord ++ tailWord_2454690).sum := by decide
  have hdescent : baseEnd_2454690 < baseStart_2454690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454735 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 3]
def baseStart_2454735 : Nat := 118140960795 + 2454735 * 2 ^ 59
def prefixEnd_2454735 : Nat := 4983230072969 + 3 ^ 40 * 2454735 * 2
def baseEnd_2454735 : Nat := 1260458934414558571723385

theorem tailTrace_2454735 : CollatzResearch.WordTrace tailWord_2454735 prefixEnd_2454735 1260458934414558571723385 := by
  unfold tailWord_2454735
  simp only [CollatzResearch.WordTrace]
  refine ⟨89531540761921805206077659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59687693841281203470718439 89531540761921805206077659)
  ·
    refine ⟨134297311142882707809116489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89531540761921805206077659 134297311142882707809116489)
    ·
      refine ⟨100722983357162030856837367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134297311142882707809116489 100722983357162030856837367)
      ·
        refine ⟨151084475035743046285256051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100722983357162030856837367 151084475035743046285256051)
        ·
          refine ⟨226626712553614569427884077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151084475035743046285256051 226626712553614569427884077)
          ·
            refine ⟨84985017207605463535456529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226626712553614569427884077 84985017207605463535456529)
            ·
              refine ⟨63738762905704097651592397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84985017207605463535456529 63738762905704097651592397)
              ·
                refine ⟨23902036089639036619347149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63738762905704097651592397 23902036089639036619347149)
                ·
                  refine ⟨8963263533614638732255181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23902036089639036619347149 8963263533614638732255181)
                  ·
                    refine ⟨3361223825105489524595693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8963263533614638732255181 3361223825105489524595693)
                    ·
                      refine ⟨1260458934414558571723385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3361223825105489524595693 1260458934414558571723385)
                      ·
                        rfl

theorem cell23_2454735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 3].length) (baseStart_2454735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454735 prefixEnd_2454735 := by exact prefixLift 2454735
  have htrace : WordTrace (prefixWord ++ tailWord_2454735) baseStart_2454735 baseEnd_2454735 := by
    simpa [prefixWord, tailWord_2454735, baseEnd_2454735] using wordTrace_append hprefix tailTrace_2454735
  have hstable : (prefixWord ++ tailWord_2454735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454735).length < 2 ^ (prefixWord ++ tailWord_2454735).sum := by decide
  have hdescent : baseEnd_2454735 < baseStart_2454735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454782 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2454782 : Nat := 118140960795 + 2454782 * 2 ^ 59
def prefixEnd_2454782 : Nat := 4983230072969 + 3 ^ 40 * 2454782 * 2
def baseEnd_2454782 : Nat := 1260483068005319887835669

theorem tailTrace_2454782 : CollatzResearch.WordTrace tailWord_2454782 prefixEnd_2454782 1260483068005319887835669 := by
  unfold tailWord_2454782
  simp only [CollatzResearch.WordTrace]
  refine ⟨11191656874093941529129825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59688836661834354822025733 11191656874093941529129825)
  ·
    refine ⟨8393742655570456146847369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11191656874093941529129825 8393742655570456146847369)
    ·
      refine ⟨6295306991677842110135527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8393742655570456146847369 6295306991677842110135527)
      ·
        refine ⟨9442960487516763165203291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6295306991677842110135527 9442960487516763165203291)
        ·
          refine ⟨14164440731275144747804937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9442960487516763165203291 14164440731275144747804937)
          ·
            refine ⟨10623330548456358560853703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14164440731275144747804937 10623330548456358560853703)
            ·
              refine ⟨15934995822684537841280555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10623330548456358560853703 15934995822684537841280555)
              ·
                refine ⟨23902493734026806761920833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15934995822684537841280555 23902493734026806761920833)
                ·
                  refine ⟨17926870300520105071440625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23902493734026806761920833 17926870300520105071440625)
                  ·
                    refine ⟨13445152725390078803580469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17926870300520105071440625 13445152725390078803580469)
                    ·
                      refine ⟨1260483068005319887835669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13445152725390078803580469 1260483068005319887835669)
                      ·
                        rfl

theorem cell23_2454782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2454782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454782 prefixEnd_2454782 := by exact prefixLift 2454782
  have htrace : WordTrace (prefixWord ++ tailWord_2454782) baseStart_2454782 baseEnd_2454782 := by
    simpa [prefixWord, tailWord_2454782, baseEnd_2454782] using wordTrace_append hprefix tailTrace_2454782
  have hstable : (prefixWord ++ tailWord_2454782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454782).length < 2 ^ (prefixWord ++ tailWord_2454782).sum := by decide
  have hdescent : baseEnd_2454782 < baseStart_2454782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454795 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 5]
def baseStart_2454795 : Nat := 118140960795 + 2454795 * 2 ^ 59
def prefixEnd_2454795 : Nat := 4983230072969 + 3 ^ 40 * 2454795 * 2
def baseEnd_2454795 : Nat := 1260489743253828336973109

theorem tailTrace_2454795 : CollatzResearch.WordTrace tailWord_2454795 prefixEnd_2454795 1260489743253828336973109 := by
  unfold tailWord_2454795
  simp only [CollatzResearch.WordTrace]
  refine ⟨89533729141704435453261839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59689152761136290302174559 89533729141704435453261839)
  ·
    refine ⟨134300593712556653179892759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89533729141704435453261839 134300593712556653179892759)
    ·
      refine ⟨201450890568834979769839139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134300593712556653179892759 201450890568834979769839139)
      ·
        refine ⟨302176335853252469654758709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201450890568834979769839139 302176335853252469654758709)
        ·
          refine ⟨28329031486242419030133629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 302176335853252469654758709 28329031486242419030133629)
          ·
            refine ⟨10623386807340907136300111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28329031486242419030133629 10623386807340907136300111)
            ·
              refine ⟨15935080211011360704450167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10623386807340907136300111 15935080211011360704450167)
              ·
                refine ⟨23902620316517041056675251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15935080211011360704450167 23902620316517041056675251)
                ·
                  refine ⟨35853930474775561585012877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23902620316517041056675251 35853930474775561585012877)
                  ·
                    refine ⟨13445223928040835594379829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35853930474775561585012877 13445223928040835594379829)
                    ·
                      refine ⟨1260489743253828336973109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13445223928040835594379829 1260489743253828336973109)
                      ·
                        rfl

theorem cell23_2454795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 5].length) (baseStart_2454795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454795 prefixEnd_2454795 := by exact prefixLift 2454795
  have htrace : WordTrace (prefixWord ++ tailWord_2454795) baseStart_2454795 baseEnd_2454795 := by
    simpa [prefixWord, tailWord_2454795, baseEnd_2454795] using wordTrace_append hprefix tailTrace_2454795
  have hstable : (prefixWord ++ tailWord_2454795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454795).length < 2 ^ (prefixWord ++ tailWord_2454795).sum := by decide
  have hdescent : baseEnd_2454795 < baseStart_2454795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454829 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2454829 : Nat := 118140960795 + 2454829 * 2 ^ 59
def prefixEnd_2454829 : Nat := 4983230072969 + 3 ^ 40 * 2454829 * 2
def baseEnd_2454829 : Nat := 1260507201596081203947953

theorem tailTrace_2454829 : CollatzResearch.WordTrace tailWord_2454829 prefixEnd_2454829 1260507201596081203947953 := by
  unfold tailWord_2454829
  simp only [CollatzResearch.WordTrace]
  refine ⟨89534969223581259259999541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59689979482387506173333027 89534969223581259259999541)
  ·
    refine ⟨8393903364710743055624957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89534969223581259259999541 8393903364710743055624957)
    ·
      refine ⟨3147713761766528645859359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8393903364710743055624957 3147713761766528645859359)
      ·
        refine ⟨4721570642649792968789039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3147713761766528645859359 4721570642649792968789039)
        ·
          refine ⟨7082355963974689453183559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721570642649792968789039 7082355963974689453183559)
          ·
            refine ⟨10623533945962034179775339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7082355963974689453183559 10623533945962034179775339)
            ·
              refine ⟨15935300918943051269663009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10623533945962034179775339 15935300918943051269663009)
              ·
                refine ⟨11951475689207288452247257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15935300918943051269663009 11951475689207288452247257)
                ·
                  refine ⟨8963606766905466339185443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11951475689207288452247257 8963606766905466339185443)
                  ·
                    refine ⟨13445410150358199508778165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8963606766905466339185443 13445410150358199508778165)
                    ·
                      refine ⟨1260507201596081203947953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13445410150358199508778165 1260507201596081203947953)
                      ·
                        rfl

theorem cell23_2454829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2454829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454829 prefixEnd_2454829 := by exact prefixLift 2454829
  have htrace : WordTrace (prefixWord ++ tailWord_2454829) baseStart_2454829 baseEnd_2454829 := by
    simpa [prefixWord, tailWord_2454829, baseEnd_2454829] using wordTrace_append hprefix tailTrace_2454829
  have hstable : (prefixWord ++ tailWord_2454829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454829).length < 2 ^ (prefixWord ++ tailWord_2454829).sum := by decide
  have hdescent : baseEnd_2454829 < baseStart_2454829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454862 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_2454862 : Nat := 118140960795 + 2454862 * 2 ^ 59
def prefixEnd_2454862 : Nat := 4983230072969 + 3 ^ 40 * 2454862 * 2
def baseEnd_2454862 : Nat := 420174715485893191611767

theorem tailTrace_2454862 : CollatzResearch.WordTrace tailWord_2454862 prefixEnd_2454862 420174715485893191611767 := by
  unfold tailWord_2454862
  simp only [CollatzResearch.WordTrace]
  refine ⟨11192021604057713236993855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59690781888307803930633893 11192021604057713236993855)
  ·
    refine ⟨16788032406086569855490783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11192021604057713236993855 16788032406086569855490783)
    ·
      refine ⟨25182048609129854783236175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16788032406086569855490783 25182048609129854783236175)
      ·
        refine ⟨37773072913694782174854263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25182048609129854783236175 37773072913694782174854263)
        ·
          refine ⟨56659609370542173262281395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37773072913694782174854263 56659609370542173262281395)
          ·
            refine ⟨84989414055813259893422093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56659609370542173262281395 84989414055813259893422093)
            ·
              refine ⟨31871030270929972460033285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84989414055813259893422093 31871030270929972460033285)
              ·
                refine ⟨5975818175799369836256241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31871030270929972460033285 5975818175799369836256241)
                ·
                  refine ⟨4481863631849527377192181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5975818175799369836256241 4481863631849527377192181)
                  ·
                    refine ⟨420174715485893191611767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4481863631849527377192181 420174715485893191611767)
                    ·
                      rfl

theorem cell23_2454862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_2454862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454862 prefixEnd_2454862 := by exact prefixLift 2454862
  have htrace : WordTrace (prefixWord ++ tailWord_2454862) baseStart_2454862 baseEnd_2454862 := by
    simpa [prefixWord, tailWord_2454862, baseEnd_2454862] using wordTrace_append hprefix tailTrace_2454862
  have hstable : (prefixWord ++ tailWord_2454862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454862).length < 2 ^ (prefixWord ++ tailWord_2454862).sum := by decide
  have hdescent : baseEnd_2454862 < baseStart_2454862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454869 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 2, 5, 2]
def baseStart_2454869 : Nat := 118140960795 + 2454869 * 2 ^ 59
def prefixEnd_2454869 : Nat := 4983230072969 + 3 ^ 40 * 2454869 * 2
def baseEnd_2454869 : Nat := 1260527740822261047447769

theorem tailTrace_2454869 : CollatzResearch.WordTrace tailWord_2454869 prefixEnd_2454869 1260527740822261047447769 := by
  unfold tailWord_2454869
  simp only [CollatzResearch.WordTrace]
  refine ⟨89536428143436346091455661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59690952095624230727637107 89536428143436346091455661)
  ·
    refine ⟨33576160553788629784295873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89536428143436346091455661 33576160553788629784295873)
    ·
      refine ⟨25182120415341472338221905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33576160553788629784295873 25182120415341472338221905)
      ·
        refine ⟨18886590311506104253666429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25182120415341472338221905 18886590311506104253666429)
        ·
          refine ⟨7082471366814789095124911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18886590311506104253666429 7082471366814789095124911)
          ·
            refine ⟨10623707050222183642687367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7082471366814789095124911 10623707050222183642687367)
            ·
              refine ⟨15935560575333275464031051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10623707050222183642687367 15935560575333275464031051)
              ·
                refine ⟨23903340862999913196046577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15935560575333275464031051 23903340862999913196046577)
                ·
                  refine ⟨17927505647249934897034933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23903340862999913196046577 17927505647249934897034933)
                  ·
                    refine ⟨1680703654429681396597025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17927505647249934897034933 1680703654429681396597025)
                    ·
                      refine ⟨1260527740822261047447769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680703654429681396597025 1260527740822261047447769)
                      ·
                        rfl

theorem cell23_2454869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_2454869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454869 prefixEnd_2454869 := by exact prefixLift 2454869
  have htrace : WordTrace (prefixWord ++ tailWord_2454869) baseStart_2454869 baseEnd_2454869 := by
    simpa [prefixWord, tailWord_2454869, baseEnd_2454869] using wordTrace_append hprefix tailTrace_2454869
  have hstable : (prefixWord ++ tailWord_2454869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454869).length < 2 ^ (prefixWord ++ tailWord_2454869).sum := by decide
  have hdescent : baseEnd_2454869 < baseStart_2454869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454949 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 5, 1, 3]
def baseStart_2454949 : Nat := 118140960795 + 2454949 * 2 ^ 59
def prefixEnd_2454949 : Nat := 4983230072969 + 3 ^ 40 * 2454949 * 2
def baseEnd_2454949 : Nat := 1260568819274620734447401

theorem tailTrace_2454949 : CollatzResearch.WordTrace tailWord_2454949 prefixEnd_2454949 1260568819274620734447401 := by
  unfold tailWord_2454949
  simp only [CollatzResearch.WordTrace]
  refine ⟨89539345983146519754367901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59692897322097679836245267 89539345983146519754367901)
  ·
    refine ⟨33577254743679944907887963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89539345983146519754367901 33577254743679944907887963)
    ·
      refine ⟨50365882115519917361831945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33577254743679944907887963 50365882115519917361831945)
      ·
        refine ⟨37774411586639938021373959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50365882115519917361831945 37774411586639938021373959)
        ·
          refine ⟨56661617379959907032060939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37774411586639938021373959 56661617379959907032060939)
          ·
            refine ⟨84992426069939860548091409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56661617379959907032060939 84992426069939860548091409)
            ·
              refine ⟨63744319552454895411068557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84992426069939860548091409 63744319552454895411068557)
              ·
                refine ⟨23904119832170585779150709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63744319552454895411068557 23904119832170585779150709)
                ·
                  refine ⟨2241011234265992416795379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23904119832170585779150709 2241011234265992416795379)
                  ·
                    refine ⟨3361516851398988625193069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2241011234265992416795379 3361516851398988625193069)
                    ·
                      refine ⟨1260568819274620734447401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3361516851398988625193069 1260568819274620734447401)
                      ·
                        rfl

theorem cell23_2454949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_2454949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454949 prefixEnd_2454949 := by exact prefixLift 2454949
  have htrace : WordTrace (prefixWord ++ tailWord_2454949) baseStart_2454949 baseEnd_2454949 := by
    simpa [prefixWord, tailWord_2454949, baseEnd_2454949] using wordTrace_append hprefix tailTrace_2454949
  have hstable : (prefixWord ++ tailWord_2454949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454949).length < 2 ^ (prefixWord ++ tailWord_2454949).sum := by decide
  have hdescent : baseEnd_2454949 < baseStart_2454949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454959 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 6, 3, 2]
def baseStart_2454959 : Nat := 118140960795 + 2454959 * 2 ^ 59
def prefixEnd_2454959 : Nat := 4983230072969 + 3 ^ 40 * 2454959 * 2
def baseEnd_2454959 : Nat := 1260573954081165695322355

theorem tailTrace_2454959 : CollatzResearch.WordTrace tailWord_2454959 prefixEnd_2454959 1260573954081165695322355 := by
  unfold tailWord_2454959
  simp only [CollatzResearch.WordTrace]
  refine ⟨89539710713110291462231931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59693140475406860974821287 89539710713110291462231931)
  ·
    refine ⟨134309566069665437193347897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89539710713110291462231931 134309566069665437193347897)
    ·
      refine ⟨100732174552249077895010923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134309566069665437193347897 100732174552249077895010923)
      ·
        refine ⟨151098261828373616842516385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100732174552249077895010923 151098261828373616842516385)
        ·
          refine ⟨113323696371280212631887289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151098261828373616842516385 113323696371280212631887289)
          ·
            refine ⟨84992772278460159473915467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113323696371280212631887289 84992772278460159473915467)
            ·
              refine ⟨127489158417690239210873201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84992772278460159473915467 127489158417690239210873201)
              ·
                refine ⟨95616868813267679408154901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127489158417690239210873201 95616868813267679408154901)
                ·
                  refine ⟨4482040725621922472257261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95616868813267679408154901 4482040725621922472257261)
                  ·
                    refine ⟨1680765272108220927096473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4482040725621922472257261 1680765272108220927096473)
                    ·
                      refine ⟨1260573954081165695322355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680765272108220927096473 1260573954081165695322355)
                      ·
                        rfl

theorem cell23_2454959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 3, 2].length) (baseStart_2454959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2454959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2454959 prefixEnd_2454959 := by exact prefixLift 2454959
  have htrace : WordTrace (prefixWord ++ tailWord_2454959) baseStart_2454959 baseEnd_2454959 := by
    simpa [prefixWord, tailWord_2454959, baseEnd_2454959] using wordTrace_append hprefix tailTrace_2454959
  have hstable : (prefixWord ++ tailWord_2454959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454959).length < 2 ^ (prefixWord ++ tailWord_2454959).sum := by decide
  have hdescent : baseEnd_2454959 < baseStart_2454959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455026 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2455026 : Nat := 118140960795 + 2455026 * 2 ^ 59
def prefixEnd_2455026 : Nat := 4983230072969 + 3 ^ 40 * 2455026 * 2
def baseEnd_2455026 : Nat := 1260608357285016933184547

theorem tailTrace_2455026 : CollatzResearch.WordTrace tailWord_2455026 prefixEnd_2455026 1260608357285016933184547 := by
  unfold tailWord_2455026
  simp only [CollatzResearch.WordTrace]
  refine ⟨22385538600966890476230233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59694769602578374603280621 22385538600966890476230233)
  ·
    refine ⟨16789153950725167857172675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22385538600966890476230233 16789153950725167857172675)
    ·
      refine ⟨25183730926087751785759013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16789153950725167857172675 25183730926087751785759013)
      ·
        refine ⟨4721949548641453459829815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25183730926087751785759013 4721949548641453459829815)
        ·
          refine ⟨7082924322962180189744723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721949548641453459829815 7082924322962180189744723)
          ·
            refine ⟨10624386484443270284617085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7082924322962180189744723 10624386484443270284617085)
            ·
              refine ⟨3984144931666226356731407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10624386484443270284617085 3984144931666226356731407)
              ·
                refine ⟨5976217397499339535097111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3984144931666226356731407 5976217397499339535097111)
                ·
                  refine ⟨8964326096249009302645667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5976217397499339535097111 8964326096249009302645667)
                  ·
                    refine ⟨13446489144373513953968501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8964326096249009302645667 13446489144373513953968501)
                    ·
                      refine ⟨1260608357285016933184547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13446489144373513953968501 1260608357285016933184547)
                      ·
                        rfl

theorem cell23_2455026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2455026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455026 prefixEnd_2455026 := by exact prefixLift 2455026
  have htrace : WordTrace (prefixWord ++ tailWord_2455026) baseStart_2455026 baseEnd_2455026 := by
    simpa [prefixWord, tailWord_2455026, baseEnd_2455026] using wordTrace_append hprefix tailTrace_2455026
  have hstable : (prefixWord ++ tailWord_2455026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455026).length < 2 ^ (prefixWord ++ tailWord_2455026).sum := by decide
  have hdescent : baseEnd_2455026 < baseStart_2455026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455029 : List Nat := [1, 3, 5, 1, 1, 12]
def baseStart_2455029 : Nat := 118140960795 + 2455029 * 2 ^ 59
def prefixEnd_2455029 : Nat := 4983230072969 + 3 ^ 40 * 2455029 * 2
def baseEnd_2455029 : Nat := 5187695052374405026531

theorem tailTrace_2455029 : CollatzResearch.WordTrace tailWord_2455029 prefixEnd_2455029 5187695052374405026531 := by
  unfold tailWord_2455029
  simp only [CollatzResearch.WordTrace]
  refine ⟨89542263822856693417280141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59694842548571128944853427 89542263822856693417280141)
  ·
    refine ⟨33578348933571260031480053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89542263822856693417280141 33578348933571260031480053)
    ·
      refine ⟨3147970212522305627951255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33578348933571260031480053 3147970212522305627951255)
      ·
        refine ⟨4721955318783458441926883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3147970212522305627951255 4721955318783458441926883)
        ·
          refine ⟨7082932978175187662890325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721955318783458441926883 7082932978175187662890325)
          ·
            refine ⟨5187695052374405026531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7082932978175187662890325 5187695052374405026531)
            ·
              rfl

theorem cell23_2455029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 12].length) (baseStart_2455029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455029 prefixEnd_2455029 := by exact prefixLift 2455029
  have htrace : WordTrace (prefixWord ++ tailWord_2455029) baseStart_2455029 baseEnd_2455029 := by
    simpa [prefixWord, tailWord_2455029, baseEnd_2455029] using wordTrace_append hprefix tailTrace_2455029
  have hstable : (prefixWord ++ tailWord_2455029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455029).length < 2 ^ (prefixWord ++ tailWord_2455029).sum := by decide
  have hdescent : baseEnd_2455029 < baseStart_2455029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455069 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2455069 : Nat := 118140960795 + 2455069 * 2 ^ 59
def prefixEnd_2455069 : Nat := 4983230072969 + 3 ^ 40 * 2455069 * 2
def baseEnd_2455069 : Nat := 1260630436953160264946849

theorem tailTrace_2455069 : CollatzResearch.WordTrace tailWord_2455069 prefixEnd_2455069 1260630436953160264946849 := by
  unfold tailWord_2455069
  simp only [CollatzResearch.WordTrace]
  refine ⟨89543722742711780248736261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59695815161807853499157507 89543722742711780248736261)
  ·
    refine ⟨16789448014258458796638049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89543722742711780248736261 16789448014258458796638049)
    ·
      refine ⟨12592086010693844097478537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16789448014258458796638049 12592086010693844097478537)
      ·
        refine ⟨9444064508020383073108903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12592086010693844097478537 9444064508020383073108903)
        ·
          refine ⟨14166096762030574609663355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9444064508020383073108903 14166096762030574609663355)
          ·
            refine ⟨21249145143045861914495033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14166096762030574609663355 21249145143045861914495033)
            ·
              refine ⟨15936858857284396435871275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21249145143045861914495033 15936858857284396435871275)
              ·
                refine ⟨23905288285926594653806913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15936858857284396435871275 23905288285926594653806913)
                ·
                  refine ⟨17928966214444945990355185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23905288285926594653806913 17928966214444945990355185)
                  ·
                    refine ⟨13446724660833709492766389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17928966214444945990355185 13446724660833709492766389)
                    ·
                      refine ⟨1260630436953160264946849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13446724660833709492766389 1260630436953160264946849)
                      ·
                        rfl

theorem cell23_2455069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2455069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455069 prefixEnd_2455069 := by exact prefixLift 2455069
  have htrace : WordTrace (prefixWord ++ tailWord_2455069) baseStart_2455069 baseEnd_2455069 := by
    simpa [prefixWord, tailWord_2455069, baseEnd_2455069] using wordTrace_append hprefix tailTrace_2455069
  have hstable : (prefixWord ++ tailWord_2455069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455069).length < 2 ^ (prefixWord ++ tailWord_2455069).sum := by decide
  have hdescent : baseEnd_2455069 < baseStart_2455069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455109 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_2455109 : Nat := 118140960795 + 2455109 * 2 ^ 59
def prefixEnd_2455109 : Nat := 4983230072969 + 3 ^ 40 * 2455109 * 2
def baseEnd_2455109 : Nat := 1260650976179340108446665

theorem tailTrace_2455109 : CollatzResearch.WordTrace tailWord_2455109 prefixEnd_2455109 1260650976179340108446665 := by
  unfold tailWord_2455109
  simp only [CollatzResearch.WordTrace]
  refine ⟨89545181662566867080192381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59696787775044578053461587 89545181662566867080192381)
  ·
    refine ⟨33579443123462575155072143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89545181662566867080192381 33579443123462575155072143)
    ·
      refine ⟨50369164685193862732608215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33579443123462575155072143 50369164685193862732608215)
      ·
        refine ⟨75553747027790794098912323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50369164685193862732608215 75553747027790794098912323)
        ·
          refine ⟨113330620541686191148368485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75553747027790794098912323 113330620541686191148368485)
          ·
            refine ⟨21249491351566160840319091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113330620541686191148368485 21249491351566160840319091)
            ·
              refine ⟨31874237027349241260478637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21249491351566160840319091 31874237027349241260478637)
              ·
                refine ⟨11952838885255965472679489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31874237027349241260478637 11952838885255965472679489)
                ·
                  refine ⟨8964629163941974104509617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11952838885255965472679489 8964629163941974104509617)
                  ·
                    refine ⟨6723471872956480578382213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8964629163941974104509617 6723471872956480578382213)
                    ·
                      refine ⟨1260650976179340108446665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6723471872956480578382213 1260650976179340108446665)
                      ·
                        rfl

theorem cell23_2455109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_2455109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455109 prefixEnd_2455109 := by exact prefixLift 2455109
  have htrace : WordTrace (prefixWord ++ tailWord_2455109) baseStart_2455109 baseEnd_2455109 := by
    simpa [prefixWord, tailWord_2455109, baseEnd_2455109] using wordTrace_append hprefix tailTrace_2455109
  have hstable : (prefixWord ++ tailWord_2455109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455109).length < 2 ^ (prefixWord ++ tailWord_2455109).sum := by decide
  have hdescent : baseEnd_2455109 < baseStart_2455109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455113 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 2, 2, 2]
def baseStart_2455113 : Nat := 118140960795 + 2455113 * 2 ^ 59
def prefixEnd_2455113 : Nat := 4983230072969 + 3 ^ 40 * 2455113 * 2
def baseEnd_2455113 : Nat := 1260653030101958092796647

theorem tailTrace_2455113 : CollatzResearch.WordTrace tailWord_2455113 prefixEnd_2455113 1260653030101958092796647 := by
  unfold tailWord_2455113
  simp only [CollatzResearch.WordTrace]
  refine ⟨89545327554552375763337993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59696885036368250508891995 89545327554552375763337993)
  ·
    refine ⟨67158995665914281822503495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89545327554552375763337993 67158995665914281822503495)
    ·
      refine ⟨100738493498871422733755243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67158995665914281822503495 100738493498871422733755243)
      ·
        refine ⟨151107740248307134100632865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100738493498871422733755243 151107740248307134100632865)
        ·
          refine ⟨113330805186230350575474649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151107740248307134100632865 113330805186230350575474649)
          ·
            refine ⟨84998103889672762931605987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113330805186230350575474649 84998103889672762931605987)
            ·
              refine ⟨127497155834509144397408981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84998103889672762931605987 127497155834509144397408981)
              ·
                refine ⟨2988214589871308071814273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 127497155834509144397408981 2988214589871308071814273)
                ·
                  refine ⟨2241160942403481053860705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2988214589871308071814273 2241160942403481053860705)
                  ·
                    refine ⟨1680870706802610790395529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2241160942403481053860705 1680870706802610790395529)
                    ·
                      refine ⟨1260653030101958092796647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680870706802610790395529 1260653030101958092796647)
                      ·
                        rfl

theorem cell23_2455113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 2, 2].length) (baseStart_2455113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455113 prefixEnd_2455113 := by exact prefixLift 2455113
  have htrace : WordTrace (prefixWord ++ tailWord_2455113) baseStart_2455113 baseEnd_2455113 := by
    simpa [prefixWord, tailWord_2455113, baseEnd_2455113] using wordTrace_append hprefix tailTrace_2455113
  have hstable : (prefixWord ++ tailWord_2455113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455113).length < 2 ^ (prefixWord ++ tailWord_2455113).sum := by decide
  have hdescent : baseEnd_2455113 < baseStart_2455113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455117 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_2455117 : Nat := 118140960795 + 2455117 * 2 ^ 59
def prefixEnd_2455117 : Nat := 4983230072969 + 3 ^ 40 * 2455117 * 2
def baseEnd_2455117 : Nat := 1260655084024576077146629

theorem tailTrace_2455117 : CollatzResearch.WordTrace tailWord_2455117 prefixEnd_2455117 1260655084024576077146629 := by
  unfold tailWord_2455117
  simp only [CollatzResearch.WordTrace]
  refine ⟨89545473446537884446483605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59696982297691922964322403 89545473446537884446483605)
  ·
    refine ⟨4197444067806463333428919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89545473446537884446483605 4197444067806463333428919)
    ·
      refine ⟨6296166101709695000143379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4197444067806463333428919 6296166101709695000143379)
      ·
        refine ⟨9444249152564542500215069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6296166101709695000143379 9444249152564542500215069)
        ·
          refine ⟨3541593432211703437580651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9444249152564542500215069 3541593432211703437580651)
          ·
            refine ⟨5312390148317555156370977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541593432211703437580651 5312390148317555156370977)
            ·
              refine ⟨3984292611238166367278233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5312390148317555156370977 3984292611238166367278233)
              ·
                refine ⟨2988219458428624775458675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3984292611238166367278233 2988219458428624775458675)
                ·
                  refine ⟨4482329187642937163188013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2988219458428624775458675 4482329187642937163188013)
                  ·
                    refine ⟨1680873445366101436195505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4482329187642937163188013 1680873445366101436195505)
                    ·
                      refine ⟨1260655084024576077146629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680873445366101436195505 1260655084024576077146629)
                      ·
                        rfl

theorem cell23_2455117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_2455117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455117 prefixEnd_2455117 := by exact prefixLift 2455117
  have htrace : WordTrace (prefixWord ++ tailWord_2455117) baseStart_2455117 baseEnd_2455117 := by
    simpa [prefixWord, tailWord_2455117, baseEnd_2455117] using wordTrace_append hprefix tailTrace_2455117
  have hstable : (prefixWord ++ tailWord_2455117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455117).length < 2 ^ (prefixWord ++ tailWord_2455117).sum := by decide
  have hdescent : baseEnd_2455117 < baseStart_2455117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455129 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 1, 5, 3]
def baseStart_2455129 : Nat := 118140960795 + 2455129 * 2 ^ 59
def prefixEnd_2455129 : Nat := 4983230072969 + 3 ^ 40 * 2455129 * 2
def baseEnd_2455129 : Nat := 1260661245792430030196573

theorem tailTrace_2455129 : CollatzResearch.WordTrace tailWord_2455129 prefixEnd_2455129 1260661245792430030196573 := by
  unfold tailWord_2455129
  simp only [CollatzResearch.WordTrace]
  refine ⟨89545911122494410495920441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59697274081662940330613627 89545911122494410495920441)
  ·
    refine ⟨67159433341870807871940331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89545911122494410495920441 67159433341870807871940331)
    ·
      refine ⟨100739150012806211807910497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67159433341870807871940331 100739150012806211807910497)
      ·
        refine ⟨75554362509604658855932873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100739150012806211807910497 75554362509604658855932873)
        ·
          refine ⟨56665771882203494141949655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75554362509604658855932873 56665771882203494141949655)
          ·
            refine ⟨84998657823305241212924483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56665771882203494141949655 84998657823305241212924483)
            ·
              refine ⟨127497986734957861819386725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84998657823305241212924483 127497986734957861819386725)
              ·
                refine ⟨23905872512804599091135011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127497986734957861819386725 23905872512804599091135011)
                ·
                  refine ⟨35858808769206898636702517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23905872512804599091135011 35858808769206898636702517)
                  ·
                    refine ⟨3361763322113146747190861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35858808769206898636702517 3361763322113146747190861)
                    ·
                      refine ⟨1260661245792430030196573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3361763322113146747190861 1260661245792430030196573)
                      ·
                        rfl

theorem cell23_2455129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_2455129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455129 prefixEnd_2455129 := by exact prefixLift 2455129
  have htrace : WordTrace (prefixWord ++ tailWord_2455129) baseStart_2455129 baseEnd_2455129 := by
    simpa [prefixWord, tailWord_2455129, baseEnd_2455129] using wordTrace_append hprefix tailTrace_2455129
  have hstable : (prefixWord ++ tailWord_2455129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455129).length < 2 ^ (prefixWord ++ tailWord_2455129).sum := by decide
  have hdescent : baseEnd_2455129 < baseStart_2455129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455213 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2455213 : Nat := 118140960795 + 2455213 * 2 ^ 59
def prefixEnd_2455213 : Nat := 4983230072969 + 3 ^ 40 * 2455213 * 2
def baseEnd_2455213 : Nat := 420234792722469233848729

theorem tailTrace_2455213 : CollatzResearch.WordTrace tailWord_2455213 prefixEnd_2455213 420234792722469233848729 := by
  unfold tailWord_2455213
  simp only [CollatzResearch.WordTrace]
  refine ⟨89548974854190092841978293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59699316569460061894652195 89548974854190092841978293)
  ·
    refine ⟨8395216392580321203935465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89548974854190092841978293 8395216392580321203935465)
    ·
      refine ⟨6296412294435240902951599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8395216392580321203935465 6296412294435240902951599)
      ·
        refine ⟨9444618441652861354427399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6296412294435240902951599 9444618441652861354427399)
        ·
          refine ⟨14166927662479292031641099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9444618441652861354427399 14166927662479292031641099)
          ·
            refine ⟨21250391493718938047461649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14166927662479292031641099 21250391493718938047461649)
            ·
              refine ⟨15937793620289203535596237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21250391493718938047461649 15937793620289203535596237)
              ·
                refine ⟨5976672607608451325848589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15937793620289203535596237 5976672607608451325848589)
                ·
                  refine ⟨2241252227853169247193221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5976672607608451325848589 2241252227853169247193221)
                  ·
                    refine ⟨420234792722469233848729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2241252227853169247193221 420234792722469233848729)
                    ·
                      rfl

theorem cell23_2455213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2455213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455213 prefixEnd_2455213 := by exact prefixLift 2455213
  have htrace : WordTrace (prefixWord ++ tailWord_2455213) baseStart_2455213 baseEnd_2455213 := by
    simpa [prefixWord, tailWord_2455213, baseEnd_2455213] using wordTrace_append hprefix tailTrace_2455213
  have hstable : (prefixWord ++ tailWord_2455213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455213).length < 2 ^ (prefixWord ++ tailWord_2455213).sum := by decide
  have hdescent : baseEnd_2455213 < baseStart_2455213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455226 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 6]
def baseStart_2455226 : Nat := 118140960795 + 2455226 * 2 ^ 59
def prefixEnd_2455226 : Nat := 4983230072969 + 3 ^ 40 * 2455226 * 2
def baseEnd_2455226 : Nat := 140079005935101794520403

theorem tailTrace_2455226 : CollatzResearch.WordTrace tailWord_2455226 prefixEnd_2455226 140079005935101794520403 := by
  unfold tailWord_2455226
  simp only [CollatzResearch.WordTrace]
  refine ⟨22387362250785749015550383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59699632668761997374801021 22387362250785749015550383)
  ·
    refine ⟨33581043376178623523325575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22387362250785749015550383 33581043376178623523325575)
    ·
      refine ⟨50371565064267935284988363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33581043376178623523325575 50371565064267935284988363)
      ·
        refine ⟨75557347596401902927482545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50371565064267935284988363 75557347596401902927482545)
        ·
          refine ⟨56668010697301427195611909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75557347596401902927482545 56668010697301427195611909)
          ·
            refine ⟨10625252005744017599177233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56668010697301427195611909 10625252005744017599177233)
            ·
              refine ⟨7968939004308013199382925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10625252005744017599177233 7968939004308013199382925)
              ·
                refine ⟨2988352126615504949768597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7968939004308013199382925 2988352126615504949768597)
                ·
                  refine ⟨140079005935101794520403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2988352126615504949768597 140079005935101794520403)
                  ·
                    rfl

theorem cell23_2455226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_2455226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455226 prefixEnd_2455226 := by exact prefixLift 2455226
  have htrace : WordTrace (prefixWord ++ tailWord_2455226) baseStart_2455226 baseEnd_2455226 := by
    simpa [prefixWord, tailWord_2455226, baseEnd_2455226] using wordTrace_append hprefix tailTrace_2455226
  have hstable : (prefixWord ++ tailWord_2455226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455226).length < 2 ^ (prefixWord ++ tailWord_2455226).sum := by decide
  have hdescent : baseEnd_2455226 < baseStart_2455226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455234 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2455234 : Nat := 118140960795 + 2455234 * 2 ^ 59
def prefixEnd_2455234 : Nat := 4983230072969 + 3 ^ 40 * 2455234 * 2
def baseEnd_2455234 : Nat := 420238387087050706461197

theorem tailTrace_2455234 : CollatzResearch.WordTrace tailWord_2455234 prefixEnd_2455234 420238387087050706461197 := by
  unfold tailWord_2455234
  simp only [CollatzResearch.WordTrace]
  refine ⟨22387435196778503357123189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59699827191409342285661837 22387435196778503357123189)
  ·
    refine ⟨2098822049697984689730299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22387435196778503357123189 2098822049697984689730299)
    ·
      refine ⟨3148233074546977034595449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2098822049697984689730299 3148233074546977034595449)
      ·
        refine ⟨2361174805910232775946587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3148233074546977034595449 2361174805910232775946587)
        ·
          refine ⟨3541762208865349163919881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361174805910232775946587 3541762208865349163919881)
          ·
            refine ⟨2656321656649011872939911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3541762208865349163919881 2656321656649011872939911)
            ·
              refine ⟨3984482484973517809409867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656321656649011872939911 3984482484973517809409867)
              ·
                refine ⟨5976723727460276714114801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3984482484973517809409867 5976723727460276714114801)
                ·
                  refine ⟨4482542795595207535586101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5976723727460276714114801 4482542795595207535586101)
                  ·
                    refine ⟨420238387087050706461197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4482542795595207535586101 420238387087050706461197)
                    ·
                      rfl

theorem cell23_2455234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2455234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455234 prefixEnd_2455234 := by exact prefixLift 2455234
  have htrace : WordTrace (prefixWord ++ tailWord_2455234) baseStart_2455234 baseEnd_2455234 := by
    simpa [prefixWord, tailWord_2455234, baseEnd_2455234] using wordTrace_append hprefix tailTrace_2455234
  have hstable : (prefixWord ++ tailWord_2455234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455234).length < 2 ^ (prefixWord ++ tailWord_2455234).sum := by decide
  have hdescent : baseEnd_2455234 < baseStart_2455234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455263 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 4, 3, 2]
def baseStart_2455263 : Nat := 118140960795 + 2455263 * 2 ^ 59
def prefixEnd_2455263 : Nat := 4983230072969 + 3 ^ 40 * 2455263 * 2
def baseEnd_2455263 : Nat := 1260730052200132505920957

theorem tailTrace_2455263 : CollatzResearch.WordTrace tailWord_2455263 prefixEnd_2455263 1260730052200132505920957 := by
  unfold tailWord_2455263
  simp only [CollatzResearch.WordTrace]
  refine ⟨89550798504008951381298443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59700532336005967587532295 89550798504008951381298443)
  ·
    refine ⟨134326197756013427071947665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89550798504008951381298443 134326197756013427071947665)
    ·
      refine ⟨100744648317010070303960749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134326197756013427071947665 100744648317010070303960749)
      ·
        refine ⟨37779243118878776363985281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100744648317010070303960749 37779243118878776363985281)
        ·
          refine ⟨28334432339159082272988961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37779243118878776363985281 28334432339159082272988961)
          ·
            refine ⟨21250824254369311704741721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28334432339159082272988961 21250824254369311704741721)
            ·
              refine ⟨15938118190776983778556291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21250824254369311704741721 15938118190776983778556291)
              ·
                refine ⟨23907177286165475667834437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15938118190776983778556291 23907177286165475667834437)
                ·
                  refine ⟨4482595741156026687718957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23907177286165475667834437 4482595741156026687718957)
                  ·
                    refine ⟨1680973402933510007894609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4482595741156026687718957 1680973402933510007894609)
                    ·
                      refine ⟨1260730052200132505920957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1680973402933510007894609 1260730052200132505920957)
                      ·
                        rfl

theorem cell23_2455263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_2455263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455263 prefixEnd_2455263 := by exact prefixLift 2455263
  have htrace : WordTrace (prefixWord ++ tailWord_2455263) baseStart_2455263 baseEnd_2455263 := by
    simpa [prefixWord, tailWord_2455263, baseEnd_2455263] using wordTrace_append hprefix tailTrace_2455263
  have hstable : (prefixWord ++ tailWord_2455263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455263).length < 2 ^ (prefixWord ++ tailWord_2455263).sum := by decide
  have hdescent : baseEnd_2455263 < baseStart_2455263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455276 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_2455276 : Nat := 118140960795 + 2455276 * 2 ^ 59
def prefixEnd_2455276 : Nat := 4983230072969 + 3 ^ 40 * 2455276 * 2
def baseEnd_2455276 : Nat := 1260736727448640955058397

theorem tailTrace_2455276 : CollatzResearch.WordTrace tailWord_2455276 prefixEnd_2455276 1260736727448640955058397 := by
  unfold tailWord_2455276
  simp only [CollatzResearch.WordTrace]
  refine ⟨44775636326480927300760841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59700848435307903067681121 44775636326480927300760841)
  ·
    refine ⟨33581727244860695475570631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44775636326480927300760841 33581727244860695475570631)
    ·
      refine ⟨50372590867291043213355947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33581727244860695475570631 50372590867291043213355947)
      ·
        refine ⟨75558886300936564820033921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50372590867291043213355947 75558886300936564820033921)
        ·
          refine ⟨56669164725702423615025441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75558886300936564820033921 56669164725702423615025441)
          ·
            refine ⟨42501873544276817711269081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56669164725702423615025441 42501873544276817711269081)
            ·
              refine ⟨31876405158207613283451811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42501873544276817711269081 31876405158207613283451811)
              ·
                refine ⟨47814607737311419925177717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31876405158207613283451811 47814607737311419925177717)
                ·
                  refine ⟨4482619475372945617985411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47814607737311419925177717 4482619475372945617985411)
                  ·
                    refine ⟨6723929213059418426978117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4482619475372945617985411 6723929213059418426978117)
                    ·
                      refine ⟨1260736727448640955058397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6723929213059418426978117 1260736727448640955058397)
                      ·
                        rfl

theorem cell23_2455276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_2455276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455276 prefixEnd_2455276 := by exact prefixLift 2455276
  have htrace : WordTrace (prefixWord ++ tailWord_2455276) baseStart_2455276 baseEnd_2455276 := by
    simpa [prefixWord, tailWord_2455276, baseEnd_2455276] using wordTrace_append hprefix tailTrace_2455276
  have hstable : (prefixWord ++ tailWord_2455276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455276).length < 2 ^ (prefixWord ++ tailWord_2455276).sum := by decide
  have hdescent : baseEnd_2455276 < baseStart_2455276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455310 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2]
def baseStart_2455310 : Nat := 118140960795 + 2455310 * 2 ^ 59
def prefixEnd_2455310 : Nat := 4983230072969 + 3 ^ 40 * 2455310 * 2
def baseEnd_2455310 : Nat := 1260754185790893822033241

theorem tailTrace_2455310 : CollatzResearch.WordTrace tailWord_2455310 prefixEnd_2455310 1260754185790893822033241 := by
  unfold tailWord_2455310
  simp only [CollatzResearch.WordTrace]
  refine ⟨11194064091854834801032423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59701675156559118938839589 11194064091854834801032423)
  ·
    refine ⟨16791096137782252201548635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11194064091854834801032423 16791096137782252201548635)
    ·
      refine ⟨25186644206673378302322953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16791096137782252201548635 25186644206673378302322953)
      ·
        refine ⟨18889983155005033726742215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25186644206673378302322953 18889983155005033726742215)
        ·
          refine ⟨28334974732507550590113323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18889983155005033726742215 28334974732507550590113323)
          ·
            refine ⟨42502462098761325885169985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28334974732507550590113323 42502462098761325885169985)
            ·
              refine ⟨31876846574070994413877489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42502462098761325885169985 31876846574070994413877489)
              ·
                refine ⟨23907634930553245810408117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31876846574070994413877489 23907634930553245810408117)
                ·
                  refine ⟨2241340774739366794725761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23907634930553245810408117 2241340774739366794725761)
                  ·
                    refine ⟨1681005581054525096044321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2241340774739366794725761 1681005581054525096044321)
                    ·
                      refine ⟨1260754185790893822033241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1681005581054525096044321 1260754185790893822033241)
                      ·
                        rfl

theorem cell23_2455310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_2455310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455310 prefixEnd_2455310 := by exact prefixLift 2455310
  have htrace : WordTrace (prefixWord ++ tailWord_2455310) baseStart_2455310 baseEnd_2455310 := by
    simpa [prefixWord, tailWord_2455310, baseEnd_2455310] using wordTrace_append hprefix tailTrace_2455310
  have hstable : (prefixWord ++ tailWord_2455310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455310).length < 2 ^ (prefixWord ++ tailWord_2455310).sum := by decide
  have hdescent : baseEnd_2455310 < baseStart_2455310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455347 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 1, 2, 3]
def baseStart_2455347 : Nat := 118140960795 + 2455347 * 2 ^ 59
def prefixEnd_2455347 : Nat := 4983230072969 + 3 ^ 40 * 2455347 * 2
def baseEnd_2455347 : Nat := 1260773184575110177270571

theorem tailTrace_2455347 : CollatzResearch.WordTrace tailWord_2455347 prefixEnd_2455347 1260773184575110177270571 := by
  unfold tailWord_2455347
  simp only [CollatzResearch.WordTrace]
  refine ⟨89553862235704633727356295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59702574823803089151570863 89553862235704633727356295)
  ·
    refine ⟨134330793353556950591034443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89553862235704633727356295 134330793353556950591034443)
    ·
      refine ⟨201496190030335425886551665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134330793353556950591034443 201496190030335425886551665)
      ·
        refine ⟨151122142522751569414913749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201496190030335425886551665 151122142522751569414913749)
        ·
          refine ⟨3541925215376989908162041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 151122142522751569414913749 3541925215376989908162041)
          ·
            refine ⟨2656443911532742431121531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3541925215376989908162041 2656443911532742431121531)
            ·
              refine ⟨3984665867299113646682297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656443911532742431121531 3984665867299113646682297)
              ·
                refine ⟨2988499400474335235011723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3984665867299113646682297 2988499400474335235011723)
                ·
                  refine ⟨4482749100711502852517585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2988499400474335235011723 4482749100711502852517585)
                  ·
                    refine ⟨3362061825533627139388189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4482749100711502852517585 3362061825533627139388189)
                    ·
                      refine ⟨1260773184575110177270571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3362061825533627139388189 1260773184575110177270571)
                      ·
                        rfl

theorem cell23_2455347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 2, 3].length) (baseStart_2455347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455347 prefixEnd_2455347 := by exact prefixLift 2455347
  have htrace : WordTrace (prefixWord ++ tailWord_2455347) baseStart_2455347 baseEnd_2455347 := by
    simpa [prefixWord, tailWord_2455347, baseEnd_2455347] using wordTrace_append hprefix tailTrace_2455347
  have hstable : (prefixWord ++ tailWord_2455347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455347).length < 2 ^ (prefixWord ++ tailWord_2455347).sum := by decide
  have hdescent : baseEnd_2455347 < baseStart_2455347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455356 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_2455356 : Nat := 118140960795 + 2455356 * 2 ^ 59
def prefixEnd_2455356 : Nat := 4983230072969 + 3 ^ 40 * 2455356 * 2
def baseEnd_2455356 : Nat := 1260777805901000642058029

theorem tailTrace_2455356 : CollatzResearch.WordTrace tailWord_2455356 prefixEnd_2455356 1260777805901000642058029 := by
  unfold tailWord_2455356
  simp only [CollatzResearch.WordTrace]
  refine ⟨44777095246336014132216961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59702793661781352176289281 44777095246336014132216961)
  ·
    refine ⟨33582821434752010599162721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44777095246336014132216961 33582821434752010599162721)
    ·
      refine ⟨25187116076064007949372041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33582821434752010599162721 25187116076064007949372041)
      ·
        refine ⟨18890337057048005962029031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25187116076064007949372041 18890337057048005962029031)
        ·
          refine ⟨28335505585572008943043547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18890337057048005962029031 28335505585572008943043547)
          ·
            refine ⟨42503258378358013414565321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28335505585572008943043547 42503258378358013414565321)
            ·
              refine ⟨31877443783768510060923991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42503258378358013414565321 31877443783768510060923991)
              ·
                refine ⟨47816165675652765091385987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31877443783768510060923991 47816165675652765091385987)
                ·
                  refine ⟨71724248513479147637078981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47816165675652765091385987 71724248513479147637078981)
                  ·
                    refine ⟨13448296596277340181952309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71724248513479147637078981 13448296596277340181952309)
                    ·
                      refine ⟨1260777805901000642058029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13448296596277340181952309 1260777805901000642058029)
                      ·
                        rfl

theorem cell23_2455356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_2455356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455356 prefixEnd_2455356 := by exact prefixLift 2455356
  have htrace : WordTrace (prefixWord ++ tailWord_2455356) baseStart_2455356 baseEnd_2455356 := by
    simpa [prefixWord, tailWord_2455356, baseEnd_2455356] using wordTrace_append hprefix tailTrace_2455356
  have hstable : (prefixWord ++ tailWord_2455356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455356).length < 2 ^ (prefixWord ++ tailWord_2455356).sum := by decide
  have hdescent : baseEnd_2455356 < baseStart_2455356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455376 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 2, 6]
def baseStart_2455376 : Nat := 118140960795 + 2455376 * 2 ^ 59
def prefixEnd_2455376 : Nat := 4983230072969 + 3 ^ 40 * 2455376 * 2
def baseEnd_2455376 : Nat := 420262691838030187935979

theorem tailTrace_2455376 : CollatzResearch.WordTrace tailWord_2455376 prefixEnd_2455376 420262691838030187935979 := by
  unfold tailWord_2455376
  simp only [CollatzResearch.WordTrace]
  refine ⟨44777459976299785840080991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59703279968399714453441321 44777459976299785840080991)
  ·
    refine ⟨67166189964449678760121487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44777459976299785840080991 67166189964449678760121487)
    ·
      refine ⟨100749284946674518140182231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67166189964449678760121487 100749284946674518140182231)
      ·
        refine ⟨151123927420011777210273347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100749284946674518140182231 151123927420011777210273347)
        ·
          refine ⟨226685891130017665815410021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151123927420011777210273347 226685891130017665815410021)
          ·
            refine ⟨42503604586878312340389379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226685891130017665815410021 42503604586878312340389379)
            ·
              refine ⟨63755406880317468510584069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42503604586878312340389379 63755406880317468510584069)
              ·
                refine ⟨11954138790059525345734513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63755406880317468510584069 11954138790059525345734513)
                ·
                  refine ⟨8965604092544644009300885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11954138790059525345734513 8965604092544644009300885)
                  ·
                    refine ⟨420262691838030187935979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8965604092544644009300885 420262691838030187935979)
                    ·
                      rfl

theorem cell23_2455376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_2455376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455376 prefixEnd_2455376 := by exact prefixLift 2455376
  have htrace : WordTrace (prefixWord ++ tailWord_2455376) baseStart_2455376 baseEnd_2455376 := by
    simpa [prefixWord, tailWord_2455376, baseEnd_2455376] using wordTrace_append hprefix tailTrace_2455376
  have hstable : (prefixWord ++ tailWord_2455376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455376).length < 2 ^ (prefixWord ++ tailWord_2455376).sum := by decide
  have hdescent : baseEnd_2455376 < baseStart_2455376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455377 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 2, 1, 3]
def baseStart_2455377 : Nat := 118140960795 + 2455377 * 2 ^ 59
def prefixEnd_2455377 : Nat := 4983230072969 + 3 ^ 40 * 2455377 * 2
def baseEnd_2455377 : Nat := 1260788588994745059895433

theorem tailTrace_2455377 : CollatzResearch.WordTrace tailWord_2455377 prefixEnd_2455377 1260788588994745059895433 := by
  unfold tailWord_2455377
  simp only [CollatzResearch.WordTrace]
  refine ⟨89554956425595948850948385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59703304283730632567298923 89554956425595948850948385)
  ·
    refine ⟨67166217319196961638211289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89554956425595948850948385 67166217319196961638211289)
    ·
      refine ⟨50374662989397721228658467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67166217319196961638211289 50374662989397721228658467)
      ·
        refine ⟨75561994484096581842987701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50374662989397721228658467 75561994484096581842987701)
        ·
          refine ⟨7083936982884054547780097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75561994484096581842987701 7083936982884054547780097)
          ·
            refine ⟨5312952737163040910835073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7083936982884054547780097 5312952737163040910835073)
            ·
              refine ⟨3984714552872280683126305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5312952737163040910835073 3984714552872280683126305)
              ·
                refine ⟨2988535914654210512344729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3984714552872280683126305 2988535914654210512344729)
                ·
                  refine ⟨2241401935990657884258547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2988535914654210512344729 2241401935990657884258547)
                  ·
                    refine ⟨3362102903985986826387821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2241401935990657884258547 3362102903985986826387821)
                    ·
                      refine ⟨1260788588994745059895433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3362102903985986826387821 1260788588994745059895433)
                      ·
                        rfl

theorem cell23_2455377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_2455377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455377 prefixEnd_2455377 := by exact prefixLift 2455377
  have htrace : WordTrace (prefixWord ++ tailWord_2455377) baseStart_2455377 baseEnd_2455377 := by
    simpa [prefixWord, tailWord_2455377, baseEnd_2455377] using wordTrace_append hprefix tailTrace_2455377
  have hstable : (prefixWord ++ tailWord_2455377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455377).length < 2 ^ (prefixWord ++ tailWord_2455377).sum := by decide
  have hdescent : baseEnd_2455377 < baseStart_2455377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455413 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2455413 : Nat := 118140960795 + 2455413 * 2 ^ 59
def prefixEnd_2455413 : Nat := 4983230072969 + 3 ^ 40 * 2455413 * 2
def baseEnd_2455413 : Nat := 1260807074298306919045267

theorem tailTrace_2455413 : CollatzResearch.WordTrace tailWord_2455413 prefixEnd_2455413 1260807074298306919045267 := by
  unfold tailWord_2455413
  simp only [CollatzResearch.WordTrace]
  refine ⟨89556269453465526999258893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59704179635643684666172595 89556269453465526999258893)
  ·
    refine ⟨33583601045049572624722085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89556269453465526999258893 33583601045049572624722085)
    ·
      refine ⟨6296925195946794867135391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33583601045049572624722085 6296925195946794867135391)
      ·
        refine ⟨9445387793920192300703087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6296925195946794867135391 9445387793920192300703087)
        ·
          refine ⟨14168081690880288451054631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9445387793920192300703087 14168081690880288451054631)
          ·
            refine ⟨21252122536320432676581947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14168081690880288451054631 21252122536320432676581947)
            ·
              refine ⟨31878183804480649014872921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21252122536320432676581947 31878183804480649014872921)
              ·
                refine ⟨23908637853360486761154691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31878183804480649014872921 23908637853360486761154691)
                ·
                  refine ⟨35862956780040730141732037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23908637853360486761154691 35862956780040730141732037)
                  ·
                    refine ⟨6724304396257636901574757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35862956780040730141732037 6724304396257636901574757)
                    ·
                      refine ⟨1260807074298306919045267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6724304396257636901574757 1260807074298306919045267)
                      ·
                        rfl

theorem cell23_2455413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2455413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455413 prefixEnd_2455413 := by exact prefixLift 2455413
  have htrace : WordTrace (prefixWord ++ tailWord_2455413) baseStart_2455413 baseEnd_2455413 := by
    simpa [prefixWord, tailWord_2455413, baseEnd_2455413] using wordTrace_append hprefix tailTrace_2455413
  have hstable : (prefixWord ++ tailWord_2455413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455413).length < 2 ^ (prefixWord ++ tailWord_2455413).sum := by decide
  have hdescent : baseEnd_2455413 < baseStart_2455413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455433 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 4, 3, 3]
def baseStart_2455433 : Nat := 118140960795 + 2455433 * 2 ^ 59
def prefixEnd_2455433 : Nat := 4983230072969 + 3 ^ 40 * 2455433 * 2
def baseEnd_2455433 : Nat := 1260817343911396840795175

theorem tailTrace_2455433 : CollatzResearch.WordTrace tailWord_2455433 prefixEnd_2455433 1260817343911396840795175 := by
  unfold tailWord_2455433
  simp only [CollatzResearch.WordTrace]
  refine ⟨89556998913393070414986953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59704665942262046943324635 89556998913393070414986953)
  ·
    refine ⟨67167749185044802811240215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89556998913393070414986953 67167749185044802811240215)
    ·
      refine ⟨100751623777567204216860323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67167749185044802811240215 100751623777567204216860323)
      ·
        refine ⟨151127435666350806325290485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100751623777567204216860323 151127435666350806325290485)
        ·
          refine ⟨14168197093720388092995983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151127435666350806325290485 14168197093720388092995983)
          ·
            refine ⟨21252295640580582139493975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14168197093720388092995983 21252295640580582139493975)
            ·
              refine ⟨31878443460870873209240963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21252295640580582139493975 31878443460870873209240963)
              ·
                refine ⟨47817665191306309813861445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31878443460870873209240963 47817665191306309813861445)
                ·
                  refine ⟨8965812223369933090099021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47817665191306309813861445 8965812223369933090099021)
                  ·
                    refine ⟨3362179583763724908787133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8965812223369933090099021 3362179583763724908787133)
                    ·
                      refine ⟨1260817343911396840795175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3362179583763724908787133 1260817343911396840795175)
                      ·
                        rfl

theorem cell23_2455433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3, 3].length) (baseStart_2455433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455433 prefixEnd_2455433 := by exact prefixLift 2455433
  have htrace : WordTrace (prefixWord ++ tailWord_2455433) baseStart_2455433 baseEnd_2455433 := by
    simpa [prefixWord, tailWord_2455433, baseEnd_2455433] using wordTrace_append hprefix tailTrace_2455433
  have hstable : (prefixWord ++ tailWord_2455433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455433).length < 2 ^ (prefixWord ++ tailWord_2455433).sum := by decide
  have hdescent : baseEnd_2455433 < baseStart_2455433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455434 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2]
def baseStart_2455434 : Nat := 118140960795 + 2455434 * 2 ^ 59
def prefixEnd_2455434 : Nat := 4983230072969 + 3 ^ 40 * 2455434 * 2
def baseEnd_2455434 : Nat := 1260817857392051336882671

theorem tailTrace_2455434 : CollatzResearch.WordTrace tailWord_2455434 prefixEnd_2455434 1260817857392051336882671 := by
  unfold tailWord_2455434
  simp only [CollatzResearch.WordTrace]
  refine ⟨22389258846597361896443339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59704690257592965057182237 22389258846597361896443339)
  ·
    refine ⟨33583888269896042844665009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22389258846597361896443339 33583888269896042844665009)
    ·
      refine ⟨25187916202422032133498757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33583888269896042844665009 25187916202422032133498757)
      ·
        refine ⟨4722734287954131025031017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25187916202422032133498757 4722734287954131025031017)
        ·
          refine ⟨3542050715965598268773263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4722734287954131025031017 3542050715965598268773263)
          ·
            refine ⟨5313076073948397403159895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542050715965598268773263 5313076073948397403159895)
            ·
              refine ⟨7969614110922596104739843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313076073948397403159895 7969614110922596104739843)
              ·
                refine ⟨11954421166383894157109765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7969614110922596104739843 11954421166383894157109765)
                ·
                  refine ⟨2241453968696980154458081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11954421166383894157109765 2241453968696980154458081)
                  ·
                    refine ⟨1681090476522735115843561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2241453968696980154458081 1681090476522735115843561)
                    ·
                      refine ⟨1260817857392051336882671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1681090476522735115843561 1260817857392051336882671)
                      ·
                        rfl

theorem cell23_2455434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_2455434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455434 prefixEnd_2455434 := by exact prefixLift 2455434
  have htrace : WordTrace (prefixWord ++ tailWord_2455434) baseStart_2455434 baseEnd_2455434 := by
    simpa [prefixWord, tailWord_2455434, baseEnd_2455434] using wordTrace_append hprefix tailTrace_2455434
  have hstable : (prefixWord ++ tailWord_2455434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455434).length < 2 ^ (prefixWord ++ tailWord_2455434).sum := by decide
  have hdescent : baseEnd_2455434 < baseStart_2455434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455450 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2455450 : Nat := 118140960795 + 2455450 * 2 ^ 59
def prefixEnd_2455450 : Nat := 4983230072969 + 3 ^ 40 * 2455450 * 2
def baseEnd_2455450 : Nat := 1260826073082523274282597

theorem tailTrace_2455450 : CollatzResearch.WordTrace tailWord_2455450 prefixEnd_2455450 1260826073082523274282597 := by
  unfold tailWord_2455450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22389404738582870579588951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59705079302887654878903869 22389404738582870579588951)
  ·
    refine ⟨33584107107874305869383427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22389404738582870579588951 33584107107874305869383427)
    ·
      refine ⟨50376160661811458804075141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33584107107874305869383427 50376160661811458804075141)
      ·
        refine ⟨9445530124089648525764089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50376160661811458804075141 9445530124089648525764089)
        ·
          refine ⟨7084147593067236394323067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9445530124089648525764089 7084147593067236394323067)
          ·
            refine ⟨10626221389600854591484601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7084147593067236394323067 10626221389600854591484601)
            ·
              refine ⟨7969666042200640943613451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10626221389600854591484601 7969666042200640943613451)
              ·
                refine ⟨11954499063300961415420177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7969666042200640943613451 11954499063300961415420177)
                ·
                  refine ⟨8965874297475721061565133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11954499063300961415420177 8965874297475721061565133)
                  ·
                    refine ⟨3362202861553395398086925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8965874297475721061565133 3362202861553395398086925)
                    ·
                      refine ⟨1260826073082523274282597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3362202861553395398086925 1260826073082523274282597)
                      ·
                        rfl

theorem cell23_2455450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2455450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455450 prefixEnd_2455450 := by exact prefixLift 2455450
  have htrace : WordTrace (prefixWord ++ tailWord_2455450) baseStart_2455450 baseEnd_2455450 := by
    simpa [prefixWord, tailWord_2455450, baseEnd_2455450] using wordTrace_append hprefix tailTrace_2455450
  have hstable : (prefixWord ++ tailWord_2455450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455450).length < 2 ^ (prefixWord ++ tailWord_2455450).sum := by decide
  have hdescent : baseEnd_2455450 < baseStart_2455450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455453 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2455453 : Nat := 118140960795 + 2455453 * 2 ^ 59
def prefixEnd_2455453 : Nat := 4983230072969 + 3 ^ 40 * 2455453 * 2
def baseEnd_2455453 : Nat := 420275871174828920848361

theorem tailTrace_2455453 : CollatzResearch.WordTrace tailWord_2455453 prefixEnd_2455453 420275871174828920848361 := by
  unfold tailWord_2455453
  simp only [CollatzResearch.WordTrace]
  refine ⟨89557728373320613830715013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59705152248880409220476675 89557728373320613830715013)
  ·
    refine ⟨16792074069997615093259065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89557728373320613830715013 16792074069997615093259065)
    ·
      refine ⟨12594055552498211319944299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16792074069997615093259065 12594055552498211319944299)
      ·
        refine ⟨18891083328747316979916449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12594055552498211319944299 18891083328747316979916449)
        ·
          refine ⟨14168312496560487734937337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18891083328747316979916449 14168312496560487734937337)
          ·
            refine ⟨10626234372420365801203003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14168312496560487734937337 10626234372420365801203003)
            ·
              refine ⟨15939351558630548701804505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10626234372420365801203003 15939351558630548701804505)
              ·
                refine ⟨11954513668972911526353379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15939351558630548701804505 11954513668972911526353379)
                ·
                  refine ⟨17931770503459367289530069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11954513668972911526353379 17931770503459367289530069)
                  ·
                    refine ⟨420275871174828920848361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17931770503459367289530069 420275871174828920848361)
                    ·
                      rfl

theorem cell23_2455453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2455453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455453 prefixEnd_2455453 := by exact prefixLift 2455453
  have htrace : WordTrace (prefixWord ++ tailWord_2455453) baseStart_2455453 baseEnd_2455453 := by
    simpa [prefixWord, tailWord_2455453, baseEnd_2455453] using wordTrace_append hprefix tailTrace_2455453
  have hstable : (prefixWord ++ tailWord_2455453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455453).length < 2 ^ (prefixWord ++ tailWord_2455453).sum := by decide
  have hdescent : baseEnd_2455453 < baseStart_2455453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455483 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 7, 4]
def baseStart_2455483 : Nat := 118140960795 + 2455483 * 2 ^ 59
def prefixEnd_2455483 : Nat := 4983230072969 + 3 ^ 40 * 2455483 * 2
def baseEnd_2455483 : Nat := 420281005981373881723315

theorem tailTrace_2455483 : CollatzResearch.WordTrace tailWord_2455483 prefixEnd_2455483 420281005981373881723315 := by
  unfold tailWord_2455483
  simp only [CollatzResearch.WordTrace]
  refine ⟨89558822563211928954307103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59705881708807952636204735 89558822563211928954307103)
  ·
    refine ⟨134338233844817893431460655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89558822563211928954307103 134338233844817893431460655)
    ·
      refine ⟨201507350767226840147190983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134338233844817893431460655 201507350767226840147190983)
      ·
        refine ⟨302261026150840260220786475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201507350767226840147190983 302261026150840260220786475)
        ·
          refine ⟨453391539226260390331179713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302261026150840260220786475 453391539226260390331179713)
          ·
            refine ⟨340043654419695292748384785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453391539226260390331179713 340043654419695292748384785)
            ·
              refine ⟨255032740814771469561288589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340043654419695292748384785 255032740814771469561288589)
              ·
                refine ⟨95637277805539301085483221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255032740814771469561288589 95637277805539301085483221)
                ·
                  refine ⟨2241498698567327369191013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 95637277805539301085483221 2241498698567327369191013)
                  ·
                    refine ⟨420281005981373881723315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2241498698567327369191013 420281005981373881723315)
                    ·
                      rfl

theorem cell23_2455483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 4].length) (baseStart_2455483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455483 prefixEnd_2455483 := by exact prefixLift 2455483
  have htrace : WordTrace (prefixWord ++ tailWord_2455483) baseStart_2455483 baseEnd_2455483 := by
    simpa [prefixWord, tailWord_2455483, baseEnd_2455483] using wordTrace_append hprefix tailTrace_2455483
  have hstable : (prefixWord ++ tailWord_2455483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455483).length < 2 ^ (prefixWord ++ tailWord_2455483).sum := by decide
  have hdescent : baseEnd_2455483 < baseStart_2455483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455493 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 3, 4, 3]
def baseStart_2455493 : Nat := 118140960795 + 2455493 * 2 ^ 59
def prefixEnd_2455493 : Nat := 4983230072969 + 3 ^ 40 * 2455493 * 2
def baseEnd_2455493 : Nat := 1260848152750666606044899

theorem tailTrace_2455493 : CollatzResearch.WordTrace tailWord_2455493 prefixEnd_2455493 1260848152750666606044899 := by
  unfold tailWord_2455493
  simp only [CollatzResearch.WordTrace]
  refine ⟨89559187293175700662171133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59706124862117133774780755 89559187293175700662171133)
  ·
    refine ⟨33584695234940887748314175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89559187293175700662171133 33584695234940887748314175)
    ·
      refine ⟨50377042852411331622471263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33584695234940887748314175 50377042852411331622471263)
      ·
        refine ⟨75565564278616997433706895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50377042852411331622471263 75565564278616997433706895)
        ·
          refine ⟨113348346417925496150560343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75565564278616997433706895 113348346417925496150560343)
          ·
            refine ⟨170022519626888244225840515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113348346417925496150560343 170022519626888244225840515)
            ·
              refine ⟨255033779440332366338760773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170022519626888244225840515 255033779440332366338760773)
              ·
                refine ⟨47818833645062318688517645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255033779440332366338760773 47818833645062318688517645)
                ·
                  refine ⟨17932062616898369508194117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47818833645062318688517645 17932062616898369508194117)
                  ·
                    refine ⟨3362261740668444282786397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17932062616898369508194117 3362261740668444282786397)
                    ·
                      refine ⟨1260848152750666606044899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3362261740668444282786397 1260848152750666606044899)
                      ·
                        rfl

theorem cell23_2455493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_2455493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455493 prefixEnd_2455493 := by exact prefixLift 2455493
  have htrace : WordTrace (prefixWord ++ tailWord_2455493) baseStart_2455493 baseEnd_2455493 := by
    simpa [prefixWord, tailWord_2455493, baseEnd_2455493] using wordTrace_append hprefix tailTrace_2455493
  have hstable : (prefixWord ++ tailWord_2455493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455493).length < 2 ^ (prefixWord ++ tailWord_2455493).sum := by decide
  have hdescent : baseEnd_2455493 < baseStart_2455493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455593 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 4]
def baseStart_2455593 : Nat := 118140960795 + 2455593 * 2 ^ 59
def prefixEnd_2455593 : Nat := 4983230072969 + 3 ^ 40 * 2455593 * 2
def baseEnd_2455593 : Nat := 1260899500816116214794439

theorem tailTrace_2455593 : CollatzResearch.WordTrace tailWord_2455593 prefixEnd_2455593 1260899500816116214794439 := by
  unfold tailWord_2455593
  simp only [CollatzResearch.WordTrace]
  refine ⟨89562834592813417740811433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59708556395208945160540955 89562834592813417740811433)
  ·
    refine ⟨67172125944610063305608575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89562834592813417740811433 67172125944610063305608575)
    ·
      refine ⟨100758188916915094958412863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67172125944610063305608575 100758188916915094958412863)
      ·
        refine ⟨151137283375372642437619295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100758188916915094958412863 151137283375372642437619295)
        ·
          refine ⟨226705925063058963656428943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151137283375372642437619295 226705925063058963656428943)
          ·
            refine ⟨340058887594588445484643415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226705925063058963656428943 340058887594588445484643415)
            ·
              refine ⟨510088331391882668226965123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340058887594588445484643415 510088331391882668226965123)
              ·
                refine ⟨765132497087824002340447685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510088331391882668226965123 765132497087824002340447685)
                ·
                  refine ⟨143462343203967000438833941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 765132497087824002340447685 143462343203967000438833941)
                  ·
                    refine ⟨6724797337685953145570341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 143462343203967000438833941 6724797337685953145570341)
                    ·
                      refine ⟨1260899500816116214794439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6724797337685953145570341 1260899500816116214794439)
                      ·
                        rfl

theorem cell23_2455593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_2455593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455593 prefixEnd_2455593 := by exact prefixLift 2455593
  have htrace : WordTrace (prefixWord ++ tailWord_2455593) baseStart_2455593 baseEnd_2455593 := by
    simpa [prefixWord, tailWord_2455593, baseEnd_2455593] using wordTrace_append hprefix tailTrace_2455593
  have hstable : (prefixWord ++ tailWord_2455593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455593).length < 2 ^ (prefixWord ++ tailWord_2455593).sum := by decide
  have hdescent : baseEnd_2455593 < baseStart_2455593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455594 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 1, 5]
def baseStart_2455594 : Nat := 118140960795 + 2455594 * 2 ^ 59
def prefixEnd_2455594 : Nat := 4983230072969 + 3 ^ 40 * 2455594 * 2
def baseEnd_2455594 : Nat := 420300004765590236960645

theorem tailTrace_2455594 : CollatzResearch.WordTrace tailWord_2455594 prefixEnd_2455594 420300004765590236960645 := by
  unfold tailWord_2455594
  simp only [CollatzResearch.WordTrace]
  refine ⟨22390717766452448727899459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59708580710539863274398557 22390717766452448727899459)
  ·
    refine ⟨33586076649678673091849189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22390717766452448727899459 33586076649678673091849189)
    ·
      refine ⟨6297389371814751204721723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33586076649678673091849189 6297389371814751204721723)
      ·
        refine ⟨9446084057722126807082585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6297389371814751204721723 9446084057722126807082585)
        ·
          refine ⟨7084563043291595105311939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9446084057722126807082585 7084563043291595105311939)
          ·
            refine ⟨10626844564937392657967909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7084563043291595105311939 10626844564937392657967909)
            ·
              refine ⟨1992533355925761123368983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10626844564937392657967909 1992533355925761123368983)
              ·
                refine ⟨2988800033888641685053475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1992533355925761123368983 2988800033888641685053475)
                ·
                  refine ⟨4483200050832962527580213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2988800033888641685053475 4483200050832962527580213)
                  ·
                    refine ⟨420300004765590236960645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4483200050832962527580213 420300004765590236960645)
                    ·
                      rfl

theorem cell23_2455594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_2455594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455594 prefixEnd_2455594 := by exact prefixLift 2455594
  have htrace : WordTrace (prefixWord ++ tailWord_2455594) baseStart_2455594 baseEnd_2455594 := by
    simpa [prefixWord, tailWord_2455594, baseEnd_2455594] using wordTrace_append hprefix tailTrace_2455594
  have hstable : (prefixWord ++ tailWord_2455594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455594).length < 2 ^ (prefixWord ++ tailWord_2455594).sum := by decide
  have hdescent : baseEnd_2455594 < baseStart_2455594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455607 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 2, 4]
def baseStart_2455607 : Nat := 118140960795 + 2455607 * 2 ^ 59
def prefixEnd_2455607 : Nat := 4983230072969 + 3 ^ 40 * 2455607 * 2
def baseEnd_2455607 : Nat := 420302229848426386673125

theorem tailTrace_2455607 : CollatzResearch.WordTrace tailWord_2455607 prefixEnd_2455607 420302229848426386673125 := by
  unfold tailWord_2455607
  simp only [CollatzResearch.WordTrace]
  refine ⟨89563345214762698131821075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59708896809841798754547383 89563345214762698131821075)
  ·
    refine ⟨134345017822144047197731613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89563345214762698131821075 134345017822144047197731613)
    ·
      refine ⟨50379381683304017699149355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134345017822144047197731613 50379381683304017699149355)
      ·
        refine ⟨75569072524956026548724033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50379381683304017699149355 75569072524956026548724033)
        ·
          refine ⟨56676804393717019911543025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75569072524956026548724033 56676804393717019911543025)
          ·
            refine ⟨42507603295287764933657269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56676804393717019911543025 42507603295287764933657269)
            ·
              refine ⟨3985087808933227962530369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42507603295287764933657269 3985087808933227962530369)
              ·
                refine ⟨2988815856699920971897777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3985087808933227962530369 2988815856699920971897777)
                ·
                  refine ⟨2241611892524940728923333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2988815856699920971897777 2241611892524940728923333)
                  ·
                    refine ⟨420302229848426386673125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2241611892524940728923333 420302229848426386673125)
                    ·
                      rfl

theorem cell23_2455607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_2455607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455607 prefixEnd_2455607 := by exact prefixLift 2455607
  have htrace : WordTrace (prefixWord ++ tailWord_2455607) baseStart_2455607 baseEnd_2455607 := by
    simpa [prefixWord, tailWord_2455607, baseEnd_2455607] using wordTrace_append hprefix tailTrace_2455607
  have hstable : (prefixWord ++ tailWord_2455607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455607).length < 2 ^ (prefixWord ++ tailWord_2455607).sum := by decide
  have hdescent : baseEnd_2455607 < baseStart_2455607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455617 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2455617 : Nat := 118140960795 + 2455617 * 2 ^ 59
def prefixEnd_2455617 : Nat := 4983230072969 + 3 ^ 40 * 2455617 * 2
def baseEnd_2455617 : Nat := 1260911824351824120894329

theorem tailTrace_2455617 : CollatzResearch.WordTrace tailWord_2455617 prefixEnd_2455617 1260911824351824120894329 := by
  unfold tailWord_2455617
  simp only [CollatzResearch.WordTrace]
  refine ⟨89563709944726469839685105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59709139963150979893123403 89563709944726469839685105)
  ·
    refine ⟨67172782458544852379763829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89563709944726469839685105 67172782458544852379763829)
    ·
      refine ⟨6297448355488579910602859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67172782458544852379763829 6297448355488579910602859)
      ·
        refine ⟨9446172533232869865904289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6297448355488579910602859 9446172533232869865904289)
        ·
          refine ⟨7084629399924652399428217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9446172533232869865904289 7084629399924652399428217)
          ·
            refine ⟨5313472049943489299571163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7084629399924652399428217 5313472049943489299571163)
            ·
              refine ⟨7970208074915233949356745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313472049943489299571163 7970208074915233949356745)
              ·
                refine ⟨5977656056186425462017559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7970208074915233949356745 5977656056186425462017559)
                ·
                  refine ⟨8966484084279638193026339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5977656056186425462017559 8966484084279638193026339)
                  ·
                    refine ⟨13449726126419457289539509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8966484084279638193026339 13449726126419457289539509)
                    ·
                      refine ⟨1260911824351824120894329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13449726126419457289539509 1260911824351824120894329)
                      ·
                        rfl

theorem cell23_2455617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2455617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455617 prefixEnd_2455617 := by exact prefixLift 2455617
  have htrace : WordTrace (prefixWord ++ tailWord_2455617) baseStart_2455617 baseEnd_2455617 := by
    simpa [prefixWord, tailWord_2455617, baseEnd_2455617] using wordTrace_append hprefix tailTrace_2455617
  have hstable : (prefixWord ++ tailWord_2455617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455617).length < 2 ^ (prefixWord ++ tailWord_2455617).sum := by decide
  have hdescent : baseEnd_2455617 < baseStart_2455617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455637 : List Nat := [1, 3, 2, 2, 1, 5, 2, 7]
def baseStart_2455637 : Nat := 118140960795 + 2455637 * 2 ^ 59
def prefixEnd_2455637 : Nat := 4983230072969 + 3 ^ 40 * 2455637 * 2
def baseEnd_2455637 : Nat := 46700818294996816394231

theorem tailTrace_2455637 : CollatzResearch.WordTrace tailWord_2455637 prefixEnd_2455637 46700818294996816394231 := by
  unfold tailWord_2455637
  simp only [CollatzResearch.WordTrace]
  refine ⟨89564439404654013255413165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59709626269769342170275443 89564439404654013255413165)
  ·
    refine ⟨33586664776745254970779937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89564439404654013255413165 33586664776745254970779937)
    ·
      refine ⟨25189998582558941228084953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33586664776745254970779937 25189998582558941228084953)
      ·
        refine ⟨18892498936919205921063715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25189998582558941228084953 18892498936919205921063715)
        ·
          refine ⟨28338748405378808881595573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18892498936919205921063715 28338748405378808881595573)
          ·
            refine ⟨2656757663004263332649585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28338748405378808881595573 2656757663004263332649585)
            ·
              refine ⟨1992568247253197499487189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2656757663004263332649585 1992568247253197499487189)
              ·
                refine ⟨46700818294996816394231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1992568247253197499487189 46700818294996816394231)
                ·
                  rfl

theorem cell23_2455637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 7].length) (baseStart_2455637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455637 prefixEnd_2455637 := by exact prefixLift 2455637
  have htrace : WordTrace (prefixWord ++ tailWord_2455637) baseStart_2455637 baseEnd_2455637 := by
    simpa [prefixWord, tailWord_2455637, baseEnd_2455637] using wordTrace_append hprefix tailTrace_2455637
  have hstable : (prefixWord ++ tailWord_2455637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455637).length < 2 ^ (prefixWord ++ tailWord_2455637).sum := by decide
  have hdescent : baseEnd_2455637 < baseStart_2455637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455648 : List Nat := [2, 1, 1, 3, 2, 5, 1, 3, 1, 2, 2]
def baseStart_2455648 : Nat := 118140960795 + 2455648 * 2 ^ 59
def prefixEnd_2455648 : Nat := 4983230072969 + 3 ^ 40 * 2455648 * 2
def baseEnd_2455648 : Nat := 1260927742252113499606687

theorem tailTrace_2455648 : CollatzResearch.WordTrace tailWord_2455648 prefixEnd_2455648 1260927742252113499606687 := by
  unfold tailWord_2455648
  simp only [CollatzResearch.WordTrace]
  refine ⟨44782420303807081067031799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59709893738409441422709065 44782420303807081067031799)
  ·
    refine ⟨67173630455710621600547699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44782420303807081067031799 67173630455710621600547699)
    ·
      refine ⟨100760445683565932400821549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67173630455710621600547699 100760445683565932400821549)
      ·
        refine ⟨37785167131337224650308081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100760445683565932400821549 37785167131337224650308081)
        ·
          refine ⟨28338875348502918487731061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37785167131337224650308081 28338875348502918487731061)
          ·
            refine ⟨2656769563922148608224787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28338875348502918487731061 2656769563922148608224787)
            ·
              refine ⟨3985154345883222912337181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656769563922148608224787 3985154345883222912337181)
              ·
                refine ⟨1494432879706208592126443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3985154345883222912337181 1494432879706208592126443)
                ·
                  refine ⟨2241649319559312888189665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494432879706208592126443 2241649319559312888189665)
                  ·
                    refine ⟨1681236989669484666142249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2241649319559312888189665 1681236989669484666142249)
                    ·
                      refine ⟨1260927742252113499606687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1681236989669484666142249 1260927742252113499606687)
                      ·
                        rfl

theorem cell23_2455648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_2455648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455648 prefixEnd_2455648 := by exact prefixLift 2455648
  have htrace : WordTrace (prefixWord ++ tailWord_2455648) baseStart_2455648 baseEnd_2455648 := by
    simpa [prefixWord, tailWord_2455648, baseEnd_2455648] using wordTrace_append hprefix tailTrace_2455648
  have hstable : (prefixWord ++ tailWord_2455648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455648).length < 2 ^ (prefixWord ++ tailWord_2455648).sum := by decide
  have hdescent : baseEnd_2455648 < baseStart_2455648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455681 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_2455681 : Nat := 118140960795 + 2455681 * 2 ^ 59
def prefixEnd_2455681 : Nat := 4983230072969 + 3 ^ 40 * 2455681 * 2
def baseEnd_2455681 : Nat := 1260944687113711870494035

theorem tailTrace_2455681 : CollatzResearch.WordTrace tailWord_2455681 prefixEnd_2455681 1260944687113711870494035 := by
  unfold tailWord_2455681
  simp only [CollatzResearch.WordTrace]
  refine ⟨89566044216494608770014897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59710696144329739180009931 89566044216494608770014897)
  ·
    refine ⟨67174533162370956577511173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89566044216494608770014897 67174533162370956577511173)
    ·
      refine ⟨12595224967944554358283345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67174533162370956577511173 12595224967944554358283345)
      ·
        refine ⟨9446418725958415768712509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12595224967944554358283345 9446418725958415768712509)
        ·
          refine ⟨3542407022234405913267191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9446418725958415768712509 3542407022234405913267191)
          ·
            refine ⟨5313610533351608869900787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542407022234405913267191 5313610533351608869900787)
            ·
              refine ⟨7970415800027413304851181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313610533351608869900787 7970415800027413304851181)
              ·
                refine ⟨2988905925010279989319193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7970415800027413304851181 2988905925010279989319193)
                ·
                  refine ⟨2241679443757709991989395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2988905925010279989319193 2241679443757709991989395)
                  ·
                    refine ⟨3362519165636564987984093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2241679443757709991989395 3362519165636564987984093)
                    ·
                      refine ⟨1260944687113711870494035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3362519165636564987984093 1260944687113711870494035)
                      ·
                        rfl

theorem cell23_2455681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_2455681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455681 prefixEnd_2455681 := by exact prefixLift 2455681
  have htrace : WordTrace (prefixWord ++ tailWord_2455681) baseStart_2455681 baseEnd_2455681 := by
    simpa [prefixWord, tailWord_2455681, baseEnd_2455681] using wordTrace_append hprefix tailTrace_2455681
  have hstable : (prefixWord ++ tailWord_2455681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455681).length < 2 ^ (prefixWord ++ tailWord_2455681).sum := by decide
  have hdescent : baseEnd_2455681 < baseStart_2455681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455702 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_2455702 : Nat := 118140960795 + 2455702 * 2 ^ 59
def prefixEnd_2455702 : Nat := 4983230072969 + 3 ^ 40 * 2455702 * 2
def baseEnd_2455702 : Nat := 1260955470207456288331439

theorem tailTrace_2455702 : CollatzResearch.WordTrace tailWord_2455702 prefixEnd_2455702 1260955470207456288331439 := by
  unfold tailWord_2455702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5597925634338658084783085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59711206766279019571019573 5597925634338658084783085)
  ·
    refine ⟨2099222112876996781793657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5597925634338658084783085 2099222112876996781793657)
    ·
      refine ⟨1574416584657747586345243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2099222112876996781793657 1574416584657747586345243)
      ·
        refine ⟨2361624876986621379517865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574416584657747586345243 2361624876986621379517865)
        ·
          refine ⟨1771218657739966034638399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2361624876986621379517865 1771218657739966034638399)
          ·
            refine ⟨2656827986609949051957599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771218657739966034638399 2656827986609949051957599)
            ·
              refine ⟨3985241979914923577936399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656827986609949051957599 3985241979914923577936399)
              ·
                refine ⟨5977862969872385366904599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3985241979914923577936399 5977862969872385366904599)
                ·
                  refine ⟨8966794454808578050356899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5977862969872385366904599 8966794454808578050356899)
                  ·
                    refine ⟨13450191682212867075535349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8966794454808578050356899 13450191682212867075535349)
                    ·
                      refine ⟨1260955470207456288331439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13450191682212867075535349 1260955470207456288331439)
                      ·
                        rfl

theorem cell23_2455702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_2455702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455702 prefixEnd_2455702 := by exact prefixLift 2455702
  have htrace : WordTrace (prefixWord ++ tailWord_2455702) baseStart_2455702 baseEnd_2455702 := by
    simpa [prefixWord, tailWord_2455702, baseEnd_2455702] using wordTrace_append hprefix tailTrace_2455702
  have hstable : (prefixWord ++ tailWord_2455702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455702).length < 2 ^ (prefixWord ++ tailWord_2455702).sum := by decide
  have hdescent : baseEnd_2455702 < baseStart_2455702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455737 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 2, 3, 3]
def baseStart_2455737 : Nat := 118140960795 + 2455737 * 2 ^ 59
def prefixEnd_2455737 : Nat := 4983230072969 + 3 ^ 40 * 2455737 * 2
def baseEnd_2455737 : Nat := 1260973442030363651393777

theorem tailTrace_2455737 : CollatzResearch.WordTrace tailWord_2455737 prefixEnd_2455737 1260973442030363651393777 := by
  unfold tailWord_2455737
  simp only [CollatzResearch.WordTrace]
  refine ⟨89568086704291730334053465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59712057802861153556035643 89568086704291730334053465)
  ·
    refine ⟨67176065028218797750540099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89568086704291730334053465 67176065028218797750540099)
    ·
      refine ⟨100764097542328196625810149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67176065028218797750540099 100764097542328196625810149)
      ·
        refine ⟨18893268289186536867339403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100764097542328196625810149 18893268289186536867339403)
        ·
          refine ⟨28339902433779805301009105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18893268289186536867339403 28339902433779805301009105)
          ·
            refine ⟨21254926825334853975756829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28339902433779805301009105 21254926825334853975756829)
            ·
              refine ⟨7970597559500570240908811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21254926825334853975756829 7970597559500570240908811)
              ·
                refine ⟨11955896339250855361363217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7970597559500570240908811 11955896339250855361363217)
                ·
                  refine ⟨8966922254438141521022413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11955896339250855361363217 8966922254438141521022413)
                  ·
                    refine ⟨3362595845414303070383405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8966922254438141521022413 3362595845414303070383405)
                    ·
                      refine ⟨1260973442030363651393777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3362595845414303070383405 1260973442030363651393777)
                      ·
                        rfl

theorem cell23_2455737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_2455737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455737 prefixEnd_2455737 := by exact prefixLift 2455737
  have htrace : WordTrace (prefixWord ++ tailWord_2455737) baseStart_2455737 baseEnd_2455737 := by
    simpa [prefixWord, tailWord_2455737, baseEnd_2455737] using wordTrace_append hprefix tailTrace_2455737
  have hstable : (prefixWord ++ tailWord_2455737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455737).length < 2 ^ (prefixWord ++ tailWord_2455737).sum := by decide
  have hdescent : baseEnd_2455737 < baseStart_2455737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455772 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2455772 : Nat := 118140960795 + 2455772 * 2 ^ 59
def prefixEnd_2455772 : Nat := 4983230072969 + 3 ^ 40 * 2455772 * 2
def baseEnd_2455772 : Nat := 1260991413853271014456117

theorem tailTrace_2455772 : CollatzResearch.WordTrace tailWord_2455772 prefixEnd_2455772 1260991413853271014456117 := by
  unfold tailWord_2455772
  simp only [CollatzResearch.WordTrace]
  refine ⟨44784681629582465655788785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59712908839443287541051713 44784681629582465655788785)
  ·
    refine ⟨33588511222186849241841589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44784681629582465655788785 33588511222186849241841589)
    ·
      refine ⟨3148922927080017116422649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33588511222186849241841589 3148922927080017116422649)
      ·
        refine ⟨2361692195310012837316987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3148922927080017116422649 2361692195310012837316987)
        ·
          refine ⟨3542538292965019255975481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361692195310012837316987 3542538292965019255975481)
          ·
            refine ⟨2656903719723764441981611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3542538292965019255975481 2656903719723764441981611)
            ·
              refine ⟨3985355579585646662972417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656903719723764441981611 3985355579585646662972417)
              ·
                refine ⟨2989016684689234997229313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3985355579585646662972417 2989016684689234997229313)
                ·
                  refine ⟨2241762513516926247921985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2989016684689234997229313 2241762513516926247921985)
                  ·
                    refine ⟨1681321885137694685941489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2241762513516926247921985 1681321885137694685941489)
                    ·
                      refine ⟨1260991413853271014456117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1681321885137694685941489 1260991413853271014456117)
                      ·
                        rfl

theorem cell23_2455772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2455772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455772 prefixEnd_2455772 := by exact prefixLift 2455772
  have htrace : WordTrace (prefixWord ++ tailWord_2455772) baseStart_2455772 baseEnd_2455772 := by
    simpa [prefixWord, tailWord_2455772, baseEnd_2455772] using wordTrace_append hprefix tailTrace_2455772
  have hstable : (prefixWord ++ tailWord_2455772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455772).length < 2 ^ (prefixWord ++ tailWord_2455772).sum := by decide
  have hdescent : baseEnd_2455772 < baseStart_2455772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455777 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_2455777 : Nat := 118140960795 + 2455777 * 2 ^ 59
def prefixEnd_2455777 : Nat := 4983230072969 + 3 ^ 40 * 2455777 * 2
def baseEnd_2455777 : Nat := 1260993981256543494893593

theorem tailTrace_2455777 : CollatzResearch.WordTrace tailWord_2455777 prefixEnd_2455777 1260993981256543494893593 := by
  unfold tailWord_2455777
  simp only [CollatzResearch.WordTrace]
  refine ⟨89569545624146817165509585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59713030416097878110339723 89569545624146817165509585)
  ·
    refine ⟨67177159218110112874132189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89569545624146817165509585 67177159218110112874132189)
    ·
      refine ⟨25191434706791292327799571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67177159218110112874132189 25191434706791292327799571)
      ·
        refine ⟨37787152060186938491699357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25191434706791292327799571 37787152060186938491699357)
        ·
          refine ⟨14170182022570101934387259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37787152060186938491699357 14170182022570101934387259)
          ·
            refine ⟨21255273033855152901580889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14170182022570101934387259 21255273033855152901580889)
            ·
              refine ⟨15941454775391364676185667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21255273033855152901580889 15941454775391364676185667)
              ·
                refine ⟨23912182163087047014278501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15941454775391364676185667 23912182163087047014278501)
                ·
                  refine ⟨4483534155578821315177219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23912182163087047014278501 4483534155578821315177219)
                  ·
                    refine ⟨6725301233368231972765829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4483534155578821315177219 6725301233368231972765829)
                    ·
                      refine ⟨1260993981256543494893593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6725301233368231972765829 1260993981256543494893593)
                      ·
                        rfl

theorem cell23_2455777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_2455777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455777 prefixEnd_2455777 := by exact prefixLift 2455777
  have htrace : WordTrace (prefixWord ++ tailWord_2455777) baseStart_2455777 baseEnd_2455777 := by
    simpa [prefixWord, tailWord_2455777, baseEnd_2455777] using wordTrace_append hprefix tailTrace_2455777
  have hstable : (prefixWord ++ tailWord_2455777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455777).length < 2 ^ (prefixWord ++ tailWord_2455777).sum := by decide
  have hdescent : baseEnd_2455777 < baseStart_2455777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455778 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 7]
def baseStart_2455778 : Nat := 118140960795 + 2455778 * 2 ^ 59
def prefixEnd_2455778 : Nat := 4983230072969 + 3 ^ 40 * 2455778 * 2
def baseEnd_2455778 : Nat := 140110499415244221220121

theorem tailTrace_2455778 : CollatzResearch.WordTrace tailWord_2455778 prefixEnd_2455778 140110499415244221220121 := by
  unfold tailWord_2455778
  simp only [CollatzResearch.WordTrace]
  refine ⟨22392395524285798584073997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59713054731428796224197325 22392395524285798584073997)
  ·
    refine ⟨8397148321607174469027749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22392395524285798584073997 8397148321607174469027749)
    ·
      refine ⟨1574465310301345212942703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8397148321607174469027749 1574465310301345212942703)
      ·
        refine ⟨2361697965452017819414055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574465310301345212942703 2361697965452017819414055)
        ·
          refine ⟨3542546948178026729121083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361697965452017819414055 3542546948178026729121083)
          ·
            refine ⟨5313820422267040093681625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542546948178026729121083 5313820422267040093681625)
            ·
              refine ⟨3985365316700280070261219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5313820422267040093681625 3985365316700280070261219)
              ·
                refine ⟨5978047975050420105391829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3985365316700280070261219 5978047975050420105391829)
                ·
                  refine ⟨140110499415244221220121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5978047975050420105391829 140110499415244221220121)
                  ·
                    rfl

theorem cell23_2455778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_2455778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455778 prefixEnd_2455778 := by exact prefixLift 2455778
  have htrace : WordTrace (prefixWord ++ tailWord_2455778) baseStart_2455778 baseEnd_2455778 := by
    simpa [prefixWord, tailWord_2455778, baseEnd_2455778] using wordTrace_append hprefix tailTrace_2455778
  have hstable : (prefixWord ++ tailWord_2455778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455778).length < 2 ^ (prefixWord ++ tailWord_2455778).sum := by decide
  have hdescent : baseEnd_2455778 < baseStart_2455778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455804 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 3, 4]
def baseStart_2455804 : Nat := 118140960795 + 2455804 * 2 ^ 59
def prefixEnd_2455804 : Nat := 4983230072969 + 3 ^ 40 * 2455804 * 2
def baseEnd_2455804 : Nat := 420335948411404963085323

theorem tailTrace_2455804 : CollatzResearch.WordTrace tailWord_2455804 prefixEnd_2455804 420335948411404963085323 := by
  unfold tailWord_2455804
  simp only [CollatzResearch.WordTrace]
  refine ⟨44785265197524500388371233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59713686930032667184494977 44785265197524500388371233)
  ·
    refine ⟨33588948898143375291278425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44785265197524500388371233 33588948898143375291278425)
    ·
      refine ⟨25191711673607531468458819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33588948898143375291278425 25191711673607531468458819)
      ·
        refine ⟨37787567510411297202688229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25191711673607531468458819 37787567510411297202688229)
        ·
          refine ⟨7085168908202118225504043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37787567510411297202688229 7085168908202118225504043)
          ·
            refine ⟨10627753362303177338256065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7085168908202118225504043 10627753362303177338256065)
            ·
              refine ⟨7970815021727383003692049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10627753362303177338256065 7970815021727383003692049)
              ·
                refine ⟨5978111266295537252769037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7970815021727383003692049 5978111266295537252769037)
                ·
                  refine ⟨2241791724860826469788389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5978111266295537252769037 2241791724860826469788389)
                  ·
                    refine ⟨420335948411404963085323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2241791724860826469788389 420335948411404963085323)
                    ·
                      rfl

theorem cell23_2455804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_2455804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455804 prefixEnd_2455804 := by exact prefixLift 2455804
  have htrace : WordTrace (prefixWord ++ tailWord_2455804) baseStart_2455804 baseEnd_2455804 := by
    simpa [prefixWord, tailWord_2455804, baseEnd_2455804] using wordTrace_append hprefix tailTrace_2455804
  have hstable : (prefixWord ++ tailWord_2455804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455804).length < 2 ^ (prefixWord ++ tailWord_2455804).sum := by decide
  have hdescent : baseEnd_2455804 < baseStart_2455804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455838 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2455838 : Nat := 118140960795 + 2455838 * 2 ^ 59
def prefixEnd_2455838 : Nat := 4983230072969 + 3 ^ 40 * 2455838 * 2
def baseEnd_2455838 : Nat := 420341767858822585410271

theorem tailTrace_2455838 : CollatzResearch.WordTrace tailWord_2455838 prefixEnd_2455838 420341767858822585410271 := by
  unfold tailWord_2455838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11196471309615728072935021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59714513651283883055653445 11196471309615728072935021)
  ·
    refine ⟨4198676741105898027350633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11196471309615728072935021 4198676741105898027350633)
    ·
      refine ⟨3149007555829423520512975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4198676741105898027350633 3149007555829423520512975)
      ·
        refine ⟨4723511333744135280769463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3149007555829423520512975 4723511333744135280769463)
        ·
          refine ⟨7085267000616202921154195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4723511333744135280769463 7085267000616202921154195)
          ·
            refine ⟨10627900500924304381731293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7085267000616202921154195 10627900500924304381731293)
            ·
              refine ⟨3985462687846614143149235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10627900500924304381731293 3985462687846614143149235)
              ·
                refine ⟨5978194031769921214723853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3985462687846614143149235 5978194031769921214723853)
                ·
                  refine ⟨2241822761913720455521445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5978194031769921214723853 2241822761913720455521445)
                  ·
                    refine ⟨420341767858822585410271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2241822761913720455521445 420341767858822585410271)
                    ·
                      rfl

theorem cell23_2455838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2455838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455838 prefixEnd_2455838 := by exact prefixLift 2455838
  have htrace : WordTrace (prefixWord ++ tailWord_2455838) baseStart_2455838 baseEnd_2455838 := by
    simpa [prefixWord, tailWord_2455838, baseEnd_2455838] using wordTrace_append hprefix tailTrace_2455838
  have hstable : (prefixWord ++ tailWord_2455838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455838).length < 2 ^ (prefixWord ++ tailWord_2455838).sum := by decide
  have hdescent : baseEnd_2455838 < baseStart_2455838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455864 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 1, 5]
def baseStart_2455864 : Nat := 118140960795 + 2455864 * 2 ^ 59
def prefixEnd_2455864 : Nat := 4983230072969 + 3 ^ 40 * 2455864 * 2
def baseEnd_2455864 : Nat := 420346218024494884835231

theorem tailTrace_2455864 : CollatzResearch.WordTrace tailWord_2455864 prefixEnd_2455864 420346218024494884835231 := by
  unfold tailWord_2455864
  simp only [CollatzResearch.WordTrace]
  refine ⟨44786359387415815511963323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59715145849887754015951097 44786359387415815511963323)
  ·
    refine ⟨67179539081123723267944985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44786359387415815511963323 67179539081123723267944985)
    ·
      refine ⟨50384654310842792450958739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67179539081123723267944985 50384654310842792450958739)
      ·
        refine ⟨75576981466264188676438109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50384654310842792450958739 75576981466264188676438109)
        ·
          refine ⟨28341368049849070753664291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75576981466264188676438109 28341368049849070753664291)
          ·
            refine ⟨42512052074773606130496437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28341368049849070753664291 42512052074773606130496437)
            ·
              refine ⟨3985504882010025574734041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42512052074773606130496437 3985504882010025574734041)
              ·
                refine ⟨2989128661507519181050531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3985504882010025574734041 2989128661507519181050531)
                ·
                  refine ⟨4483692992261278771575797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989128661507519181050531 4483692992261278771575797)
                  ·
                    refine ⟨420346218024494884835231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4483692992261278771575797 420346218024494884835231)
                    ·
                      rfl

theorem cell23_2455864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_2455864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455864 prefixEnd_2455864 := by exact prefixLift 2455864
  have htrace : WordTrace (prefixWord ++ tailWord_2455864) baseStart_2455864 baseEnd_2455864 := by
    simpa [prefixWord, tailWord_2455864, baseEnd_2455864] using wordTrace_append hprefix tailTrace_2455864
  have hstable : (prefixWord ++ tailWord_2455864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455864).length < 2 ^ (prefixWord ++ tailWord_2455864).sum := by decide
  have hdescent : baseEnd_2455864 < baseStart_2455864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455871 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 2, 3, 2]
def baseStart_2455871 : Nat := 118140960795 + 2455871 * 2 ^ 59
def prefixEnd_2455871 : Nat := 4983230072969 + 3 ^ 40 * 2455871 * 2
def baseEnd_2455871 : Nat := 1261042248438066127118161

theorem tailTrace_2455871 : CollatzResearch.WordTrace tailWord_2455871 prefixEnd_2455871 1261042248438066127118161 := by
  unfold tailWord_2455871
  simp only [CollatzResearch.WordTrace]
  refine ⟨89572974085806271219431467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59715316057204180812954311 89572974085806271219431467)
  ·
    refine ⟨134359461128709406829147201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89572974085806271219431467 134359461128709406829147201)
    ·
      refine ⟨100769595846532055121860401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134359461128709406829147201 100769595846532055121860401)
      ·
        refine ⟨75577196884899041341395301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100769595846532055121860401 75577196884899041341395301)
        ·
          refine ⟨14170724415918570251511619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75577196884899041341395301 14170724415918570251511619)
          ·
            refine ⟨21256086623877855377267429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14170724415918570251511619 21256086623877855377267429)
            ·
              refine ⟨3985516241977097883237643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21256086623877855377267429 3985516241977097883237643)
              ·
                refine ⟨5978274362965646824856465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3985516241977097883237643 5978274362965646824856465)
                ·
                  refine ⟨4483705772224235118642349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5978274362965646824856465 4483705772224235118642349)
                  ·
                    refine ⟨1681389664584088169490881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4483705772224235118642349 1681389664584088169490881)
                    ·
                      refine ⟨1261042248438066127118161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1681389664584088169490881 1261042248438066127118161)
                      ·
                        rfl

theorem cell23_2455871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 3, 2].length) (baseStart_2455871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455871 prefixEnd_2455871 := by exact prefixLift 2455871
  have htrace : WordTrace (prefixWord ++ tailWord_2455871) baseStart_2455871 baseEnd_2455871 := by
    simpa [prefixWord, tailWord_2455871, baseEnd_2455871] using wordTrace_append hprefix tailTrace_2455871
  have hstable : (prefixWord ++ tailWord_2455871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455871).length < 2 ^ (prefixWord ++ tailWord_2455871).sum := by decide
  have hdescent : baseEnd_2455871 < baseStart_2455871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455887 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 5]
def baseStart_2455887 : Nat := 118140960795 + 2455887 * 2 ^ 59
def prefixEnd_2455887 : Nat := 4983230072969 + 3 ^ 40 * 2455887 * 2
def baseEnd_2455887 : Nat := 1261050464128538064518087

theorem tailTrace_2455887 : CollatzResearch.WordTrace tailWord_2455887 prefixEnd_2455887 1261050464128538064518087 := by
  unfold tailWord_2455887
  simp only [CollatzResearch.WordTrace]
  refine ⟨89573557653748305952013915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59715705102498870634675943 89573557653748305952013915)
  ·
    refine ⟨134360336480622458928020873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89573557653748305952013915 134360336480622458928020873)
    ·
      refine ⟨100770252360466844196015655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134360336480622458928020873 100770252360466844196015655)
      ·
        refine ⟨151155378540700266294023483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100770252360466844196015655 151155378540700266294023483)
        ·
          refine ⟨226733067811050399441035225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151155378540700266294023483 226733067811050399441035225)
          ·
            refine ⟨170049800858287799580776419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226733067811050399441035225 170049800858287799580776419)
            ·
              refine ⟨255074701287431699371164629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170049800858287799580776419 255074701287431699371164629)
              ·
                refine ⟨5978313311424180454011671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 255074701287431699371164629 5978313311424180454011671)
                ·
                  refine ⟨8967469967136270681017507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5978313311424180454011671 8967469967136270681017507)
                  ·
                    refine ⟨13451204950704406021526261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8967469967136270681017507 13451204950704406021526261)
                    ·
                      refine ⟨1261050464128538064518087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13451204950704406021526261 1261050464128538064518087)
                      ·
                        rfl

theorem cell23_2455887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_2455887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455887 prefixEnd_2455887 := by exact prefixLift 2455887
  have htrace : WordTrace (prefixWord ++ tailWord_2455887) baseStart_2455887 baseEnd_2455887 := by
    simpa [prefixWord, tailWord_2455887, baseEnd_2455887] using wordTrace_append hprefix tailTrace_2455887
  have hstable : (prefixWord ++ tailWord_2455887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455887).length < 2 ^ (prefixWord ++ tailWord_2455887).sum := by decide
  have hdescent : baseEnd_2455887 < baseStart_2455887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455897 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 4]
def baseStart_2455897 : Nat := 118140960795 + 2455897 * 2 ^ 59
def prefixEnd_2455897 : Nat := 4983230072969 + 3 ^ 40 * 2455897 * 2
def baseEnd_2455897 : Nat := 1261055598935083025393041

theorem tailTrace_2455897 : CollatzResearch.WordTrace tailWord_2455897 prefixEnd_2455897 1261055598935083025393041 := by
  unfold tailWord_2455897
  simp only [CollatzResearch.WordTrace]
  refine ⟨89573922383712077659877945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59715948255808051773251963 89573922383712077659877945)
  ·
    refine ⟨67180441787784058244908459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89573922383712077659877945 67180441787784058244908459)
    ·
      refine ⟨100770662681676087367362689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67180441787784058244908459 100770662681676087367362689)
      ·
        refine ⟨75577997011257065525522017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100770662681676087367362689 75577997011257065525522017)
        ·
          refine ⟨56683497758442799144141513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75577997011257065525522017 56683497758442799144141513)
          ·
            refine ⟨42512623318832099358106135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56683497758442799144141513 42512623318832099358106135)
            ·
              refine ⟨63768934978248149037159203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42512623318832099358106135 63768934978248149037159203)
              ·
                refine ⟨95653402467372223555738805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63768934978248149037159203 95653402467372223555738805)
                ·
                  refine ⟨8967506481316145958350513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95653402467372223555738805 8967506481316145958350513)
                  ·
                    refine ⟨6725629860987109468762885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8967506481316145958350513 6725629860987109468762885)
                    ·
                      refine ⟨1261055598935083025393041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6725629860987109468762885 1261055598935083025393041)
                      ·
                        rfl

theorem cell23_2455897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_2455897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455897 prefixEnd_2455897 := by exact prefixLift 2455897
  have htrace : WordTrace (prefixWord ++ tailWord_2455897) baseStart_2455897 baseEnd_2455897 := by
    simpa [prefixWord, tailWord_2455897, baseEnd_2455897] using wordTrace_append hprefix tailTrace_2455897
  have hstable : (prefixWord ++ tailWord_2455897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455897).length < 2 ^ (prefixWord ++ tailWord_2455897).sum := by decide
  have hdescent : baseEnd_2455897 < baseStart_2455897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455911 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 2, 4]
def baseStart_2455911 : Nat := 118140960795 + 2455911 * 2 ^ 59
def prefixEnd_2455911 : Nat := 4983230072969 + 3 ^ 40 * 2455911 * 2
def baseEnd_2455911 : Nat := 420354262554748656872659

theorem tailTrace_2455911 : CollatzResearch.WordTrace tailWord_2455911 prefixEnd_2455911 420354262554748656872659 := by
  unfold tailWord_2455911
  simp only [CollatzResearch.WordTrace]
  refine ⟨89574433005661358050887587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59716288670440905367258391 89574433005661358050887587)
  ·
    refine ⟨134361649508492037076331381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89574433005661358050887587 134361649508492037076331381)
    ·
      refine ⟨12596404641421128475906067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134361649508492037076331381 12596404641421128475906067)
      ·
        refine ⟨18894606962131692713859101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12596404641421128475906067 18894606962131692713859101)
        ·
          refine ⟨7085477610799384767697163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18894606962131692713859101 7085477610799384767697163)
          ·
            refine ⟨10628216416199077151545745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7085477610799384767697163 10628216416199077151545745)
            ·
              refine ⟨7971162312149307863659309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10628216416199077151545745 7971162312149307863659309)
              ·
                refine ⟨2989185867055990448872241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7971162312149307863659309 2989185867055990448872241)
                ·
                  refine ⟨2241889400291992836654181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2989185867055990448872241 2241889400291992836654181)
                  ·
                    refine ⟨420354262554748656872659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2241889400291992836654181 420354262554748656872659)
                    ·
                      rfl

theorem cell23_2455911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_2455911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455911 prefixEnd_2455911 := by exact prefixLift 2455911
  have htrace : WordTrace (prefixWord ++ tailWord_2455911) baseStart_2455911 baseEnd_2455911 := by
    simpa [prefixWord, tailWord_2455911, baseEnd_2455911] using wordTrace_append hprefix tailTrace_2455911
  have hstable : (prefixWord ++ tailWord_2455911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455911).length < 2 ^ (prefixWord ++ tailWord_2455911).sum := by decide
  have hdescent : baseEnd_2455911 < baseStart_2455911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455977 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_2455977 : Nat := 118140960795 + 2455977 * 2 ^ 59
def prefixEnd_2455977 : Nat := 4983230072969 + 3 ^ 40 * 2455977 * 2
def baseEnd_2455977 : Nat := 1261096677387442712392673

theorem tailTrace_2455977 : CollatzResearch.WordTrace tailWord_2455977 prefixEnd_2455977 1261096677387442712392673 := by
  unfold tailWord_2455977
  simp only [CollatzResearch.WordTrace]
  refine ⟨89576840223422251322790185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59717893482281500881860123 89576840223422251322790185)
  ·
    refine ⟨67182630167566688492092639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89576840223422251322790185 67182630167566688492092639)
    ·
      refine ⟨100773945251350032738138959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67182630167566688492092639 100773945251350032738138959)
      ·
        refine ⟨151160917877025049107208439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100773945251350032738138959 151160917877025049107208439)
        ·
          refine ⟨226741376815537573660812659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151160917877025049107208439 226741376815537573660812659)
          ·
            refine ⟨340112065223306360491218989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226741376815537573660812659 340112065223306360491218989)
            ·
              refine ⟨127542024458739885184207121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 340112065223306360491218989 127542024458739885184207121)
              ·
                refine ⟨95656518344054913888155341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127542024458739885184207121 95656518344054913888155341)
                ·
                  refine ⟨35871194379020592708058253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95656518344054913888155341 35871194379020592708058253)
                  ·
                    refine ⟨13451697892132722265521845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35871194379020592708058253 13451697892132722265521845)
                    ·
                      refine ⟨1261096677387442712392673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13451697892132722265521845 1261096677387442712392673)
                      ·
                        rfl

theorem cell23_2455977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_2455977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2455977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2455977 prefixEnd_2455977 := by exact prefixLift 2455977
  have htrace : WordTrace (prefixWord ++ tailWord_2455977) baseStart_2455977 baseEnd_2455977 := by
    simpa [prefixWord, tailWord_2455977, baseEnd_2455977] using wordTrace_append hprefix tailTrace_2455977
  have hstable : (prefixWord ++ tailWord_2455977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455977).length < 2 ^ (prefixWord ++ tailWord_2455977).sum := by decide
  have hdescent : baseEnd_2455977 < baseStart_2455977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456008 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 4, 2, 2]
def baseStart_2456008 : Nat := 118140960795 + 2456008 * 2 ^ 59
def prefixEnd_2456008 : Nat := 4983230072969 + 3 ^ 40 * 2456008 * 2
def baseEnd_2456008 : Nat := 1261112595287732091105031

theorem tailTrace_2456008 : CollatzResearch.WordTrace tailWord_2456008 prefixEnd_2456008 1261112595287732091105031 := by
  unfold tailWord_2456008
  simp only [CollatzResearch.WordTrace]
  refine ⟨44788985443154971808584339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59718647257539962411445785 44788985443154971808584339)
  ·
    refine ⟨67183478164732457712876509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44788985443154971808584339 67183478164732457712876509)
    ·
      refine ⟨25193804311774671642328691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67183478164732457712876509 25193804311774671642328691)
      ·
        refine ⟨37790706467662007463493037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25193804311774671642328691 37790706467662007463493037)
        ·
          refine ⟨14171514925373252798809889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37790706467662007463493037 14171514925373252798809889)
          ·
            refine ⟨10628636194029939599107417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14171514925373252798809889 10628636194029939599107417)
            ·
              refine ⟨7971477145522454699330563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10628636194029939599107417 7971477145522454699330563)
              ·
                refine ⟨11957215718283682048995845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7971477145522454699330563 11957215718283682048995845)
                ·
                  refine ⟨2241977947178190384186721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11957215718283682048995845 2241977947178190384186721)
                  ·
                    refine ⟨1681483460383642788140041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2241977947178190384186721 1681483460383642788140041)
                    ·
                      refine ⟨1261112595287732091105031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1681483460383642788140041 1261112595287732091105031)
                      ·
                        rfl

theorem cell23_2456008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_2456008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456008 prefixEnd_2456008 := by exact prefixLift 2456008
  have htrace : WordTrace (prefixWord ++ tailWord_2456008) baseStart_2456008 baseEnd_2456008 := by
    simpa [prefixWord, tailWord_2456008, baseEnd_2456008] using wordTrace_append hprefix tailTrace_2456008
  have hstable : (prefixWord ++ tailWord_2456008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456008).length < 2 ^ (prefixWord ++ tailWord_2456008).sum := by decide
  have hdescent : baseEnd_2456008 < baseStart_2456008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456024 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 1, 5, 3]
def baseStart_2456024 : Nat := 118140960795 + 2456024 * 2 ^ 59
def prefixEnd_2456024 : Nat := 4983230072969 + 3 ^ 40 * 2456024 * 2
def baseEnd_2456024 : Nat := 1261120810978204028504957

theorem tailTrace_2456024 : CollatzResearch.WordTrace tailWord_2456024 prefixEnd_2456024 1261120810978204028504957 := by
  unfold tailWord_2456024
  simp only [CollatzResearch.WordTrace]
  refine ⟨44789277227125989174875563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59719036302834652233167417 44789277227125989174875563)
  ·
    refine ⟨67183915840688983762313345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44789277227125989174875563 67183915840688983762313345)
    ·
      refine ⟨50387936880516737821735009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67183915840688983762313345 50387936880516737821735009)
      ·
        refine ⟨37790952660387553366301257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50387936880516737821735009 37790952660387553366301257)
        ·
          refine ⟨28343214495290665024725943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37790952660387553366301257 28343214495290665024725943)
          ·
            refine ⟨42514821742935997537088915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28343214495290665024725943 42514821742935997537088915)
            ·
              refine ⟨63772232614403996305633373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42514821742935997537088915 63772232614403996305633373)
              ·
                refine ⟨23914587230401498614612515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63772232614403996305633373 23914587230401498614612515)
                ·
                  refine ⟨35871880845602247921918773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23914587230401498614612515 35871880845602247921918773)
                  ·
                    refine ⟨3362988829275210742679885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35871880845602247921918773 3362988829275210742679885)
                    ·
                      refine ⟨1261120810978204028504957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3362988829275210742679885 1261120810978204028504957)
                      ·
                        rfl

theorem cell23_2456024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_2456024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456024 prefixEnd_2456024 := by exact prefixLift 2456024
  have htrace : WordTrace (prefixWord ++ tailWord_2456024) baseStart_2456024 baseEnd_2456024 := by
    simpa [prefixWord, tailWord_2456024, baseEnd_2456024] using wordTrace_append hprefix tailTrace_2456024
  have hstable : (prefixWord ++ tailWord_2456024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456024).length < 2 ^ (prefixWord ++ tailWord_2456024).sum := by decide
  have hdescent : baseEnd_2456024 < baseStart_2456024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456065 : List Nat := [1, 2, 4, 1, 3, 3, 2, 2, 5]
def baseStart_2456065 : Nat := 118140960795 + 2456065 * 2 ^ 59
def prefixEnd_2456065 : Nat := 4983230072969 + 3 ^ 40 * 2456065 * 2
def baseEnd_2456065 : Nat := 140126873742782040899141

theorem tailTrace_2456065 : CollatzResearch.WordTrace tailWord_2456065 prefixEnd_2456065 140126873742782040899141 := by
  unfold tailWord_2456065
  simp only [CollatzResearch.WordTrace]
  refine ⟨89580049847103442351993649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59720033231402294901329099 89580049847103442351993649)
  ·
    refine ⟨67185037385327581763995237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89580049847103442351993649 67185037385327581763995237)
    ·
      refine ⟨12597194509748921580749107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67185037385327581763995237 12597194509748921580749107)
      ·
        refine ⟨18895791764623382371123661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12597194509748921580749107 18895791764623382371123661)
        ·
          refine ⟨7085921911733768389171373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18895791764623382371123661 7085921911733768389171373)
          ·
            refine ⟨2657220716900163145939265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7085921911733768389171373 2657220716900163145939265)
            ·
              refine ⟨1992915537675122359454449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2657220716900163145939265 1992915537675122359454449)
              ·
                refine ⟨1494686653256341769590837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1992915537675122359454449 1494686653256341769590837)
                ·
                  refine ⟨140126873742782040899141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1494686653256341769590837 140126873742782040899141)
                  ·
                    rfl

theorem cell23_2456065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 5].length) (baseStart_2456065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456065 prefixEnd_2456065 := by exact prefixLift 2456065
  have htrace : WordTrace (prefixWord ++ tailWord_2456065) baseStart_2456065 baseEnd_2456065 := by
    simpa [prefixWord, tailWord_2456065, baseEnd_2456065] using wordTrace_append hprefix tailTrace_2456065
  have hstable : (prefixWord ++ tailWord_2456065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456065).length < 2 ^ (prefixWord ++ tailWord_2456065).sum := by decide
  have hdescent : baseEnd_2456065 < baseStart_2456065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456068 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_2456068 : Nat := 118140960795 + 2456068 * 2 ^ 59
def prefixEnd_2456068 : Nat := 4983230072969 + 3 ^ 40 * 2456068 * 2
def baseEnd_2456068 : Nat := 1261143404127001856354755

theorem tailTrace_2456068 : CollatzResearch.WordTrace tailWord_2456068 prefixEnd_2456068 1261143404127001856354755 := by
  unfold tailWord_2456068
  simp only [CollatzResearch.WordTrace]
  refine ⟨44790079633046286932176429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59720106177395049242901905 44790079633046286932176429)
  ·
    refine ⟨16796279862392357599566161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44790079633046286932176429 16796279862392357599566161)
    ·
      refine ⟨12597209896794268199674621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16796279862392357599566161 12597209896794268199674621)
      ·
        refine ⟨4723953711297850574877983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12597209896794268199674621 4723953711297850574877983)
        ·
          refine ⟨7085930566946775862316975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4723953711297850574877983 7085930566946775862316975)
          ·
            refine ⟨10628895850420163793475463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7085930566946775862316975 10628895850420163793475463)
            ·
              refine ⟨15943343775630245690213195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10628895850420163793475463 15943343775630245690213195)
              ·
                refine ⟨23915015663445368535319793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15943343775630245690213195 23915015663445368535319793)
                ·
                  refine ⟨17936261747584026401489845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23915015663445368535319793 17936261747584026401489845)
                  ·
                    refine ⟨1681524538836002475139673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17936261747584026401489845 1681524538836002475139673)
                    ·
                      refine ⟨1261143404127001856354755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1681524538836002475139673 1261143404127001856354755)
                      ·
                        rfl

theorem cell23_2456068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_2456068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456068 prefixEnd_2456068 := by exact prefixLift 2456068
  have htrace : WordTrace (prefixWord ++ tailWord_2456068) baseStart_2456068 baseEnd_2456068 := by
    simpa [prefixWord, tailWord_2456068, baseEnd_2456068] using wordTrace_append hprefix tailTrace_2456068
  have hstable : (prefixWord ++ tailWord_2456068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456068).length < 2 ^ (prefixWord ++ tailWord_2456068).sum := by decide
  have hdescent : baseEnd_2456068 < baseStart_2456068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456125 : List Nat := [1, 4, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_2456125 : Nat := 118140960795 + 2456125 * 2 ^ 59
def prefixEnd_2456125 : Nat := 4983230072969 + 3 ^ 40 * 2456125 * 2
def baseEnd_2456125 : Nat := 420390890841436044447331

theorem tailTrace_2456125 : CollatzResearch.WordTrace tailWord_2456125 prefixEnd_2456125 420390890841436044447331 := by
  unfold tailWord_2456125
  simp only [CollatzResearch.WordTrace]
  refine ⟨89582238226886072599177829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59721492151257381732785219 89582238226886072599177829)
  ·
    refine ⟨16796669667541138612345843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89582238226886072599177829 16796669667541138612345843)
    ·
      refine ⟨25195004501311707918518765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16796669667541138612345843 25195004501311707918518765)
      ·
        refine ⟨9448126687991890469444537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25195004501311707918518765 9448126687991890469444537)
        ·
          refine ⟨7086095015993917852083403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9448126687991890469444537 7086095015993917852083403)
          ·
            refine ⟨10629142523990876778125105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7086095015993917852083403 10629142523990876778125105)
            ·
              refine ⟨7971856892993157583593829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10629142523990876778125105 7971856892993157583593829)
              ·
                refine ⟨1494723167436217046923843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7971856892993157583593829 1494723167436217046923843)
                ·
                  refine ⟨2242084751154325570385765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494723167436217046923843 2242084751154325570385765)
                  ·
                    refine ⟨420390890841436044447331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2242084751154325570385765 420390890841436044447331)
                    ·
                      rfl

theorem cell23_2456125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_2456125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456125 prefixEnd_2456125 := by exact prefixLift 2456125
  have htrace : WordTrace (prefixWord ++ tailWord_2456125) baseStart_2456125 baseEnd_2456125 := by
    simpa [prefixWord, tailWord_2456125, baseEnd_2456125] using wordTrace_append hprefix tailTrace_2456125
  have hstable : (prefixWord ++ tailWord_2456125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456125).length < 2 ^ (prefixWord ++ tailWord_2456125).sum := by decide
  have hdescent : baseEnd_2456125 < baseStart_2456125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456138 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 6]
def baseStart_2456138 : Nat := 118140960795 + 2456138 * 2 ^ 59
def prefixEnd_2456138 : Nat := 4983230072969 + 3 ^ 40 * 2456138 * 2
def baseEnd_2456138 : Nat := 140131038641424064719937

theorem tailTrace_2456138 : CollatzResearch.WordTrace tailWord_2456138 prefixEnd_2456138 140131038641424064719937 := by
  unfold tailWord_2456138
  simp only [CollatzResearch.WordTrace]
  refine ⟨22395678093959743954850267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59721808250559317212934045 22395678093959743954850267)
  ·
    refine ⟨33593517140939615932275401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22395678093959743954850267 33593517140939615932275401)
    ·
      refine ⟨25195137855704711949206551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33593517140939615932275401 25195137855704711949206551)
      ·
        refine ⟨37792706783557067923809827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25195137855704711949206551 37792706783557067923809827)
        ·
          refine ⟨56689060175335601885714741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37792706783557067923809827 56689060175335601885714741)
          ·
            refine ⟨5314599391437712676785757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56689060175335601885714741 5314599391437712676785757)
            ·
              refine ⟨1992974771789142253794659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5314599391437712676785757 1992974771789142253794659)
              ·
                refine ⟨2989462157683713380691989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1992974771789142253794659 2989462157683713380691989)
                ·
                  refine ⟨140131038641424064719937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2989462157683713380691989 140131038641424064719937)
                  ·
                    rfl

theorem cell23_2456138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_2456138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456138 prefixEnd_2456138 := by exact prefixLift 2456138
  have htrace : WordTrace (prefixWord ++ tailWord_2456138) baseStart_2456138 baseEnd_2456138 := by
    simpa [prefixWord, tailWord_2456138, baseEnd_2456138] using wordTrace_append hprefix tailTrace_2456138
  have hstable : (prefixWord ++ tailWord_2456138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456138).length < 2 ^ (prefixWord ++ tailWord_2456138).sum := by decide
  have hdescent : baseEnd_2456138 < baseStart_2456138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456201 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 4]
def baseStart_2456201 : Nat := 118140960795 + 2456201 * 2 ^ 59
def prefixEnd_2456201 : Nat := 4983230072969 + 3 ^ 40 * 2456201 * 2
def baseEnd_2456201 : Nat := 1261211697054049835991643

theorem tailTrace_2456201 : CollatzResearch.WordTrace tailWord_2456201 prefixEnd_2456201 1261211697054049835991643 := by
  unfold tailWord_2456201
  simp only [CollatzResearch.WordTrace]
  refine ⟨89585010174610737578944457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59723340116407158385962971 89585010174610737578944457)
  ·
    refine ⟨67188757630958053184208343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89585010174610737578944457 67188757630958053184208343)
    ·
      refine ⟨100783136446437079776312515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67188757630958053184208343 100783136446437079776312515)
      ·
        refine ⟨151174704669655619664468773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100783136446437079776312515 151174704669655619664468773)
        ·
          refine ⟨28345257125560428687087895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151174704669655619664468773 28345257125560428687087895)
          ·
            refine ⟨42517885688340643030631843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28345257125560428687087895 42517885688340643030631843)
            ·
              refine ⟨63776828532510964545947765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42517885688340643030631843 63776828532510964545947765)
              ·
                refine ⟨5979077674922902926182603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63776828532510964545947765 5979077674922902926182603)
                ·
                  refine ⟨8968616512384354389273905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5979077674922902926182603 8968616512384354389273905)
                  ·
                    refine ⟨6726462384288265791955429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8968616512384354389273905 6726462384288265791955429)
                    ·
                      refine ⟨1261211697054049835991643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6726462384288265791955429 1261211697054049835991643)
                      ·
                        rfl

theorem cell23_2456201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_2456201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456201 prefixEnd_2456201 := by exact prefixLift 2456201
  have htrace : WordTrace (prefixWord ++ tailWord_2456201) baseStart_2456201 baseEnd_2456201 := by
    simpa [prefixWord, tailWord_2456201, baseEnd_2456201] using wordTrace_append hprefix tailTrace_2456201
  have hstable : (prefixWord ++ tailWord_2456201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456201).length < 2 ^ (prefixWord ++ tailWord_2456201).sum := by decide
  have hdescent : baseEnd_2456201 < baseStart_2456201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456202 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 1, 5]
def baseStart_2456202 : Nat := 118140960795 + 2456202 * 2 ^ 59
def prefixEnd_2456202 : Nat := 4983230072969 + 3 ^ 40 * 2456202 * 2
def baseEnd_2456202 : Nat := 420404070178234777359713

theorem tailTrace_2456202 : CollatzResearch.WordTrace tailWord_2456202 prefixEnd_2456202 420404070178234777359713 := by
  unfold tailWord_2456202
  simp only [CollatzResearch.WordTrace]
  refine ⟨22396261661901778687432715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59723364431738076499820573 22396261661901778687432715)
  ·
    refine ⟨33594392492852668031149073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22396261661901778687432715 33594392492852668031149073)
    ·
      refine ⟨25195794369639501023361805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33594392492852668031149073 25195794369639501023361805)
      ·
        refine ⟨9448422888614812883760677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25195794369639501023361805 9448422888614812883760677)
        ·
          refine ⟨1771579291615277415705127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9448422888614812883760677 1771579291615277415705127)
          ·
            refine ⟨2657368937422916123557691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771579291615277415705127 2657368937422916123557691)
            ·
              refine ⟨3986053406134374185336537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657368937422916123557691 3986053406134374185336537)
              ·
                refine ⟨2989540054600780639002403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3986053406134374185336537 2989540054600780639002403)
                ·
                  refine ⟨4484310081901170958503605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989540054600780639002403 4484310081901170958503605)
                  ·
                    refine ⟨420404070178234777359713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4484310081901170958503605 420404070178234777359713)
                    ·
                      rfl

theorem cell23_2456202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_2456202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456202 prefixEnd_2456202 := by exact prefixLift 2456202
  have htrace : WordTrace (prefixWord ++ tailWord_2456202) baseStart_2456202 baseEnd_2456202 := by
    simpa [prefixWord, tailWord_2456202, baseEnd_2456202] using wordTrace_append hprefix tailTrace_2456202
  have hstable : (prefixWord ++ tailWord_2456202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456202).length < 2 ^ (prefixWord ++ tailWord_2456202).sum := by decide
  have hdescent : baseEnd_2456202 < baseStart_2456202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456222 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_2456222 : Nat := 118140960795 + 2456222 * 2 ^ 59
def prefixEnd_2456222 : Nat := 4983230072969 + 3 ^ 40 * 2456222 * 2
def baseEnd_2456222 : Nat := 1261222480147794253829047

theorem tailTrace_2456222 : CollatzResearch.WordTrace tailWord_2456222 prefixEnd_2456222 1261222480147794253829047 := by
  unfold tailWord_2456222
  simp only [CollatzResearch.WordTrace]
  refine ⟨11198222013441832270682365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59723850738356438776972613 11198222013441832270682365)
  ·
    refine ⟨4199333255040687101505887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11198222013441832270682365 4199333255040687101505887)
    ·
      refine ⟨6298999882561030652258831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4199333255040687101505887 6298999882561030652258831)
      ·
        refine ⟨9448499823841545978388247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6298999882561030652258831 9448499823841545978388247)
        ·
          refine ⟨14172749735762318967582371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9448499823841545978388247 14172749735762318967582371)
          ·
            refine ⟨21259124603643478451373557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14172749735762318967582371 21259124603643478451373557)
            ·
              refine ⟨1993042931591576104816271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21259124603643478451373557 1993042931591576104816271)
              ·
                refine ⟨2989564397387364157224407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993042931591576104816271 2989564397387364157224407)
                ·
                  refine ⟨4484346596081046235836611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989564397387364157224407 4484346596081046235836611)
                  ·
                    refine ⟨6726519894121569353754917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4484346596081046235836611 6726519894121569353754917)
                    ·
                      refine ⟨1261222480147794253829047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6726519894121569353754917 1261222480147794253829047)
                      ·
                        rfl

theorem cell23_2456222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_2456222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456222 prefixEnd_2456222 := by exact prefixLift 2456222
  have htrace : WordTrace (prefixWord ++ tailWord_2456222) baseStart_2456222 baseEnd_2456222 := by
    simpa [prefixWord, tailWord_2456222, baseEnd_2456222] using wordTrace_append hprefix tailTrace_2456222
  have hstable : (prefixWord ++ tailWord_2456222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456222).length < 2 ^ (prefixWord ++ tailWord_2456222).sum := by decide
  have hdescent : baseEnd_2456222 < baseStart_2456222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456225 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_2456225 : Nat := 118140960795 + 2456225 * 2 ^ 59
def prefixEnd_2456225 : Nat := 4983230072969 + 3 ^ 40 * 2456225 * 2
def baseEnd_2456225 : Nat := 1261224020589757742091533

theorem tailTrace_2456225 : CollatzResearch.WordTrace tailWord_2456225 prefixEnd_2456225 1261224020589757742091533 := by
  unfold tailWord_2456225
  simp only [CollatzResearch.WordTrace]
  refine ⟨89585885526523789677818129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59723923684349193118545419 89585885526523789677818129)
  ·
    refine ⟨67189414144892842258363597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89585885526523789677818129 67189414144892842258363597)
    ·
      refine ⟨25196030304334815846886349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67189414144892842258363597 25196030304334815846886349)
      ·
        refine ⟨9448511364125555942582381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25196030304334815846886349 9448511364125555942582381)
        ·
          refine ⟨3543191761547083478468393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9448511364125555942582381 3543191761547083478468393)
          ·
            refine ⟨2657393821160312608851295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3543191761547083478468393 2657393821160312608851295)
            ·
              refine ⟨3986090731740468913276943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657393821160312608851295 3986090731740468913276943)
              ·
                refine ⟨5979136097610703369915415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3986090731740468913276943 5979136097610703369915415)
                ·
                  refine ⟨8968704146416055054873123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5979136097610703369915415 8968704146416055054873123)
                  ·
                    refine ⟨13453056219624082582309685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8968704146416055054873123 13453056219624082582309685)
                    ·
                      refine ⟨1261224020589757742091533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13453056219624082582309685 1261224020589757742091533)
                      ·
                        rfl

theorem cell23_2456225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_2456225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456225 prefixEnd_2456225 := by exact prefixLift 2456225
  have htrace : WordTrace (prefixWord ++ tailWord_2456225) baseStart_2456225 baseEnd_2456225 := by
    simpa [prefixWord, tailWord_2456225, baseEnd_2456225] using wordTrace_append hprefix tailTrace_2456225
  have hstable : (prefixWord ++ tailWord_2456225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456225).length < 2 ^ (prefixWord ++ tailWord_2456225).sum := by decide
  have hdescent : baseEnd_2456225 < baseStart_2456225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456239 : List Nat := [1, 1, 2, 1, 2, 5, 4, 2, 1, 2, 2]
def baseStart_2456239 : Nat := 118140960795 + 2456239 * 2 ^ 59
def prefixEnd_2456239 : Nat := 4983230072969 + 3 ^ 40 * 2456239 * 2
def baseEnd_2456239 : Nat := 1261231209318920687316469

theorem tailTrace_2456239 : CollatzResearch.WordTrace tailWord_2456239 prefixEnd_2456239 1261231209318920687316469 := by
  unfold tailWord_2456239
  simp only [CollatzResearch.WordTrace]
  refine ⟨89586396148473070068827771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59724264098982046712551847 89586396148473070068827771)
  ·
    refine ⟨134379594222709605103241657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89586396148473070068827771 134379594222709605103241657)
    ·
      refine ⟨100784695667032203827431243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134379594222709605103241657 100784695667032203827431243)
      ·
        refine ⟨151177043500548305741146865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100784695667032203827431243 151177043500548305741146865)
        ·
          refine ⟨113382782625411229305860149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151177043500548305741146865 113382782625411229305860149)
          ·
            refine ⟨10629635871132302747424389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113382782625411229305860149 10629635871132302747424389)
            ·
              refine ⟨1993056725837306765142073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10629635871132302747424389 1993056725837306765142073)
              ·
                refine ⟨1494792544377980073856555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993056725837306765142073 1494792544377980073856555)
                ·
                  refine ⟨2242188816566970110784833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494792544377980073856555 2242188816566970110784833)
                  ·
                    refine ⟨1681641612425227583088625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2242188816566970110784833 1681641612425227583088625)
                    ·
                      refine ⟨1261231209318920687316469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1681641612425227583088625 1261231209318920687316469)
                      ·
                        rfl

theorem cell23_2456239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 1, 2, 2].length) (baseStart_2456239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456239 prefixEnd_2456239 := by exact prefixLift 2456239
  have htrace : WordTrace (prefixWord ++ tailWord_2456239) baseStart_2456239 baseEnd_2456239 := by
    simpa [prefixWord, tailWord_2456239, baseEnd_2456239] using wordTrace_append hprefix tailTrace_2456239
  have hstable : (prefixWord ++ tailWord_2456239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456239).length < 2 ^ (prefixWord ++ tailWord_2456239).sum := by decide
  have hdescent : baseEnd_2456239 < baseStart_2456239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456255 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 2, 1, 3]
def baseStart_2456255 : Nat := 118140960795 + 2456255 * 2 ^ 59
def prefixEnd_2456255 : Nat := 4983230072969 + 3 ^ 40 * 2456255 * 2
def baseEnd_2456255 : Nat := 1261239425009392624716395

theorem tailTrace_2456255 : CollatzResearch.WordTrace tailWord_2456255 prefixEnd_2456255 1261239425009392624716395 := by
  unfold tailWord_2456255
  simp only [CollatzResearch.WordTrace]
  refine ⟨89586979716415104801410219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59724653144276736534273479 89586979716415104801410219)
  ·
    refine ⟨134380469574622657202115329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89586979716415104801410219 134380469574622657202115329)
    ·
      refine ⟨100785352180966992901586497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134380469574622657202115329 100785352180966992901586497)
      ·
        refine ⟨75589014135725244676189873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100785352180966992901586497 75589014135725244676189873)
        ·
          refine ⟨56691760601793933507142405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75589014135725244676189873 56691760601793933507142405)
          ·
            refine ⟨10629705112836362532589201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56691760601793933507142405 10629705112836362532589201)
            ·
              refine ⟨7972278834627271899441901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10629705112836362532589201 7972278834627271899441901)
              ·
                refine ⟨2989604562985226962290713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7972278834627271899441901 2989604562985226962290713)
                ·
                  refine ⟨2242203422238920221718035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2989604562985226962290713 2242203422238920221718035)
                  ·
                    refine ⟨3363305133358380332577053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2242203422238920221718035 3363305133358380332577053)
                    ·
                      refine ⟨1261239425009392624716395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3363305133358380332577053 1261239425009392624716395)
                      ·
                        rfl

theorem cell23_2456255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_2456255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456255 prefixEnd_2456255 := by exact prefixLift 2456255
  have htrace : WordTrace (prefixWord ++ tailWord_2456255) baseStart_2456255 baseEnd_2456255 := by
    simpa [prefixWord, tailWord_2456255, baseEnd_2456255] using wordTrace_append hprefix tailTrace_2456255
  have hstable : (prefixWord ++ tailWord_2456255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456255).length < 2 ^ (prefixWord ++ tailWord_2456255).sum := by decide
  have hdescent : baseEnd_2456255 < baseStart_2456255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456276 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2456276 : Nat := 118140960795 + 2456276 * 2 ^ 59
def prefixEnd_2456276 : Nat := 4983230072969 + 3 ^ 40 * 2456276 * 2
def baseEnd_2456276 : Nat := 1261250208103137042553799

theorem tailTrace_2456276 : CollatzResearch.WordTrace tailWord_2456276 prefixEnd_2456276 1261250208103137042553799 := by
  unfold tailWord_2456276
  simp only [CollatzResearch.WordTrace]
  refine ⟨44793872824669512693962341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59725163766226016925283121 44793872824669512693962341)
  ·
    refine ⟨8398851154625533630117939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44793872824669512693962341 8398851154625533630117939)
    ·
      refine ⟨12598276731938300445176909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8398851154625533630117939 12598276731938300445176909)
      ·
        refine ⟨4724353774476862666941341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12598276731938300445176909 4724353774476862666941341)
        ·
          refine ⟨1771632665428823500103003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4724353774476862666941341 1771632665428823500103003)
          ·
            refine ⟨2657448998143235250154505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771632665428823500103003 2657448998143235250154505)
            ·
              refine ⟨1993086748607426437615879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2657448998143235250154505 1993086748607426437615879)
              ·
                refine ⟨2989630122911139656423819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993086748607426437615879 2989630122911139656423819)
                ·
                  refine ⟨4484445184366709484635729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989630122911139656423819 4484445184366709484635729)
                  ·
                    refine ⟨3363333888275032113476797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4484445184366709484635729 3363333888275032113476797)
                    ·
                      refine ⟨1261250208103137042553799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3363333888275032113476797 1261250208103137042553799)
                      ·
                        rfl

theorem cell23_2456276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2456276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456276 prefixEnd_2456276 := by exact prefixLift 2456276
  have htrace : WordTrace (prefixWord ++ tailWord_2456276) baseStart_2456276 baseEnd_2456276 := by
    simpa [prefixWord, tailWord_2456276, baseEnd_2456276] using wordTrace_append hprefix tailTrace_2456276
  have hstable : (prefixWord ++ tailWord_2456276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456276).length < 2 ^ (prefixWord ++ tailWord_2456276).sum := by decide
  have hdescent : baseEnd_2456276 < baseStart_2456276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456281 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_2456281 : Nat := 118140960795 + 2456281 * 2 ^ 59
def prefixEnd_2456281 : Nat := 4983230072969 + 3 ^ 40 * 2456281 * 2
def baseEnd_2456281 : Nat := 1261252775506409522991275

theorem tailTrace_2456281 : CollatzResearch.WordTrace tailWord_2456281 prefixEnd_2456281 1261252775506409522991275 := by
  unfold tailWord_2456281
  simp only [CollatzResearch.WordTrace]
  refine ⟨89587928014320911241856697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59725285342880607494571131 89587928014320911241856697)
  ·
    refine ⟨67190946010740683431392523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89587928014320911241856697 67190946010740683431392523)
    ·
      refine ⟨100786419016111025147088785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67190946010740683431392523 100786419016111025147088785)
      ·
        refine ⟨75589814262083268860316589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100786419016111025147088785 75589814262083268860316589)
        ·
          refine ⟨28346180348281225822618721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75589814262083268860316589 28346180348281225822618721)
          ·
            refine ⟨21259635261210919366964041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28346180348281225822618721 21259635261210919366964041)
            ·
              refine ⟨15944726445908189525223031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21259635261210919366964041 15944726445908189525223031)
              ·
                refine ⟨23917089668862284287834547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15944726445908189525223031 23917089668862284287834547)
                ·
                  refine ⟨35875634503293426431751821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23917089668862284287834547 35875634503293426431751821)
                  ·
                    refine ⟨13453362938735034911906933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35875634503293426431751821 13453362938735034911906933)
                    ·
                      refine ⟨1261252775506409522991275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13453362938735034911906933 1261252775506409522991275)
                      ·
                        rfl

theorem cell23_2456281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_2456281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456281 prefixEnd_2456281 := by exact prefixLift 2456281
  have htrace : WordTrace (prefixWord ++ tailWord_2456281) baseStart_2456281 baseEnd_2456281 := by
    simpa [prefixWord, tailWord_2456281, baseEnd_2456281] using wordTrace_append hprefix tailTrace_2456281
  have hstable : (prefixWord ++ tailWord_2456281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456281).length < 2 ^ (prefixWord ++ tailWord_2456281).sum := by decide
  have hdescent : baseEnd_2456281 < baseStart_2456281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456348 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_2456348 : Nat := 118140960795 + 2456348 * 2 ^ 59
def prefixEnd_2456348 : Nat := 4983230072969 + 3 ^ 40 * 2456348 * 2
def baseEnd_2456348 : Nat := 420429059570086920284489

theorem tailTrace_2456348 : CollatzResearch.WordTrace tailWord_2456348 prefixEnd_2456348 420429059570086920284489 := by
  unfold tailWord_2456348
  simp only [CollatzResearch.WordTrace]
  refine ⟨44795185852539090842272849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59726914470052121123030465 44795185852539090842272849)
  ·
    refine ⟨33596389389404318131704637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44795185852539090842272849 33596389389404318131704637)
    ·
      refine ⟨12598646021026619299389239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33596389389404318131704637 12598646021026619299389239)
      ·
        refine ⟨18897969031539928949083859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12598646021026619299389239 18897969031539928949083859)
        ·
          refine ⟨28346953547309893423625789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18897969031539928949083859 28346953547309893423625789)
          ·
            refine ⟨10630107580241210033859671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28346953547309893423625789 10630107580241210033859671)
            ·
              refine ⟨15945161370361815050789507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10630107580241210033859671 15945161370361815050789507)
              ·
                refine ⟨23917742055542722576184261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15945161370361815050789507 23917742055542722576184261)
                ·
                  refine ⟨4484576635414260483034549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23917742055542722576184261 4484576635414260483034549)
                  ·
                    refine ⟨420429059570086920284489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4484576635414260483034549 420429059570086920284489)
                    ·
                      rfl

theorem cell23_2456348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_2456348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456348 prefixEnd_2456348 := by exact prefixLift 2456348
  have htrace : WordTrace (prefixWord ++ tailWord_2456348) baseStart_2456348 baseEnd_2456348 := by
    simpa [prefixWord, tailWord_2456348, baseEnd_2456348] using wordTrace_append hprefix tailTrace_2456348
  have hstable : (prefixWord ++ tailWord_2456348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456348).length < 2 ^ (prefixWord ++ tailWord_2456348).sum := by decide
  have hdescent : baseEnd_2456348 < baseStart_2456348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456352 : List Nat := [2, 1, 1, 5, 1, 3, 3, 2, 5]
def baseStart_2456352 : Nat := 118140960795 + 2456352 * 2 ^ 59
def prefixEnd_2456352 : Nat := 4983230072969 + 3 ^ 40 * 2456352 * 2
def baseEnd_2456352 : Nat := 140143248070319860578161

theorem tailTrace_2456352 : CollatzResearch.WordTrace tailWord_2456352 prefixEnd_2456352 140143248070319860578161 := by
  unfold tailWord_2456352
  simp only [CollatzResearch.WordTrace]
  refine ⟨44795258798531845183845655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59727011731375793578460873 44795258798531845183845655)
  ·
    refine ⟨67192888197797767775768483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44795258798531845183845655 67192888197797767775768483)
    ·
      refine ⟨100789332296696651663652725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67192888197797767775768483 100789332296696651663652725)
      ·
        refine ⟨9448999902815311093467443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100789332296696651663652725 9448999902815311093467443)
        ·
          refine ⟨14173499854222966640201165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9448999902815311093467443 14173499854222966640201165)
          ·
            refine ⟨5315062445333612490075437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14173499854222966640201165 5315062445333612490075437)
            ·
              refine ⟨1993148417000104683778289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5315062445333612490075437 1993148417000104683778289)
              ·
                refine ⟨1494861312750078512833717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993148417000104683778289 1494861312750078512833717)
                ·
                  refine ⟨140143248070319860578161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1494861312750078512833717 140143248070319860578161)
                  ·
                    rfl

theorem cell23_2456352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 5].length) (baseStart_2456352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456352 prefixEnd_2456352 := by exact prefixLift 2456352
  have htrace : WordTrace (prefixWord ++ tailWord_2456352) baseStart_2456352 baseEnd_2456352 := by
    simpa [prefixWord, tailWord_2456352, baseEnd_2456352] using wordTrace_append hprefix tailTrace_2456352
  have hstable : (prefixWord ++ tailWord_2456352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456352).length < 2 ^ (prefixWord ++ tailWord_2456352).sum := by decide
  have hdescent : baseEnd_2456352 < baseStart_2456352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456382 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_2456382 : Nat := 118140960795 + 2456382 * 2 ^ 59
def prefixEnd_2456382 : Nat := 4983230072969 + 3 ^ 40 * 2456382 * 2
def baseEnd_2456382 : Nat := 420434879017504542609437

theorem tailTrace_2456382 : CollatzResearch.WordTrace tailWord_2456382 prefixEnd_2456382 420434879017504542609437 := by
  unfold tailWord_2456382
  simp only [CollatzResearch.WordTrace]
  refine ⟨11198951473369375686410425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59727741191303336994188933 11198951473369375686410425)
  ·
    refine ⟨8399213605027031764807819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11198951473369375686410425 8399213605027031764807819)
    ·
      refine ⟨12598820407540547647211729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8399213605027031764807819 12598820407540547647211729)
      ·
        refine ⟨9449115305655410735408797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12598820407540547647211729 9449115305655410735408797)
        ·
          refine ⟨3543418239620779025778299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9449115305655410735408797 3543418239620779025778299)
          ·
            refine ⟨5315127359431168538667449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543418239620779025778299 5315127359431168538667449)
            ·
              refine ⟨3986345519573376404000587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5315127359431168538667449 3986345519573376404000587)
              ·
                refine ⟨5979518279360064606000881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3986345519573376404000587 5979518279360064606000881)
                ·
                  refine ⟨4484638709520048454500661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5979518279360064606000881 4484638709520048454500661)
                  ·
                    refine ⟨420434879017504542609437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4484638709520048454500661 420434879017504542609437)
                    ·
                      rfl

theorem cell23_2456382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_2456382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456382 prefixEnd_2456382 := by exact prefixLift 2456382
  have htrace : WordTrace (prefixWord ++ tailWord_2456382) baseStart_2456382 baseEnd_2456382 := by
    simpa [prefixWord, tailWord_2456382, baseEnd_2456382] using wordTrace_append hprefix tailTrace_2456382
  have hstable : (prefixWord ++ tailWord_2456382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456382).length < 2 ^ (prefixWord ++ tailWord_2456382).sum := by decide
  have hdescent : baseEnd_2456382 < baseStart_2456382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456405 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_2456405 : Nat := 118140960795 + 2456405 * 2 ^ 59
def prefixEnd_2456405 : Nat := 4983230072969 + 3 ^ 40 * 2456405 * 2
def baseEnd_2456405 : Nat := 1261316447107567037840705

theorem tailTrace_2456405 : CollatzResearch.WordTrace tailWord_2456405 prefixEnd_2456405 1261316447107567037840705 := by
  unfold tailWord_2456405
  simp only [CollatzResearch.WordTrace]
  refine ⟨89592450665871680419370669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59728300443914453612913779 89592450665871680419370669)
  ·
    refine ⟨33597168999701880157264001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89592450665871680419370669 33597168999701880157264001)
    ·
      refine ⟨25197876749776410117948001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33597168999701880157264001 25197876749776410117948001)
      ·
        refine ⟨18898407562332307588461001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25197876749776410117948001 18898407562332307588461001)
        ·
          refine ⟨14173805671749230691345751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18898407562332307588461001 14173805671749230691345751)
          ·
            refine ⟨21260708507623846037018627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14173805671749230691345751 21260708507623846037018627)
            ·
              refine ⟨31891062761435769055527941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21260708507623846037018627 31891062761435769055527941)
              ·
                refine ⟨5979574267769206697911489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31891062761435769055527941 5979574267769206697911489)
                ·
                  refine ⟨4484680700826905023433617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5979574267769206697911489 4484680700826905023433617)
                  ·
                    refine ⟨3363510525620178767575213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4484680700826905023433617 3363510525620178767575213)
                    ·
                      refine ⟨1261316447107567037840705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3363510525620178767575213 1261316447107567037840705)
                      ·
                        rfl

theorem cell23_2456405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_2456405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456405 prefixEnd_2456405 := by exact prefixLift 2456405
  have htrace : WordTrace (prefixWord ++ tailWord_2456405) baseStart_2456405 baseEnd_2456405 := by
    simpa [prefixWord, tailWord_2456405, baseEnd_2456405] using wordTrace_append hprefix tailTrace_2456405
  have hstable : (prefixWord ++ tailWord_2456405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456405).length < 2 ^ (prefixWord ++ tailWord_2456405).sum := by decide
  have hdescent : baseEnd_2456405 < baseStart_2456405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456435 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 5, 1, 3]
def baseStart_2456435 : Nat := 118140960795 + 2456435 * 2 ^ 59
def prefixEnd_2456435 : Nat := 4983230072969 + 3 ^ 40 * 2456435 * 2
def baseEnd_2456435 : Nat := 1261331851527201920465567

theorem tailTrace_2456435 : CollatzResearch.WordTrace tailWord_2456435 prefixEnd_2456435 1261331851527201920465567 := by
  unfold tailWord_2456435
  simp only [CollatzResearch.WordTrace]
  refine ⟨89593544855762995542962759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59729029903841997028641839 89593544855762995542962759)
  ·
    refine ⟨134390317283644493314444139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89593544855762995542962759 134390317283644493314444139)
    ·
      refine ⟨201585475925466739971666209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134390317283644493314444139 201585475925466739971666209)
      ·
        refine ⟨151189106944100054978749657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201585475925466739971666209 151189106944100054978749657)
        ·
          refine ⟨113391830208075041234062243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151189106944100054978749657 113391830208075041234062243)
          ·
            refine ⟨170087745312112561851093365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113391830208075041234062243 170087745312112561851093365)
            ·
              refine ⟨15945726123010552673540003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170087745312112561851093365 15945726123010552673540003)
              ·
                refine ⟨23918589184515829010310005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15945726123010552673540003 23918589184515829010310005)
                ·
                  refine ⟨2242367736048358969716563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23918589184515829010310005 2242367736048358969716563)
                  ·
                    refine ⟨3363551604072538454574845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2242367736048358969716563 3363551604072538454574845)
                    ·
                      refine ⟨1261331851527201920465567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3363551604072538454574845 1261331851527201920465567)
                      ·
                        rfl

theorem cell23_2456435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 1, 3].length) (baseStart_2456435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456435 prefixEnd_2456435 := by exact prefixLift 2456435
  have htrace : WordTrace (prefixWord ++ tailWord_2456435) baseStart_2456435 baseEnd_2456435 := by
    simpa [prefixWord, tailWord_2456435, baseEnd_2456435] using wordTrace_append hprefix tailTrace_2456435
  have hstable : (prefixWord ++ tailWord_2456435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456435).length < 2 ^ (prefixWord ++ tailWord_2456435).sum := by decide
  have hdescent : baseEnd_2456435 < baseStart_2456435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456469 : List Nat := [1, 3, 2, 1, 1, 4, 2, 4, 1, 1, 3]
def baseStart_2456469 : Nat := 118140960795 + 2456469 * 2 ^ 59
def prefixEnd_2456469 : Nat := 4983230072969 + 3 ^ 40 * 2456469 * 2
def baseEnd_2456469 : Nat := 1261349309869454787440411

theorem tailTrace_2456469 : CollatzResearch.WordTrace tailWord_2456469 prefixEnd_2456469 1261349309869454787440411 := by
  unfold tailWord_2456469
  simp only [CollatzResearch.WordTrace]
  refine ⟨89594784937639819349700461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59729856625093212899800307 89594784937639819349700461)
  ·
    refine ⟨33598044351614932256137673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89594784937639819349700461 33598044351614932256137673)
    ·
      refine ⟨25198533263711199192103255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33598044351614932256137673 25198533263711199192103255)
      ·
        refine ⟨37797799895566798788154883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25198533263711199192103255 37797799895566798788154883)
        ·
          refine ⟨56696699843350198182232325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37797799895566798788154883 56696699843350198182232325)
          ·
            refine ⟨10630631220628162159168561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56696699843350198182232325 10630631220628162159168561)
            ·
              refine ⟨7972973415471121619376421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10630631220628162159168561 7972973415471121619376421)
              ·
                refine ⟨1494932515400835303633079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7972973415471121619376421 1494932515400835303633079)
                ·
                  refine ⟨2242398773101252955449619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494932515400835303633079 2242398773101252955449619)
                  ·
                    refine ⟨3363598159651879433174429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2242398773101252955449619 3363598159651879433174429)
                    ·
                      refine ⟨1261349309869454787440411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3363598159651879433174429 1261349309869454787440411)
                      ·
                        rfl

theorem cell23_2456469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_2456469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456469 prefixEnd_2456469 := by exact prefixLift 2456469
  have htrace : WordTrace (prefixWord ++ tailWord_2456469) baseStart_2456469 baseEnd_2456469 := by
    simpa [prefixWord, tailWord_2456469, baseEnd_2456469] using wordTrace_append hprefix tailTrace_2456469
  have hstable : (prefixWord ++ tailWord_2456469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456469).length < 2 ^ (prefixWord ++ tailWord_2456469).sum := by decide
  have hdescent : baseEnd_2456469 < baseStart_2456469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456512 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 3]
def baseStart_2456512 : Nat := 118140960795 + 2456512 * 2 ^ 59
def prefixEnd_2456512 : Nat := 4983230072969 + 3 ^ 40 * 2456512 * 2
def baseEnd_2456512 : Nat := 1261371389537598119202713

theorem tailTrace_2456512 : CollatzResearch.WordTrace tailWord_2456512 prefixEnd_2456512 1261371389537598119202713 := by
  unfold tailWord_2456512
  simp only [CollatzResearch.WordTrace]
  refine ⟨44798176638242018846757895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59730902184322691795677193 44798176638242018846757895)
  ·
    refine ⟨67197264957363028270136843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44798176638242018846757895 67197264957363028270136843)
    ·
      refine ⟨100795897436044542405205265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67197264957363028270136843 100795897436044542405205265)
      ·
        refine ⟨75596923077033406803903949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100795897436044542405205265 75596923077033406803903949)
        ·
          refine ⟨28348846153887527551463981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75596923077033406803903949 28348846153887527551463981)
          ·
            refine ⟨10630817307707822831798993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28348846153887527551463981 10630817307707822831798993)
            ·
              refine ⟨7973112980780867123849245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10630817307707822831798993 7973112980780867123849245)
              ·
                refine ⟨2989917367792825171443467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7973112980780867123849245 2989917367792825171443467)
                ·
                  refine ⟨4484876051689237757165201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989917367792825171443467 4484876051689237757165201)
                  ·
                    refine ⟨3363657038766928317873901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4484876051689237757165201 3363657038766928317873901)
                    ·
                      refine ⟨1261371389537598119202713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3363657038766928317873901 1261371389537598119202713)
                      ·
                        rfl

theorem cell23_2456512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_2456512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456512 prefixEnd_2456512 := by exact prefixLift 2456512
  have htrace : WordTrace (prefixWord ++ tailWord_2456512) baseStart_2456512 baseEnd_2456512 := by
    simpa [prefixWord, tailWord_2456512, baseEnd_2456512] using wordTrace_append hprefix tailTrace_2456512
  have hstable : (prefixWord ++ tailWord_2456512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456512).length < 2 ^ (prefixWord ++ tailWord_2456512).sum := by decide
  have hdescent : baseEnd_2456512 < baseStart_2456512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456526 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2]
def baseStart_2456526 : Nat := 118140960795 + 2456526 * 2 ^ 59
def prefixEnd_2456526 : Nat := 4983230072969 + 3 ^ 40 * 2456526 * 2
def baseEnd_2456526 : Nat := 1261378578266761064427649

theorem tailTrace_2456526 : CollatzResearch.WordTrace tailWord_2456526 prefixEnd_2456526 1261378578266761064427649 := by
  unfold tailWord_2456526
  simp only [CollatzResearch.WordTrace]
  refine ⟨11199607987304164760565679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59731242598955545389683621 11199607987304164760565679)
  ·
    refine ⟨16799411980956247140848519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11199607987304164760565679 16799411980956247140848519)
    ·
      refine ⟨25199117971434370711272779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16799411980956247140848519 25199117971434370711272779)
      ·
        refine ⟨37798676957151556066909169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25199117971434370711272779 37798676957151556066909169)
        ·
          refine ⟨28349007717863667050181877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37798676957151556066909169 28349007717863667050181877)
          ·
            refine ⟨2657719473549718785954551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28349007717863667050181877 2657719473549718785954551)
            ·
              refine ⟨3986579210324578178931827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657719473549718785954551 3986579210324578178931827)
              ·
                refine ⟨5979868815486867268397741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3986579210324578178931827 5979868815486867268397741)
                ·
                  refine ⟨2242450805807575225649153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5979868815486867268397741 2242450805807575225649153)
                  ·
                    refine ⟨1681838104355681419236865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2242450805807575225649153 1681838104355681419236865)
                    ·
                      refine ⟨1261378578266761064427649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1681838104355681419236865 1261378578266761064427649)
                      ·
                        rfl

theorem cell23_2456526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_2456526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456526 prefixEnd_2456526 := by exact prefixLift 2456526
  have htrace : WordTrace (prefixWord ++ tailWord_2456526) baseStart_2456526 baseEnd_2456526 := by
    simpa [prefixWord, tailWord_2456526, baseEnd_2456526] using wordTrace_append hprefix tailTrace_2456526
  have hstable : (prefixWord ++ tailWord_2456526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456526).length < 2 ^ (prefixWord ++ tailWord_2456526).sum := by decide
  have hdescent : baseEnd_2456526 < baseStart_2456526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456528 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 2, 7]
def baseStart_2456528 : Nat := 118140960795 + 2456528 * 2 ^ 59
def prefixEnd_2456528 : Nat := 4983230072969 + 3 ^ 40 * 2456528 * 2
def baseEnd_2456528 : Nat := 420459868409356685534213

theorem tailTrace_2456528 : CollatzResearch.WordTrace tailWord_2456528 prefixEnd_2456528 420459868409356685534213 := by
  unfold tailWord_2456528
  simp only [CollatzResearch.WordTrace]
  refine ⟨44798468422213036213049119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59731291229617381617398825 44798468422213036213049119)
  ·
    refine ⟨67197702633319554319573679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44798468422213036213049119 67197702633319554319573679)
    ·
      refine ⟨100796553949979331479360519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67197702633319554319573679 100796553949979331479360519)
      ·
        refine ⟨151194830924968997219040779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100796553949979331479360519 151194830924968997219040779)
        ·
          refine ⟨226792246387453495828561169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151194830924968997219040779 226792246387453495828561169)
          ·
            refine ⟨170094184790590121871420877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226792246387453495828561169 170094184790590121871420877)
            ·
              refine ⟨63785319296471295701782829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170094184790590121871420877 63785319296471295701782829)
              ·
                refine ⟨23919494736176735888168561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63785319296471295701782829 23919494736176735888168561)
                ·
                  refine ⟨17939621052132551916126421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23919494736176735888168561 17939621052132551916126421)
                  ·
                    refine ⟨420459868409356685534213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17939621052132551916126421 420459868409356685534213)
                    ·
                      rfl

theorem cell23_2456528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_2456528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456528 prefixEnd_2456528 := by exact prefixLift 2456528
  have htrace : WordTrace (prefixWord ++ tailWord_2456528) baseStart_2456528 baseEnd_2456528 := by
    simpa [prefixWord, tailWord_2456528, baseEnd_2456528] using wordTrace_append hprefix tailTrace_2456528
  have hstable : (prefixWord ++ tailWord_2456528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456528).length < 2 ^ (prefixWord ++ tailWord_2456528).sum := by decide
  have hdescent : baseEnd_2456528 < baseStart_2456528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456546 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2456546 : Nat := 118140960795 + 2456546 * 2 ^ 59
def prefixEnd_2456546 : Nat := 4983230072969 + 3 ^ 40 * 2456546 * 2
def baseEnd_2456546 : Nat := 1261388847879850986177557

theorem tailTrace_2456546 : CollatzResearch.WordTrace tailWord_2456546 prefixEnd_2456546 1261388847879850986177557 := by
  unfold tailWord_2456546
  simp only [CollatzResearch.WordTrace]
  refine ⟨22399398339590215375063373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59731728905573907666835661 22399398339590215375063373)
  ·
    refine ⟨8399774377346330765648765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22399398339590215375063373 8399774377346330765648765)
    ·
      refine ⟨3149915391504874037118287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8399774377346330765648765 3149915391504874037118287)
      ·
        refine ⟨4724873087257311055677431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3149915391504874037118287 4724873087257311055677431)
        ·
          refine ⟨7087309630885966583516147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4724873087257311055677431 7087309630885966583516147)
          ·
            refine ⟨10630964446328949875274221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087309630885966583516147 10630964446328949875274221)
            ·
              refine ⟨3986611667373356203227833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10630964446328949875274221 3986611667373356203227833)
              ·
                refine ⟨2989958750530017152420875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3986611667373356203227833 2989958750530017152420875)
                ·
                  refine ⟨4484938125795025728631313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989958750530017152420875 4484938125795025728631313)
                  ·
                    refine ⟨3363703594346269296473485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4484938125795025728631313 3363703594346269296473485)
                    ·
                      refine ⟨1261388847879850986177557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3363703594346269296473485 1261388847879850986177557)
                      ·
                        rfl

theorem cell23_2456546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2456546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456546 prefixEnd_2456546 := by exact prefixLift 2456546
  have htrace : WordTrace (prefixWord ++ tailWord_2456546) baseStart_2456546 baseEnd_2456546 := by
    simpa [prefixWord, tailWord_2456546, baseEnd_2456546] using wordTrace_append hprefix tailTrace_2456546
  have hstable : (prefixWord ++ tailWord_2456546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456546).length < 2 ^ (prefixWord ++ tailWord_2456546).sum := by decide
  have hdescent : baseEnd_2456546 < baseStart_2456546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456599 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 1, 4, 2]
def baseStart_2456599 : Nat := 118140960795 + 2456599 * 2 ^ 59
def prefixEnd_2456599 : Nat := 4983230072969 + 3 ^ 40 * 2456599 * 2
def baseEnd_2456599 : Nat := 1261416062354539278814813

theorem tailTrace_2456599 : CollatzResearch.WordTrace tailWord_2456599 prefixEnd_2456599 1261416062354539278814813 := by
  unfold tailWord_2456599
  simp only [CollatzResearch.WordTrace]
  refine ⟨89599526427168851551932851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59733017618112567701288567 89599526427168851551932851)
  ·
    refine ⟨134399289640753277327899277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89599526427168851551932851 134399289640753277327899277)
    ·
      refine ⟨50399733615282478997962229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134399289640753277327899277 50399733615282478997962229)
      ·
        refine ⟨4724975026432732406058959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50399733615282478997962229 4724975026432732406058959)
        ·
          refine ⟨7087462539649098609088439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4724975026432732406058959 7087462539649098609088439)
          ·
            refine ⟨10631193809473647913632659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087462539649098609088439 10631193809473647913632659)
            ·
              refine ⟨15946790714210471870448989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10631193809473647913632659 15946790714210471870448989)
              ·
                refine ⟨5980046517828926951418371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15946790714210471870448989 5980046517828926951418371)
                ·
                  refine ⟨8970069776743390427127557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5980046517828926951418371 8970069776743390427127557)
                  ·
                    refine ⟨1681888083139385705086417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8970069776743390427127557 1681888083139385705086417)
                    ·
                      refine ⟨1261416062354539278814813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1681888083139385705086417 1261416062354539278814813)
                      ·
                        rfl

theorem cell23_2456599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_2456599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456599 prefixEnd_2456599 := by exact prefixLift 2456599
  have htrace : WordTrace (prefixWord ++ tailWord_2456599) baseStart_2456599 baseEnd_2456599 := by
    simpa [prefixWord, tailWord_2456599, baseEnd_2456599] using wordTrace_append hprefix tailTrace_2456599
  have hstable : (prefixWord ++ tailWord_2456599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456599).length < 2 ^ (prefixWord ++ tailWord_2456599).sum := by decide
  have hdescent : baseEnd_2456599 < baseStart_2456599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456632 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 2, 3, 3]
def baseStart_2456632 : Nat := 118140960795 + 2456632 * 2 ^ 59
def prefixEnd_2456632 : Nat := 4983230072969 + 3 ^ 40 * 2456632 * 2
def baseEnd_2456632 : Nat := 1261433007216137649702161

theorem tailTrace_2456632 : CollatzResearch.WordTrace tailWord_2456632 prefixEnd_2456632 1261433007216137649702161 := by
  unfold tailWord_2456632
  simp only [CollatzResearch.WordTrace]
  refine ⟨44800365018024649093942075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59733820024032865458589433 44800365018024649093942075)
  ·
    refine ⟨67200547527036973640913113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44800365018024649093942075 67200547527036973640913113)
    ·
      refine ⟨50400410645277730230684835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67200547527036973640913113 50400410645277730230684835)
      ·
        refine ⟨75600615967916595346027253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50400410645277730230684835 75600615967916595346027253)
        ·
          refine ⟨7087557746992180813690055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75600615967916595346027253 7087557746992180813690055)
          ·
            refine ⟨10631336620488271220535083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087557746992180813690055 10631336620488271220535083)
            ·
              refine ⟨15947004930732406830802625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10631336620488271220535083 15947004930732406830802625)
              ·
                refine ⟨11960253698049305123101969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15947004930732406830802625 11960253698049305123101969)
                ·
                  refine ⟨8970190273536978842326477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11960253698049305123101969 8970190273536978842326477)
                  ·
                    refine ⟨3363821352576367065872429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8970190273536978842326477 3363821352576367065872429)
                    ·
                      refine ⟨1261433007216137649702161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3363821352576367065872429 1261433007216137649702161)
                      ·
                        rfl

theorem cell23_2456632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_2456632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456632 prefixEnd_2456632 := by exact prefixLift 2456632
  have htrace : WordTrace (prefixWord ++ tailWord_2456632) baseStart_2456632 baseEnd_2456632 := by
    simpa [prefixWord, tailWord_2456632, baseEnd_2456632] using wordTrace_append hprefix tailTrace_2456632
  have hstable : (prefixWord ++ tailWord_2456632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456632).length < 2 ^ (prefixWord ++ tailWord_2456632).sum := by decide
  have hdescent : baseEnd_2456632 < baseStart_2456632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456633 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 2, 2, 2]
def baseStart_2456633 : Nat := 118140960795 + 2456633 * 2 ^ 59
def prefixEnd_2456633 : Nat := 4983230072969 + 3 ^ 40 * 2456633 * 2
def baseEnd_2456633 : Nat := 1261433520696792145789657

theorem tailTrace_2456633 : CollatzResearch.WordTrace tailWord_2456633 prefixEnd_2456633 1261433520696792145789657 := by
  unfold tailWord_2456633
  simp only [CollatzResearch.WordTrace]
  refine ⟨89600766509045675358670553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59733844339363783572447035 89600766509045675358670553)
  ·
    refine ⟨67200574881784256519002915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89600766509045675358670553 67200574881784256519002915)
    ·
      refine ⟨100800862322676384778504373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67200574881784256519002915 100800862322676384778504373)
      ·
        refine ⟨9450080842750911072984785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100800862322676384778504373 9450080842750911072984785)
        ·
          refine ⟨7087560632063183304738589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9450080842750911072984785 7087560632063183304738589)
          ·
            refine ⟨2657835237023693739276971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7087560632063183304738589 2657835237023693739276971)
            ·
              refine ⟨3986752855535540608915457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657835237023693739276971 3986752855535540608915457)
              ·
                refine ⟨2990064641651655456686593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3986752855535540608915457 2990064641651655456686593)
                ·
                  refine ⟨2242548481238741592514945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2990064641651655456686593 2242548481238741592514945)
                  ·
                    refine ⟨1681911360929056194386209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2242548481238741592514945 1681911360929056194386209)
                    ·
                      refine ⟨1261433520696792145789657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1681911360929056194386209 1261433520696792145789657)
                      ·
                        rfl

theorem cell23_2456633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_2456633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456633 prefixEnd_2456633 := by exact prefixLift 2456633
  have htrace : WordTrace (prefixWord ++ tailWord_2456633) baseStart_2456633 baseEnd_2456633 := by
    simpa [prefixWord, tailWord_2456633, baseEnd_2456633] using wordTrace_append hprefix tailTrace_2456633
  have hstable : (prefixWord ++ tailWord_2456633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456633).length < 2 ^ (prefixWord ++ tailWord_2456633).sum := by decide
  have hdescent : baseEnd_2456633 < baseStart_2456633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456645 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_2456645 : Nat := 118140960795 + 2456645 * 2 ^ 59
def prefixEnd_2456645 : Nat := 4983230072969 + 3 ^ 40 * 2456645 * 2
def baseEnd_2456645 : Nat := 1261439682464646098839601

theorem tailTrace_2456645 : CollatzResearch.WordTrace tailWord_2456645 prefixEnd_2456645 1261439682464646098839601 := by
  unfold tailWord_2456645
  simp only [CollatzResearch.WordTrace]
  refine ⟨89601204185002201408107389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59734136123334800938738259 89601204185002201408107389)
  ·
    refine ⟨33600451569375825528040271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89601204185002201408107389 33600451569375825528040271)
    ·
      refine ⟨50400677354063738292060407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33600451569375825528040271 50400677354063738292060407)
      ·
        refine ⟨75601016031095607438090611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50400677354063738292060407 75601016031095607438090611)
        ·
          refine ⟨113401524046643411157135917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75601016031095607438090611 113401524046643411157135917)
          ·
            refine ⟨42525571517491279183925969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113401524046643411157135917 42525571517491279183925969)
            ·
              refine ⟨31894178638118459387944477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42525571517491279183925969 31894178638118459387944477)
              ·
                refine ⟨11960316989294422270479179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31894178638118459387944477 11960316989294422270479179)
                ·
                  refine ⟨17940475483941633405718769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11960316989294422270479179 17940475483941633405718769)
                  ·
                    refine ⟨13455356612956225054289077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17940475483941633405718769 13455356612956225054289077)
                    ·
                      refine ⟨1261439682464646098839601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13455356612956225054289077 1261439682464646098839601)
                      ·
                        rfl

theorem cell23_2456645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_2456645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456645 prefixEnd_2456645 := by exact prefixLift 2456645
  have htrace : WordTrace (prefixWord ++ tailWord_2456645) baseStart_2456645 baseEnd_2456645 := by
    simpa [prefixWord, tailWord_2456645, baseEnd_2456645] using wordTrace_append hprefix tailTrace_2456645
  have hstable : (prefixWord ++ tailWord_2456645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456645).length < 2 ^ (prefixWord ++ tailWord_2456645).sum := by decide
  have hdescent : baseEnd_2456645 < baseStart_2456645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456672 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 4]
def baseStart_2456672 : Nat := 118140960795 + 2456672 * 2 ^ 59
def prefixEnd_2456672 : Nat := 4983230072969 + 3 ^ 40 * 2456672 * 2
def baseEnd_2456672 : Nat := 1261453546442317493201977

theorem tailTrace_2456672 : CollatzResearch.WordTrace tailWord_2456672 prefixEnd_2456672 1261453546442317493201977 := by
  unfold tailWord_2456672
  simp only [CollatzResearch.WordTrace]
  refine ⟨44801094477952192509670135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59734792637269590012893513 44801094477952192509670135)
  ·
    refine ⟨67201641716928288764505203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44801094477952192509670135 67201641716928288764505203)
    ·
      refine ⟨100802462575392433146757805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67201641716928288764505203 100802462575392433146757805)
      ·
        refine ⟨37800923465772162430034177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100802462575392433146757805 37800923465772162430034177)
        ·
          refine ⟨28350692599329121822525633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37800923465772162430034177 28350692599329121822525633)
          ·
            refine ⟨21263019449496841366894225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28350692599329121822525633 21263019449496841366894225)
            ·
              refine ⟨15947264587122631025170669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21263019449496841366894225 15947264587122631025170669)
              ·
                refine ⟨5980224220170986634439001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15947264587122631025170669 5980224220170986634439001)
                ·
                  refine ⟨4485168165128239975829251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5980224220170986634439001 4485168165128239975829251)
                  ·
                    refine ⟨6727752247692359963743877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4485168165128239975829251 6727752247692359963743877)
                    ·
                      refine ⟨1261453546442317493201977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6727752247692359963743877 1261453546442317493201977)
                      ·
                        rfl

theorem cell23_2456672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_2456672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456672 prefixEnd_2456672 := by exact prefixLift 2456672
  have htrace : WordTrace (prefixWord ++ tailWord_2456672) baseStart_2456672 baseEnd_2456672 := by
    simpa [prefixWord, tailWord_2456672, baseEnd_2456672] using wordTrace_append hprefix tailTrace_2456672
  have hstable : (prefixWord ++ tailWord_2456672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456672).length < 2 ^ (prefixWord ++ tailWord_2456672).sum := by decide
  have hdescent : baseEnd_2456672 < baseStart_2456672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456675 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 5]
def baseStart_2456675 : Nat := 118140960795 + 2456675 * 2 ^ 59
def prefixEnd_2456675 : Nat := 4983230072969 + 3 ^ 40 * 2456675 * 2
def baseEnd_2456675 : Nat := 1261455086884280981464463

theorem tailTrace_2456675 : CollatzResearch.WordTrace tailWord_2456675 prefixEnd_2456675 1261455086884280981464463 := by
  unfold tailWord_2456675
  simp only [CollatzResearch.WordTrace]
  refine ⟨89602298374893516531699479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59734865583262344354466319 89602298374893516531699479)
  ·
    refine ⟨134403447562340274797549219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89602298374893516531699479 134403447562340274797549219)
    ·
      refine ⟨201605171343510412196323829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134403447562340274797549219 201605171343510412196323829)
      ·
        refine ⟨18900484813454101143405359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201605171343510412196323829 18900484813454101143405359)
        ·
          refine ⟨28350727220181151715108039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18900484813454101143405359 28350727220181151715108039)
          ·
            refine ⟨42526090830271727572662059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28350727220181151715108039 42526090830271727572662059)
            ·
              refine ⟨63789136245407591358993089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42526090830271727572662059 63789136245407591358993089)
              ·
                refine ⟨47841852184055693519244817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63789136245407591358993089 47841852184055693519244817)
                ·
                  refine ⟨35881389138041770139433613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47841852184055693519244817 35881389138041770139433613)
                  ·
                    refine ⟨13455520926765663802287605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35881389138041770139433613 13455520926765663802287605)
                    ·
                      refine ⟨1261455086884280981464463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13455520926765663802287605 1261455086884280981464463)
                      ·
                        rfl

theorem cell23_2456675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_2456675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456675 prefixEnd_2456675 := by exact prefixLift 2456675
  have htrace : WordTrace (prefixWord ++ tailWord_2456675) baseStart_2456675 baseEnd_2456675 := by
    simpa [prefixWord, tailWord_2456675, baseEnd_2456675] using wordTrace_append hprefix tailTrace_2456675
  have hstable : (prefixWord ++ tailWord_2456675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456675).length < 2 ^ (prefixWord ++ tailWord_2456675).sum := by decide
  have hdescent : baseEnd_2456675 < baseStart_2456675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456695 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 8]
def baseStart_2456695 : Nat := 118140960795 + 2456695 * 2 ^ 59
def prefixEnd_2456695 : Nat := 4983230072969 + 3 ^ 40 * 2456695 * 2
def baseEnd_2456695 : Nat := 140162817388596767023819

theorem tailTrace_2456695 : CollatzResearch.WordTrace tailWord_2456695 prefixEnd_2456695 140162817388596767023819 := by
  unfold tailWord_2456695
  simp only [CollatzResearch.WordTrace]
  refine ⟨89603027834821059947427539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59735351889880706631618359 89603027834821059947427539)
  ·
    refine ⟨134404541752231589921141309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89603027834821059947427539 134404541752231589921141309)
    ·
      refine ⟨50401703157086846220427991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134404541752231589921141309 50401703157086846220427991)
      ·
        refine ⟨75602554735630269330641987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50401703157086846220427991 75602554735630269330641987)
        ·
          refine ⟨113403832103445403995962981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75602554735630269330641987 113403832103445403995962981)
          ·
            refine ⟨21263218519396013249243059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113403832103445403995962981 21263218519396013249243059)
            ·
              refine ⟨31894827779094019873864589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21263218519396013249243059 31894827779094019873864589)
              ·
                refine ⟨11960560417160257452699221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31894827779094019873864589 11960560417160257452699221)
                ·
                  refine ⟨140162817388596767023819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11960560417160257452699221 140162817388596767023819)
                  ·
                    rfl

theorem cell23_2456695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 8].length) (baseStart_2456695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456695 prefixEnd_2456695 := by exact prefixLift 2456695
  have htrace : WordTrace (prefixWord ++ tailWord_2456695) baseStart_2456695 baseEnd_2456695 := by
    simpa [prefixWord, tailWord_2456695, baseEnd_2456695] using wordTrace_append hprefix tailTrace_2456695
  have hstable : (prefixWord ++ tailWord_2456695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456695).length < 2 ^ (prefixWord ++ tailWord_2456695).sum := by decide
  have hdescent : baseEnd_2456695 < baseStart_2456695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456699 : List Nat := [1, 1, 1, 1, 1, 4, 1, 8, 1, 4]
def baseStart_2456699 : Nat := 118140960795 + 2456699 * 2 ^ 59
def prefixEnd_2456699 : Nat := 4983230072969 + 3 ^ 40 * 2456699 * 2
def baseEnd_2456699 : Nat := 420489136806662962521451

theorem tailTrace_2456699 : CollatzResearch.WordTrace tailWord_2456699 prefixEnd_2456699 420489136806662962521451 := by
  unfold tailWord_2456699
  simp only [CollatzResearch.WordTrace]
  refine ⟨89603173726806568630573151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59735449151204379087048767 89603173726806568630573151)
  ·
    refine ⟨134404760590209852945859727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89603173726806568630573151 134404760590209852945859727)
    ·
      refine ⟨201607140885314779418789591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134404760590209852945859727 201607140885314779418789591)
      ·
        refine ⟨302410711327972169128184387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201607140885314779418789591 302410711327972169128184387)
        ·
          refine ⟨453616066991958253692276581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302410711327972169128184387 453616066991958253692276581)
          ·
            refine ⟨85053012560992172567301859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 453616066991958253692276581 85053012560992172567301859)
            ·
              refine ⟨127579518841488258850952789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85053012560992172567301859 127579518841488258850952789)
              ·
                refine ⟨1495072486423690533409603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 127579518841488258850952789 1495072486423690533409603)
                ·
                  refine ⟨2242608729635535800114405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495072486423690533409603 2242608729635535800114405)
                  ·
                    refine ⟨420489136806662962521451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2242608729635535800114405 420489136806662962521451)
                    ·
                      rfl

theorem cell23_2456699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 1, 4].length) (baseStart_2456699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456699 prefixEnd_2456699 := by exact prefixLift 2456699
  have htrace : WordTrace (prefixWord ++ tailWord_2456699) baseStart_2456699 baseEnd_2456699 := by
    simpa [prefixWord, tailWord_2456699, baseEnd_2456699] using wordTrace_append hprefix tailTrace_2456699
  have hstable : (prefixWord ++ tailWord_2456699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456699).length < 2 ^ (prefixWord ++ tailWord_2456699).sum := by decide
  have hdescent : baseEnd_2456699 < baseStart_2456699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456715 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 6]
def baseStart_2456715 : Nat := 118140960795 + 2456715 * 2 ^ 59
def prefixEnd_2456715 : Nat := 4983230072969 + 3 ^ 40 * 2456715 * 2
def baseEnd_2456715 : Nat := 1261475626110460824964279

theorem tailTrace_2456715 : CollatzResearch.WordTrace tailWord_2456715 prefixEnd_2456715 1261475626110460824964279 := by
  unfold tailWord_2456715
  simp only [CollatzResearch.WordTrace]
  refine ⟨89603757294748603363155599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59735838196499068908770399 89603757294748603363155599)
  ·
    refine ⟨134405635942122905044733399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89603757294748603363155599 134405635942122905044733399)
    ·
      refine ⟨201608453913184357567100099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134405635942122905044733399 201608453913184357567100099)
      ·
        refine ⟨302412680869776536350650149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201608453913184357567100099 302412680869776536350650149)
        ·
          refine ⟨56702377663083100565746903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302412680869776536350650149 56702377663083100565746903)
          ·
            refine ⟨85053566494624650848620355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56702377663083100565746903 85053566494624650848620355)
            ·
              refine ⟨127580349741936976272930533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85053566494624650848620355 127580349741936976272930533)
              ·
                refine ⟨23921315576613183051174475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127580349741936976272930533 23921315576613183051174475)
                ·
                  refine ⟨35881973364919774576761713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23921315576613183051174475 35881973364919774576761713)
                  ·
                    refine ⟨26911480023689830932571285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35881973364919774576761713 26911480023689830932571285)
                    ·
                      refine ⟨1261475626110460824964279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26911480023689830932571285 1261475626110460824964279)
                      ·
                        rfl

theorem cell23_2456715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_2456715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456715 prefixEnd_2456715 := by exact prefixLift 2456715
  have htrace : WordTrace (prefixWord ++ tailWord_2456715) baseStart_2456715 baseEnd_2456715 := by
    simpa [prefixWord, tailWord_2456715, baseEnd_2456715] using wordTrace_append hprefix tailTrace_2456715
  have hstable : (prefixWord ++ tailWord_2456715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456715).length < 2 ^ (prefixWord ++ tailWord_2456715).sum := by decide
  have hdescent : baseEnd_2456715 < baseStart_2456715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456746 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 6]
def baseStart_2456746 : Nat := 118140960795 + 2456746 * 2 ^ 59
def prefixEnd_2456746 : Nat := 4983230072969 + 3 ^ 40 * 2456746 * 2
def baseEnd_2456746 : Nat := 140165727112305578186293

theorem tailTrace_2456746 : CollatzResearch.WordTrace tailWord_2456746 prefixEnd_2456746 140165727112305578186293 := by
  unfold tailWord_2456746
  simp only [CollatzResearch.WordTrace]
  refine ⟨22401221989409073914383523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59736591971757530438356061 22401221989409073914383523)
  ·
    refine ⟨33601832984113610871575285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22401221989409073914383523 33601832984113610871575285)
    ·
      refine ⟨3150171842260651019210183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33601832984113610871575285 3150171842260651019210183)
      ·
        refine ⟨4725257763390976528815275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3150171842260651019210183 4725257763390976528815275)
        ·
          refine ⟨7087886645086464793222913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4725257763390976528815275 7087886645086464793222913)
          ·
            refine ⟨5315914983814848594917185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7087886645086464793222913 5315914983814848594917185)
            ·
              refine ⟨3986936237861136446187889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5315914983814848594917185 3986936237861136446187889)
              ·
                refine ⟨2990202178395852334640917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3986936237861136446187889 2990202178395852334640917)
                ·
                  refine ⟨140165727112305578186293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2990202178395852334640917 140165727112305578186293)
                  ·
                    rfl

theorem cell23_2456746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_2456746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456746 prefixEnd_2456746 := by exact prefixLift 2456746
  have htrace : WordTrace (prefixWord ++ tailWord_2456746) baseStart_2456746 baseEnd_2456746 := by
    simpa [prefixWord, tailWord_2456746, baseEnd_2456746] using wordTrace_append hprefix tailTrace_2456746
  have hstable : (prefixWord ++ tailWord_2456746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456746).length < 2 ^ (prefixWord ++ tailWord_2456746).sum := by decide
  have hdescent : baseEnd_2456746 < baseStart_2456746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456789 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_2456789 : Nat := 118140960795 + 2456789 * 2 ^ 59
def prefixEnd_2456789 : Nat := 4983230072969 + 3 ^ 40 * 2456789 * 2
def baseEnd_2456789 : Nat := 420504541226297845146313

theorem tailTrace_2456789 : CollatzResearch.WordTrace tailWord_2456789 prefixEnd_2456789 420504541226297845146313 := by
  unfold tailWord_2456789
  simp only [CollatzResearch.WordTrace]
  refine ⟨89606456296480514001349421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59737637530987009334232947 89606456296480514001349421)
  ·
    refine ⟨33602421111180192750506033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89606456296480514001349421 33602421111180192750506033)
    ·
      refine ⟨25201815833385144562879525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33602421111180192750506033 25201815833385144562879525)
      ·
        refine ⟨4725340468759714605539911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25201815833385144562879525 4725340468759714605539911)
        ·
          refine ⟨7088010703139571908309867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4725340468759714605539911 7088010703139571908309867)
          ·
            refine ⟨10632016054709357862464801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7088010703139571908309867 10632016054709357862464801)
            ·
              refine ⟨7974012041032018396848601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10632016054709357862464801 7974012041032018396848601)
              ·
                refine ⟨5980509030774013797636451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7974012041032018396848601 5980509030774013797636451)
                ·
                  refine ⟨8970763546161020696454677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5980509030774013797636451 8970763546161020696454677)
                  ·
                    refine ⟨420504541226297845146313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8970763546161020696454677 420504541226297845146313)
                    ·
                      rfl

theorem cell23_2456789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_2456789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456789 prefixEnd_2456789 := by exact prefixLift 2456789
  have htrace : WordTrace (prefixWord ++ tailWord_2456789) baseStart_2456789 baseEnd_2456789 := by
    simpa [prefixWord, tailWord_2456789, baseEnd_2456789] using wordTrace_append hprefix tailTrace_2456789
  have hstable : (prefixWord ++ tailWord_2456789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456789).length < 2 ^ (prefixWord ++ tailWord_2456789).sum := by decide
  have hdescent : baseEnd_2456789 < baseStart_2456789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456813 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_2456813 : Nat := 118140960795 + 2456813 * 2 ^ 59
def prefixEnd_2456813 : Nat := 4983230072969 + 3 ^ 40 * 2456813 * 2
def baseEnd_2456813 : Nat := 1261525947214601441538829

theorem tailTrace_2456813 : CollatzResearch.WordTrace tailWord_2456813 prefixEnd_2456813 1261525947214601441538829 := by
  unfold tailWord_2456813
  simp only [CollatzResearch.WordTrace]
  refine ⟨89607331648393566100223093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59738221098929044066815395 89607331648393566100223093)
  ·
    refine ⟨8400687342036896821895915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89607331648393566100223093 8400687342036896821895915)
    ·
      refine ⟨12601031013055345232843873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8400687342036896821895915 12601031013055345232843873)
      ·
        refine ⟨9450773259791508924632905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12601031013055345232843873 9450773259791508924632905)
        ·
          refine ⟨7088079944843631693474679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9450773259791508924632905 7088079944843631693474679)
          ·
            refine ⟨10632119917265447540212019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7088079944843631693474679 10632119917265447540212019)
            ·
              refine ⟨15948179875898171310318029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10632119917265447540212019 15948179875898171310318029)
              ·
                refine ⟨5980567453461814241369261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15948179875898171310318029 5980567453461814241369261)
                ·
                  refine ⟨2242712795048180340513473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5980567453461814241369261 2242712795048180340513473)
                  ·
                    refine ⟨1682034596286135255385105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2242712795048180340513473 1682034596286135255385105)
                    ·
                      refine ⟨1261525947214601441538829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682034596286135255385105 1261525947214601441538829)
                      ·
                        rfl

theorem cell23_2456813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_2456813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456813 prefixEnd_2456813 := by exact prefixLift 2456813
  have htrace : WordTrace (prefixWord ++ tailWord_2456813) baseStart_2456813 baseEnd_2456813 := by
    simpa [prefixWord, tailWord_2456813, baseEnd_2456813] using wordTrace_append hprefix tailTrace_2456813
  have hstable : (prefixWord ++ tailWord_2456813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456813).length < 2 ^ (prefixWord ++ tailWord_2456813).sum := by decide
  have hdescent : baseEnd_2456813 < baseStart_2456813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456836 : List Nat := [2, 3, 2, 2, 2, 3, 2, 7]
def baseStart_2456836 : Nat := 118140960795 + 2456836 * 2 ^ 59
def prefixEnd_2456836 : Nat := 4983230072969 + 3 ^ 40 * 2456836 * 2
def baseEnd_2456836 : Nat := 46723620639616846353749

theorem tailTrace_2456836 : CollatzResearch.WordTrace tailWord_2456836 prefixEnd_2456836 46723620639616846353749 := by
  unfold tailWord_2456836
  simp only [CollatzResearch.WordTrace]
  refine ⟨44804085263655120514155181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59738780351540160685540241 44804085263655120514155181)
  ·
    refine ⟨16801531973870670192808193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44804085263655120514155181 16801531973870670192808193)
    ·
      refine ⟨12601148980403002644606145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16801531973870670192808193 12601148980403002644606145)
      ·
        refine ⟨9450861735302251983454609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12601148980403002644606145 9450861735302251983454609)
        ·
          refine ⟨7088146301476688987590957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9450861735302251983454609 7088146301476688987590957)
          ·
            refine ⟨2658054863053758370346609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7088146301476688987590957 2658054863053758370346609)
            ·
              refine ⟨1993541147290318777759957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2658054863053758370346609 1993541147290318777759957)
              ·
                refine ⟨46723620639616846353749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1993541147290318777759957 46723620639616846353749)
                ·
                  rfl

theorem cell23_2456836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 7].length) (baseStart_2456836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456836 prefixEnd_2456836 := by exact prefixLift 2456836
  have htrace : WordTrace (prefixWord ++ tailWord_2456836) baseStart_2456836 baseEnd_2456836 := by
    simpa [prefixWord, tailWord_2456836, baseEnd_2456836] using wordTrace_append hprefix tailTrace_2456836
  have hstable : (prefixWord ++ tailWord_2456836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456836).length < 2 ^ (prefixWord ++ tailWord_2456836).sum := by decide
  have hdescent : baseEnd_2456836 < baseStart_2456836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456846 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_2456846 : Nat := 118140960795 + 2456846 * 2 ^ 59
def prefixEnd_2456846 : Nat := 4983230072969 + 3 ^ 40 * 2456846 * 2
def baseEnd_2456846 : Nat := 1261542892076199812426177

theorem tailTrace_2456846 : CollatzResearch.WordTrace tailWord_2456846 prefixEnd_2456846 1261542892076199812426177 := by
  unfold tailWord_2456846
  simp only [CollatzResearch.WordTrace]
  refine ⟨11201066907159251592021799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59739023504849341824116261 11201066907159251592021799)
  ·
    refine ⟨16801600360738877388032699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11201066907159251592021799 16801600360738877388032699)
    ·
      refine ⟨25202400541108316082049049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16801600360738877388032699 25202400541108316082049049)
      ·
        refine ⟨18901800405831237061536787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25202400541108316082049049 18901800405831237061536787)
        ·
          refine ⟨28352700608746855592305181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18901800405831237061536787 28352700608746855592305181)
          ·
            refine ⟨10632262728280070847114443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28352700608746855592305181 10632262728280070847114443)
            ·
              refine ⟨15948394092420106270671665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10632262728280070847114443 15948394092420106270671665)
              ·
                refine ⟨11961295569315079703003749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15948394092420106270671665 11961295569315079703003749)
                ·
                  refine ⟨2242742919246577444313203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11961295569315079703003749 2242742919246577444313203)
                  ·
                    refine ⟨3364114378869866166469805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2242742919246577444313203 3364114378869866166469805)
                    ·
                      refine ⟨1261542892076199812426177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3364114378869866166469805 1261542892076199812426177)
                      ·
                        rfl

theorem cell23_2456846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_2456846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456846 prefixEnd_2456846 := by exact prefixLift 2456846
  have htrace : WordTrace (prefixWord ++ tailWord_2456846) baseStart_2456846 baseEnd_2456846 := by
    simpa [prefixWord, tailWord_2456846, baseEnd_2456846] using wordTrace_append hprefix tailTrace_2456846
  have hstable : (prefixWord ++ tailWord_2456846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456846).length < 2 ^ (prefixWord ++ tailWord_2456846).sum := by decide
  have hdescent : baseEnd_2456846 < baseStart_2456846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456946 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 2, 5, 2]
def baseStart_2456946 : Nat := 118140960795 + 2456946 * 2 ^ 59
def prefixEnd_2456946 : Nat := 4983230072969 + 3 ^ 40 * 2456946 * 2
def baseEnd_2456946 : Nat := 1261594240141649421175717

theorem tailTrace_2456946 : CollatzResearch.WordTrace tailWord_2456946 prefixEnd_2456946 1261594240141649421175717 := by
  unfold tailWord_2456946
  simp only [CollatzResearch.WordTrace]
  refine ⟨22403045639227932453703673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59741455037941153209876461 22403045639227932453703673)
  ·
    refine ⟨16802284229420949340277755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22403045639227932453703673 16802284229420949340277755)
    ·
      refine ⟨25203426344131424010416633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16802284229420949340277755 25203426344131424010416633)
      ·
        refine ⟨18902569758098568007812475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25203426344131424010416633 18902569758098568007812475)
        ·
          refine ⟨28353854637147852011718713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18902569758098568007812475 28353854637147852011718713)
          ·
            refine ⟨21265390977860889008789035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28353854637147852011718713 21265390977860889008789035)
            ·
              refine ⟨31898086466791333513183553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21265390977860889008789035 31898086466791333513183553)
              ·
                refine ⟨23923564850093500134887665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31898086466791333513183553 23923564850093500134887665)
                ·
                  refine ⟨17942673637570125101165749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23923564850093500134887665 17942673637570125101165749)
                  ·
                    refine ⟨1682125653522199228234289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17942673637570125101165749 1682125653522199228234289)
                    ·
                      refine ⟨1261594240141649421175717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682125653522199228234289 1261594240141649421175717)
                      ·
                        rfl

theorem cell23_2456946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_2456946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2456946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2456946 prefixEnd_2456946 := by exact prefixLift 2456946
  have htrace : WordTrace (prefixWord ++ tailWord_2456946) baseStart_2456946 baseEnd_2456946 := by
    simpa [prefixWord, tailWord_2456946, baseEnd_2456946] using wordTrace_append hprefix tailTrace_2456946
  have hstable : (prefixWord ++ tailWord_2456946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456946).length < 2 ^ (prefixWord ++ tailWord_2456946).sum := by decide
  have hdescent : baseEnd_2456946 < baseStart_2456946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457063 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 1, 5]
def baseStart_2457063 : Nat := 118140960795 + 2457063 * 2 ^ 59
def prefixEnd_2457063 : Nat := 4983230072969 + 3 ^ 40 * 2457063 * 2
def baseEnd_2457063 : Nat := 420551439126075154470893

theorem tailTrace_2457063 : CollatzResearch.WordTrace tailWord_2457063 prefixEnd_2457063 420551439126075154470893 := by
  unfold tailWord_2457063
  simp only [CollatzResearch.WordTrace]
  refine ⟨89616449897487858796823843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59744299931658572531215895 89616449897487858796823843)
  ·
    refine ⟨134424674846231788195235765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89616449897487858796823843 134424674846231788195235765)
    ·
      refine ⟨12602313266834230143303353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134424674846231788195235765 12602313266834230143303353)
      ·
        refine ⟨9451734950125672607477515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12602313266834230143303353 9451734950125672607477515)
        ·
          refine ⟨14177602425188508911216273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9451734950125672607477515 14177602425188508911216273)
          ·
            refine ⟨10633201818891381683412205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14177602425188508911216273 10633201818891381683412205)
            ·
              refine ⟨3987450682084268131279577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10633201818891381683412205 3987450682084268131279577)
              ·
                refine ⟨2990588011563201098459683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3987450682084268131279577 2990588011563201098459683)
                ·
                  refine ⟨4485882017344801647689525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990588011563201098459683 4485882017344801647689525)
                  ·
                    refine ⟨420551439126075154470893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4485882017344801647689525 420551439126075154470893)
                    ·
                      rfl

theorem cell23_2457063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_2457063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457063 prefixEnd_2457063 := by exact prefixLift 2457063
  have htrace : WordTrace (prefixWord ++ tailWord_2457063) baseStart_2457063 baseEnd_2457063 := by
    simpa [prefixWord, tailWord_2457063, baseEnd_2457063] using wordTrace_append hprefix tailTrace_2457063
  have hstable : (prefixWord ++ tailWord_2457063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457063).length < 2 ^ (prefixWord ++ tailWord_2457063).sum := by decide
  have hdescent : baseEnd_2457063 < baseStart_2457063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457070 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_2457070 : Nat := 118140960795 + 2457070 * 2 ^ 59
def prefixEnd_2457070 : Nat := 4983230072969 + 3 ^ 40 * 2457070 * 2
def baseEnd_2457070 : Nat := 1261657911742806936025147

theorem tailTrace_2457070 : CollatzResearch.WordTrace tailWord_2457070 prefixEnd_2457070 1261657911742806936025147 := by
  unfold tailWord_2457070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11202088151057812374041083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59744470138974999328219109 11202088151057812374041083)
  ·
    refine ⟨16803132226586718561061625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11202088151057812374041083 16803132226586718561061625)
    ·
      refine ⟨12602349169940038920796219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16803132226586718561061625 12602349169940038920796219)
      ·
        refine ⟨18903523754910058381194329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12602349169940038920796219 18903523754910058381194329)
        ·
          refine ⟨14177642816182543785895747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18903523754910058381194329 14177642816182543785895747)
          ·
            refine ⟨21266464224273815678843621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14177642816182543785895747 21266464224273815678843621)
            ·
              refine ⟨3987462042051340439783179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21266464224273815678843621 3987462042051340439783179)
              ·
                refine ⟨5981193063077010659674769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3987462042051340439783179 5981193063077010659674769)
                ·
                  refine ⟨4485894797307757994756077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5981193063077010659674769 4485894797307757994756077)
                  ·
                    refine ⟨1682210548990409248033529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4485894797307757994756077 1682210548990409248033529)
                    ·
                      refine ⟨1261657911742806936025147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682210548990409248033529 1261657911742806936025147)
                      ·
                        rfl

theorem cell23_2457070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_2457070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457070 prefixEnd_2457070 := by exact prefixLift 2457070
  have htrace : WordTrace (prefixWord ++ tailWord_2457070) baseStart_2457070 baseEnd_2457070 := by
    simpa [prefixWord, tailWord_2457070, baseEnd_2457070] using wordTrace_append hprefix tailTrace_2457070
  have hstable : (prefixWord ++ tailWord_2457070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457070).length < 2 ^ (prefixWord ++ tailWord_2457070).sum := by decide
  have hdescent : baseEnd_2457070 < baseStart_2457070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457079 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_2457079 : Nat := 118140960795 + 2457079 * 2 ^ 59
def prefixEnd_2457079 : Nat := 4983230072969 + 3 ^ 40 * 2457079 * 2
def baseEnd_2457079 : Nat := 1261662533068697400812605

theorem tailTrace_2457079 : CollatzResearch.WordTrace tailWord_2457079 prefixEnd_2457079 1261662533068697400812605 := by
  unfold tailWord_2457079
  simp only [CollatzResearch.WordTrace]
  refine ⟨89617033465429893529406291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59744688976953262352937527 89617033465429893529406291)
  ·
    refine ⟨134425550198144840294109437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89617033465429893529406291 134425550198144840294109437)
    ·
      refine ⟨50409581324304315110291039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134425550198144840294109437 50409581324304315110291039)
      ·
        refine ⟨75614371986456472665436559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50409581324304315110291039 75614371986456472665436559)
        ·
          refine ⟨113421557979684708998154839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75614371986456472665436559 113421557979684708998154839)
          ·
            refine ⟨170132336969527063497232259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113421557979684708998154839 170132336969527063497232259)
            ·
              refine ⟨255198505454290595245848389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170132336969527063497232259 255198505454290595245848389)
              ·
                refine ⟨47849719772679486608596573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255198505454290595245848389 47849719772679486608596573)
                ·
                  refine ⟨17943644914754807478223715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47849719772679486608596573 17943644914754807478223715)
                  ·
                    refine ⟨26915467372132211217335573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17943644914754807478223715 26915467372132211217335573)
                    ·
                      refine ⟨1261662533068697400812605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26915467372132211217335573 1261662533068697400812605)
                      ·
                        rfl

theorem cell23_2457079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_2457079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457079 prefixEnd_2457079 := by exact prefixLift 2457079
  have htrace : WordTrace (prefixWord ++ tailWord_2457079) baseStart_2457079 baseEnd_2457079 := by
    simpa [prefixWord, tailWord_2457079, baseEnd_2457079] using wordTrace_append hprefix tailTrace_2457079
  have hstable : (prefixWord ++ tailWord_2457079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457079).length < 2 ^ (prefixWord ++ tailWord_2457079).sum := by decide
  have hdescent : baseEnd_2457079 < baseStart_2457079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457083 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 5, 2, 2]
def baseStart_2457083 : Nat := 118140960795 + 2457083 * 2 ^ 59
def prefixEnd_2457083 : Nat := 4983230072969 + 3 ^ 40 * 2457083 * 2
def baseEnd_2457083 : Nat := 1261664586991315385162587

theorem tailTrace_2457083 : CollatzResearch.WordTrace tailWord_2457083 prefixEnd_2457083 1261664586991315385162587 := by
  unfold tailWord_2457083
  simp only [CollatzResearch.WordTrace]
  refine ⟨89617179357415402212551903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59744786238276934808367935 89617179357415402212551903)
  ·
    refine ⟨134425769036123103318827855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89617179357415402212551903 134425769036123103318827855)
    ·
      refine ⟨201638653554184654978241783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134425769036123103318827855 201638653554184654978241783)
      ·
        refine ⟨302457980331276982467362675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201638653554184654978241783 302457980331276982467362675)
        ·
          refine ⟨453686970496915473701044013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302457980331276982467362675 453686970496915473701044013)
          ·
            refine ⟨170132613936343302637891505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 453686970496915473701044013 170132613936343302637891505)
            ·
              refine ⟨127599460452257476978418629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170132613936343302637891505 127599460452257476978418629)
              ·
                refine ⟨23924898834798276933453493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127599460452257476978418629 23924898834798276933453493)
                ·
                  refine ⟨2242959265762338462511265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23924898834798276933453493 2242959265762338462511265)
                  ·
                    refine ⟨1682219449321753846883449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2242959265762338462511265 1682219449321753846883449)
                    ·
                      refine ⟨1261664586991315385162587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682219449321753846883449 1261664586991315385162587)
                      ·
                        rfl

theorem cell23_2457083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 2, 2].length) (baseStart_2457083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457083 prefixEnd_2457083 := by exact prefixLift 2457083
  have htrace : WordTrace (prefixWord ++ tailWord_2457083) baseStart_2457083 baseEnd_2457083 := by
    simpa [prefixWord, tailWord_2457083, baseEnd_2457083] using wordTrace_append hprefix tailTrace_2457083
  have hstable : (prefixWord ++ tailWord_2457083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457083).length < 2 ^ (prefixWord ++ tailWord_2457083).sum := by decide
  have hdescent : baseEnd_2457083 < baseStart_2457083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457089 : List Nat := [1, 2, 4, 1, 15]
def baseStart_2457089 : Nat := 118140960795 + 2457089 * 2 ^ 59
def prefixEnd_2457089 : Nat := 4983230072969 + 3 ^ 40 * 2457089 * 2
def baseEnd_2457089 : Nat := 1730682671982499810271

theorem tailTrace_2457089 : CollatzResearch.WordTrace tailWord_2457089 prefixEnd_2457089 1730682671982499810271 := by
  unfold tailWord_2457089
  simp only [CollatzResearch.WordTrace]
  refine ⟨89617398195393665237270321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59744932130262443491513547 89617398195393665237270321)
  ·
    refine ⟨67213048646545248927952741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89617398195393665237270321 67213048646545248927952741)
    ·
      refine ⟨12602446621227234173991139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67213048646545248927952741 12602446621227234173991139)
      ·
        refine ⟨18903669931840851260986709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12602446621227234173991139 18903669931840851260986709)
        ·
          refine ⟨1730682671982499810271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 18903669931840851260986709 1730682671982499810271)
          ·
            rfl

theorem cell23_2457089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 15].length) (baseStart_2457089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457089 prefixEnd_2457089 := by exact prefixLift 2457089
  have htrace : WordTrace (prefixWord ++ tailWord_2457089) baseStart_2457089 baseEnd_2457089 := by
    simpa [prefixWord, tailWord_2457089, baseEnd_2457089] using wordTrace_append hprefix tailTrace_2457089
  have hstable : (prefixWord ++ tailWord_2457089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457089).length < 2 ^ (prefixWord ++ tailWord_2457089).sum := by decide
  have hdescent : baseEnd_2457089 < baseStart_2457089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457123 : List Nat := [1, 1, 1, 4, 5, 1, 3, 7]
def baseStart_2457123 : Nat := 118140960795 + 2457123 * 2 ^ 59
def prefixEnd_2457123 : Nat := 4983230072969 + 3 ^ 40 * 2457123 * 2
def baseEnd_2457123 : Nat := 46729078748796119580089

theorem tailTrace_2457123 : CollatzResearch.WordTrace tailWord_2457123 prefixEnd_2457123 46729078748796119580089 := by
  unfold tailWord_2457123
  simp only [CollatzResearch.WordTrace]
  refine ⟨89618638277270489044008023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59745758851513659362672015 89618638277270489044008023)
  ·
    refine ⟨134427957415905733566012035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89618638277270489044008023 134427957415905733566012035)
    ·
      refine ⟨201641936123858600349018053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134427957415905733566012035 201641936123858600349018053)
      ·
        refine ⟨37807863023223487565440885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201641936123858600349018053 37807863023223487565440885)
        ·
          refine ⟨3544487158427201959260083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37807863023223487565440885 3544487158427201959260083)
          ·
            refine ⟨5316730737640802938890125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544487158427201959260083 5316730737640802938890125)
            ·
              refine ⟨1993774026615301102083797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5316730737640802938890125 1993774026615301102083797)
              ·
                refine ⟨46729078748796119580089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1993774026615301102083797 46729078748796119580089)
                ·
                  rfl

theorem cell23_2457123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 7].length) (baseStart_2457123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457123 prefixEnd_2457123 := by exact prefixLift 2457123
  have htrace : WordTrace (prefixWord ++ tailWord_2457123) baseStart_2457123 baseEnd_2457123 := by
    simpa [prefixWord, tailWord_2457123, baseEnd_2457123] using wordTrace_append hprefix tailTrace_2457123
  have hstable : (prefixWord ++ tailWord_2457123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457123).length < 2 ^ (prefixWord ++ tailWord_2457123).sum := by decide
  have hdescent : baseEnd_2457123 < baseStart_2457123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457129 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_2457129 : Nat := 118140960795 + 2457129 * 2 ^ 59
def prefixEnd_2457129 : Nat := 4983230072969 + 3 ^ 40 * 2457129 * 2
def baseEnd_2457129 : Nat := 1261688207101422205187375

theorem tailTrace_2457129 : CollatzResearch.WordTrace tailWord_2457129 prefixEnd_2457129 1261688207101422205187375 := by
  unfold tailWord_2457129
  simp only [CollatzResearch.WordTrace]
  refine ⟨89618857115248752068726441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59745904743499168045817627 89618857115248752068726441)
  ·
    refine ⟨67214142836436564051544831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89618857115248752068726441 67214142836436564051544831)
    ·
      refine ⟨100821214254654846077317247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67214142836436564051544831 100821214254654846077317247)
      ·
        refine ⟨151231821381982269115975871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100821214254654846077317247 151231821381982269115975871)
        ·
          refine ⟨226847732072973403673963807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151231821381982269115975871 226847732072973403673963807)
          ·
            refine ⟨340271598109460105510945711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226847732072973403673963807 340271598109460105510945711)
            ·
              refine ⟨510407397164190158266418567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340271598109460105510945711 510407397164190158266418567)
              ·
                refine ⟨765611095746285237399627851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510407397164190158266418567 765611095746285237399627851)
                ·
                  refine ⟨1148416643619427856099441777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765611095746285237399627851 1148416643619427856099441777)
                  ·
                    refine ⟨861312482714570892074581333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1148416643619427856099441777 861312482714570892074581333)
                    ·
                      refine ⟨1261688207101422205187375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 861312482714570892074581333 1261688207101422205187375)
                      ·
                        rfl

theorem cell23_2457129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_2457129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457129 prefixEnd_2457129 := by exact prefixLift 2457129
  have htrace : WordTrace (prefixWord ++ tailWord_2457129) baseStart_2457129 baseEnd_2457129 := by
    simpa [prefixWord, tailWord_2457129, baseEnd_2457129] using wordTrace_append hprefix tailTrace_2457129
  have hstable : (prefixWord ++ tailWord_2457129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457129).length < 2 ^ (prefixWord ++ tailWord_2457129).sum := by decide
  have hdescent : baseEnd_2457129 < baseStart_2457129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457134 : List Nat := [4, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_2457134 : Nat := 118140960795 + 2457134 * 2 ^ 59
def prefixEnd_2457134 : Nat := 4983230072969 + 3 ^ 40 * 2457134 * 2
def baseEnd_2457134 : Nat := 1261690774504694685624853

theorem tailTrace_2457134 : CollatzResearch.WordTrace tailWord_2457134 prefixEnd_2457134 1261690774504694685624853 := by
  unfold tailWord_2457134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11202379935028829740332307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59746026320153758615105637 11202379935028829740332307)
  ·
    refine ⟨16803569902543244610498461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11202379935028829740332307 16803569902543244610498461)
    ·
      refine ⟨6301338713453716728936923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16803569902543244610498461 6301338713453716728936923)
      ·
        refine ⟨9452008070180575093405385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6301338713453716728936923 9452008070180575093405385)
        ·
          refine ⟨7089006052635431320054039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9452008070180575093405385 7089006052635431320054039)
          ·
            refine ⟨10633509078953146980081059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7089006052635431320054039 10633509078953146980081059)
            ·
              refine ⟨15950263618429720470121589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10633509078953146980081059 15950263618429720470121589)
              ·
                refine ⟨1495337214227786294073899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15950263618429720470121589 1495337214227786294073899)
                ·
                  refine ⟨2243005821341679441110849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495337214227786294073899 2243005821341679441110849)
                  ·
                    refine ⟨1682254366006259580833137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2243005821341679441110849 1682254366006259580833137)
                    ·
                      refine ⟨1261690774504694685624853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682254366006259580833137 1261690774504694685624853)
                      ·
                        rfl

theorem cell23_2457134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_2457134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457134 prefixEnd_2457134 := by exact prefixLift 2457134
  have htrace : WordTrace (prefixWord ++ tailWord_2457134) baseStart_2457134 baseEnd_2457134 := by
    simpa [prefixWord, tailWord_2457134, baseEnd_2457134] using wordTrace_append hprefix tailTrace_2457134
  have hstable : (prefixWord ++ tailWord_2457134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457134).length < 2 ^ (prefixWord ++ tailWord_2457134).sum := by decide
  have hdescent : baseEnd_2457134 < baseStart_2457134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457174 : List Nat := [5, 2, 2, 2, 1, 2, 2, 7]
def baseStart_2457174 : Nat := 118140960795 + 2457174 * 2 ^ 59
def prefixEnd_2457174 : Nat := 4983230072969 + 3 ^ 40 * 2457174 * 2
def baseEnd_2457174 : Nat := 46730048656699056634247

theorem tailTrace_2457174 : CollatzResearch.WordTrace tailWord_2457174 prefixEnd_2457174 46730048656699056634247 := by
  unfold tailWord_2457174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5601281150005357797132161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59746998933390483169409717 5601281150005357797132161)
  ·
    refine ⟨4200960862504018347849121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5601281150005357797132161 4200960862504018347849121)
    ·
      refine ⟨3150720646878013760886841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4200960862504018347849121 3150720646878013760886841)
      ·
        refine ⟨2363040485158510320665131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3150720646878013760886841 2363040485158510320665131)
        ·
          refine ⟨3544560727737765480997697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363040485158510320665131 3544560727737765480997697)
          ·
            refine ⟨2658420545803324110748273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3544560727737765480997697 2658420545803324110748273)
            ·
              refine ⟨1993815409352493083061205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2658420545803324110748273 1993815409352493083061205)
              ·
                refine ⟨46730048656699056634247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1993815409352493083061205 46730048656699056634247)
                ·
                  rfl

theorem cell23_2457174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_2457174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457174 prefixEnd_2457174 := by exact prefixLift 2457174
  have htrace : WordTrace (prefixWord ++ tailWord_2457174) baseStart_2457174 baseEnd_2457174 := by
    simpa [prefixWord, tailWord_2457174, baseEnd_2457174] using wordTrace_append hprefix tailTrace_2457174
  have hstable : (prefixWord ++ tailWord_2457174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457174).length < 2 ^ (prefixWord ++ tailWord_2457174).sum := by decide
  have hdescent : baseEnd_2457174 < baseStart_2457174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457176 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2457176 : Nat := 118140960795 + 2457176 * 2 ^ 59
def prefixEnd_2457176 : Nat := 4983230072969 + 3 ^ 40 * 2457176 * 2
def baseEnd_2457176 : Nat := 1261712340692183521299659

theorem tailTrace_2457176 : CollatzResearch.WordTrace tailWord_2457176 prefixEnd_2457176 1261712340692183521299659 := by
  unfold tailWord_2457176
  simp only [CollatzResearch.WordTrace]
  refine ⟨44810285673039239547843691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59747047564052319397124921 44810285673039239547843691)
  ·
    refine ⟨67215428509558859321765537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44810285673039239547843691 67215428509558859321765537)
    ·
      refine ⟨50411571382169144491324153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67215428509558859321765537 50411571382169144491324153)
      ·
        refine ⟨37808678536626858368493115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50411571382169144491324153 37808678536626858368493115)
        ·
          refine ⟨56713017804940287552739673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37808678536626858368493115 56713017804940287552739673)
          ·
            refine ⟨42534763353705215664554755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56713017804940287552739673 42534763353705215664554755)
            ·
              refine ⟨63802145030557823496832133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42534763353705215664554755 63802145030557823496832133)
              ·
                refine ⟨11962902193229591905656025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63802145030557823496832133 11962902193229591905656025)
                ·
                  refine ⟨8972176644922193929242019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11962902193229591905656025 8972176644922193929242019)
                  ·
                    refine ⟨13458264967383290893863029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8972176644922193929242019 13458264967383290893863029)
                    ·
                      refine ⟨1261712340692183521299659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13458264967383290893863029 1261712340692183521299659)
                      ·
                        rfl

theorem cell23_2457176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2457176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457176 prefixEnd_2457176 := by exact prefixLift 2457176
  have htrace : WordTrace (prefixWord ++ tailWord_2457176) baseStart_2457176 baseEnd_2457176 := by
    simpa [prefixWord, tailWord_2457176, baseEnd_2457176] using wordTrace_append hprefix tailTrace_2457176
  have hstable : (prefixWord ++ tailWord_2457176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457176).length < 2 ^ (prefixWord ++ tailWord_2457176).sum := by decide
  have hdescent : baseEnd_2457176 < baseStart_2457176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457213 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 7]
def baseStart_2457213 : Nat := 118140960795 + 2457213 * 2 ^ 59
def prefixEnd_2457213 : Nat := 4983230072969 + 3 ^ 40 * 2457213 * 2
def baseEnd_2457213 : Nat := 140192371052933319615221

theorem tailTrace_2457213 : CollatzResearch.WordTrace tailWord_2457213 prefixEnd_2457213 140192371052933319615221 := by
  unfold tailWord_2457213
  simp only [CollatzResearch.WordTrace]
  refine ⟨89621920846944434414784293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59747947231296289609856195 89621920846944434414784293)
  ·
    refine ⟨16804110158802081452772055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89621920846944434414784293 16804110158802081452772055)
    ·
      refine ⟨25206165238203122179158083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16804110158802081452772055 25206165238203122179158083)
      ·
        refine ⟨37809247857304683268737125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25206165238203122179158083 37809247857304683268737125)
        ·
          refine ⟨7089233973244628112888211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37809247857304683268737125 7089233973244628112888211)
          ·
            refine ⟨10633850959866942169332317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7089233973244628112888211 10633850959866942169332317)
            ·
              refine ⟨3987694109950103313499619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10633850959866942169332317 3987694109950103313499619)
              ·
                refine ⟨5981541164925154970249429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3987694109950103313499619 5981541164925154970249429)
                ·
                  refine ⟨140192371052933319615221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5981541164925154970249429 140192371052933319615221)
                  ·
                    rfl

theorem cell23_2457213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_2457213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457213 prefixEnd_2457213 := by exact prefixLift 2457213
  have htrace : WordTrace (prefixWord ++ tailWord_2457213) baseStart_2457213 baseEnd_2457213 := by
    simpa [prefixWord, tailWord_2457213, baseEnd_2457213] using wordTrace_append hprefix tailTrace_2457213
  have hstable : (prefixWord ++ tailWord_2457213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457213).length < 2 ^ (prefixWord ++ tailWord_2457213).sum := by decide
  have hdescent : baseEnd_2457213 < baseStart_2457213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457233 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 4, 5, 2]
def baseStart_2457233 : Nat := 118140960795 + 2457233 * 2 ^ 59
def prefixEnd_2457233 : Nat := 4983230072969 + 3 ^ 40 * 2457233 * 2
def baseEnd_2457233 : Nat := 1261741609089489798286897

theorem tailTrace_2457233 : CollatzResearch.WordTrace tailWord_2457233 prefixEnd_2457233 1261741609089489798286897 := by
  unfold tailWord_2457233
  simp only [CollatzResearch.WordTrace]
  refine ⟨89622650306871977830512353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59748433537914651887008235 89622650306871977830512353)
  ·
    refine ⟨67216987730153983372884265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89622650306871977830512353 67216987730153983372884265)
    ·
      refine ⟨50412740797615487529663199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67216987730153983372884265 50412740797615487529663199)
      ·
        refine ⟨75619111196423231294494799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50412740797615487529663199 75619111196423231294494799)
        ·
          refine ⟨113428666794634846941742199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75619111196423231294494799 113428666794634846941742199)
          ·
            refine ⟨170143000191952270412613299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113428666794634846941742199 170143000191952270412613299)
            ·
              refine ⟨255214500287928405618919949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170143000191952270412613299 255214500287928405618919949)
              ·
                refine ⟨95705437607973152107094981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255214500287928405618919949 95705437607973152107094981)
                ·
                  refine ⟨17944769551494966020080309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95705437607973152107094981 17944769551494966020080309)
                  ·
                    refine ⟨1682322145452653064382529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17944769551494966020080309 1682322145452653064382529)
                    ·
                      refine ⟨1261741609089489798286897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682322145452653064382529 1261741609089489798286897)
                      ·
                        rfl

theorem cell23_2457233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 5, 2].length) (baseStart_2457233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457233 prefixEnd_2457233 := by exact prefixLift 2457233
  have htrace : WordTrace (prefixWord ++ tailWord_2457233) baseStart_2457233 baseEnd_2457233 := by
    simpa [prefixWord, tailWord_2457233, baseEnd_2457233] using wordTrace_append hprefix tailTrace_2457233
  have hstable : (prefixWord ++ tailWord_2457233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457233).length < 2 ^ (prefixWord ++ tailWord_2457233).sum := by decide
  have hdescent : baseEnd_2457233 < baseStart_2457233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457263 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 4]
def baseStart_2457263 : Nat := 118140960795 + 2457263 * 2 ^ 59
def prefixEnd_2457263 : Nat := 4983230072969 + 3 ^ 40 * 2457263 * 2
def baseEnd_2457263 : Nat := 1261757013509124680911759

theorem tailTrace_2457263 : CollatzResearch.WordTrace tailWord_2457263 prefixEnd_2457263 1261757013509124680911759 := by
  unfold tailWord_2457263
  simp only [CollatzResearch.WordTrace]
  refine ⟨89623744496763292954104443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59749162997842195302736295 89623744496763292954104443)
  ·
    refine ⟨134435616745144939431156665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89623744496763292954104443 134435616745144939431156665)
    ·
      refine ⟨100826712558858704573367499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134435616745144939431156665 100826712558858704573367499)
      ·
        refine ⟨151240068838288056860051249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100826712558858704573367499 151240068838288056860051249)
        ·
          refine ⟨113430051628716042645038437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151240068838288056860051249 113430051628716042645038437)
          ·
            refine ⟨21268134680384257995944707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113430051628716042645038437 21268134680384257995944707)
            ·
              refine ⟨31902202020576386993917061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21268134680384257995944707 31902202020576386993917061)
              ·
                refine ⟨5981662878858072561359449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31902202020576386993917061 5981662878858072561359449)
                ·
                  refine ⟨4486247159143554421019587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5981662878858072561359449 4486247159143554421019587)
                  ·
                    refine ⟨6729370738715331631529381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4486247159143554421019587 6729370738715331631529381)
                    ·
                      refine ⟨1261757013509124680911759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6729370738715331631529381 1261757013509124680911759)
                      ·
                        rfl

theorem cell23_2457263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_2457263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457263 prefixEnd_2457263 := by exact prefixLift 2457263
  have htrace : WordTrace (prefixWord ++ tailWord_2457263) baseStart_2457263 baseEnd_2457263 := by
    simpa [prefixWord, tailWord_2457263, baseEnd_2457263] using wordTrace_append hprefix tailTrace_2457263
  have hstable : (prefixWord ++ tailWord_2457263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457263).length < 2 ^ (prefixWord ++ tailWord_2457263).sum := by decide
  have hdescent : baseEnd_2457263 < baseStart_2457263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457280 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 2, 4, 2]
def baseStart_2457280 : Nat := 118140960795 + 2457280 * 2 ^ 59
def prefixEnd_2457280 : Nat := 4983230072969 + 3 ^ 40 * 2457280 * 2
def baseEnd_2457280 : Nat := 1261765742680251114399181

theorem tailTrace_2457280 : CollatzResearch.WordTrace tailWord_2457280 prefixEnd_2457280 1261765742680251114399181 := by
  unfold tailWord_2457280
  simp only [CollatzResearch.WordTrace]
  refine ⟨44812182268850852428736647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59749576358467803238315529 44812182268850852428736647)
  ·
    refine ⟨67218273403276278643104971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44812182268850852428736647 67218273403276278643104971)
    ·
      refine ⟨100827410104914417964657457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67218273403276278643104971 100827410104914417964657457)
      ·
        refine ⟨75620557578685813473493093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100827410104914417964657457 75620557578685813473493093)
        ·
          refine ⟨14178854546003590026279955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75620557578685813473493093 14178854546003590026279955)
          ·
            refine ⟨21268281819005385039419933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14178854546003590026279955 21268281819005385039419933)
            ·
              refine ⟨7975605682127019389782475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21268281819005385039419933 7975605682127019389782475)
              ·
                refine ⟨11963408523190529084673713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7975605682127019389782475 11963408523190529084673713)
                ·
                  refine ⟨8972556392392896813505285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11963408523190529084673713 8972556392392896813505285)
                  ·
                    refine ⟨1682354323573668152532241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8972556392392896813505285 1682354323573668152532241)
                    ·
                      refine ⟨1261765742680251114399181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682354323573668152532241 1261765742680251114399181)
                      ·
                        rfl

theorem cell23_2457280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 4, 2].length) (baseStart_2457280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457280 prefixEnd_2457280 := by exact prefixLift 2457280
  have htrace : WordTrace (prefixWord ++ tailWord_2457280) baseStart_2457280 baseEnd_2457280 := by
    simpa [prefixWord, tailWord_2457280, baseEnd_2457280] using wordTrace_append hprefix tailTrace_2457280
  have hstable : (prefixWord ++ tailWord_2457280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457280).length < 2 ^ (prefixWord ++ tailWord_2457280).sum := by decide
  have hdescent : baseEnd_2457280 < baseStart_2457280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457320 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 6]
def baseStart_2457320 : Nat := 118140960795 + 2457320 * 2 ^ 59
def prefixEnd_2457320 : Nat := 4983230072969 + 3 ^ 40 * 2457320 * 2
def baseEnd_2457320 : Nat := 140198475767381217544333

theorem tailTrace_2457320 : CollatzResearch.WordTrace tailWord_2457320 prefixEnd_2457320 140198475767381217544333 := by
  unfold tailWord_2457320
  simp only [CollatzResearch.WordTrace]
  refine ⟨44812911728778395844464707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59750548971704527792619609 44812911728778395844464707)
  ·
    refine ⟨67219367593167593766697061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44812911728778395844464707 67219367593167593766697061)
    ·
      refine ⟨12603631423718923831255699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67219367593167593766697061 12603631423718923831255699)
      ·
        refine ⟨18905447135578385746883549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12603631423718923831255699 18905447135578385746883549)
        ·
          refine ⟨7089542675841894655081331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18905447135578385746883549 7089542675841894655081331)
          ·
            refine ⟨10634314013762841982621997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7089542675841894655081331 10634314013762841982621997)
            ·
              refine ⟨3987867755161065743483249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10634314013762841982621997 3987867755161065743483249)
              ·
                refine ⟨2990900816370799307612437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3987867755161065743483249 2990900816370799307612437)
                ·
                  refine ⟨140198475767381217544333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2990900816370799307612437 140198475767381217544333)
                  ·
                    rfl

theorem cell23_2457320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 6].length) (baseStart_2457320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457320 prefixEnd_2457320 := by exact prefixLift 2457320
  have htrace : WordTrace (prefixWord ++ tailWord_2457320) baseStart_2457320 baseEnd_2457320 := by
    simpa [prefixWord, tailWord_2457320, baseEnd_2457320] using wordTrace_append hprefix tailTrace_2457320
  have hstable : (prefixWord ++ tailWord_2457320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457320).length < 2 ^ (prefixWord ++ tailWord_2457320).sum := by decide
  have hdescent : baseEnd_2457320 < baseStart_2457320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457340 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 3, 5, 2]
def baseStart_2457340 : Nat := 118140960795 + 2457340 * 2 ^ 59
def prefixEnd_2457340 : Nat := 4983230072969 + 3 ^ 40 * 2457340 * 2
def baseEnd_2457340 : Nat := 1261796551519520879648905

theorem tailTrace_2457340 : CollatzResearch.WordTrace tailWord_2457340 prefixEnd_2457340 1261796551519520879648905 := by
  unfold tailWord_2457340
  simp only [CollatzResearch.WordTrace]
  refine ⟨44813276458742167552328737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59751035278322890069771649 44813276458742167552328737)
  ·
    refine ⟨33609957344056625664246553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44813276458742167552328737 33609957344056625664246553)
    ·
      refine ⟨25207468008042469248184915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33609957344056625664246553 25207468008042469248184915)
      ·
        refine ⟨37811202012063703872277373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25207468008042469248184915 37811202012063703872277373)
        ·
          refine ⟨14179200754523888952104015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37811202012063703872277373 14179200754523888952104015)
          ·
            refine ⟨21268801131785833428156023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14179200754523888952104015 21268801131785833428156023)
            ·
              refine ⟨31903201697678750142234035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21268801131785833428156023 31903201697678750142234035)
              ·
                refine ⟨47854802546518125213351053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31903201697678750142234035 47854802546518125213351053)
                ·
                  refine ⟨17945550954944296955006645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47854802546518125213351053 17945550954944296955006645)
                  ·
                    refine ⟨1682395402026027839531873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17945550954944296955006645 1682395402026027839531873)
                    ·
                      refine ⟨1261796551519520879648905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682395402026027839531873 1261796551519520879648905)
                      ·
                        rfl

theorem cell23_2457340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_2457340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457340 prefixEnd_2457340 := by exact prefixLift 2457340
  have htrace : WordTrace (prefixWord ++ tailWord_2457340) baseStart_2457340 baseEnd_2457340 := by
    simpa [prefixWord, tailWord_2457340, baseEnd_2457340] using wordTrace_append hprefix tailTrace_2457340
  have hstable : (prefixWord ++ tailWord_2457340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457340).length < 2 ^ (prefixWord ++ tailWord_2457340).sum := by decide
  have hdescent : baseEnd_2457340 < baseStart_2457340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457381 : List Nat := [1, 3, 1, 2, 3, 3, 3, 2, 1, 1, 3]
def baseStart_2457381 : Nat := 118140960795 + 2457381 * 2 ^ 59
def prefixEnd_2457381 : Nat := 4983230072969 + 3 ^ 40 * 2457381 * 2
def baseEnd_2457381 : Nat := 1261817604226355219236217

theorem tailTrace_2457381 : CollatzResearch.WordTrace tailWord_2457381 prefixEnd_2457381 1261817604226355219236217 := by
  unfold tailWord_2457381
  simp only [CollatzResearch.WordTrace]
  refine ⟨89628048310335799106899997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59752032206890532737933331 89628048310335799106899997)
  ·
    refine ⟨33610518116375924665087499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89628048310335799106899997 33610518116375924665087499)
    ·
      refine ⟨50415777174563886997631249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33610518116375924665087499 50415777174563886997631249)
      ·
        refine ⟨37811832880922915248223437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50415777174563886997631249 37811832880922915248223437)
        ·
          refine ⟨14179437330346093218083789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37811832880922915248223437 14179437330346093218083789)
          ·
            refine ⟨5317288998879784956781421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14179437330346093218083789 5317288998879784956781421)
            ·
              refine ⟨1993983374579919358793033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5317288998879784956781421 1993983374579919358793033)
              ·
                refine ⟨1495487530934939519094775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993983374579919358793033 1495487530934939519094775)
                ·
                  refine ⟨2243231296402409278642163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495487530934939519094775 2243231296402409278642163)
                  ·
                    refine ⟨3364846944603613917963245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2243231296402409278642163 3364846944603613917963245)
                    ·
                      refine ⟨1261817604226355219236217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3364846944603613917963245 1261817604226355219236217)
                      ·
                        rfl

theorem cell23_2457381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_2457381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457381 prefixEnd_2457381 := by exact prefixLift 2457381
  have htrace : WordTrace (prefixWord ++ tailWord_2457381) baseStart_2457381 baseEnd_2457381 := by
    simpa [prefixWord, tailWord_2457381, baseEnd_2457381] using wordTrace_append hprefix tailTrace_2457381
  have hstable : (prefixWord ++ tailWord_2457381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457381).length < 2 ^ (prefixWord ++ tailWord_2457381).sum := by decide
  have hdescent : baseEnd_2457381 < baseStart_2457381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457393 : List Nat := [1, 2, 2, 3, 2, 2, 1, 10]
def baseStart_2457393 : Nat := 118140960795 + 2457393 * 2 ^ 59
def prefixEnd_2457393 : Nat := 4983230072969 + 3 ^ 40 * 2457393 * 2
def baseEnd_2457393 : Nat := 46734213555341080455043

theorem tailTrace_2457393 : CollatzResearch.WordTrace tailWord_2457393 prefixEnd_2457393 46734213555341080455043 := by
  unfold tailWord_2457393
  simp only [CollatzResearch.WordTrace]
  refine ⟨89628485986292325156336833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59752323990861550104224555 89628485986292325156336833)
  ·
    refine ⟨67221364489719243867252625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89628485986292325156336833 67221364489719243867252625)
    ·
      refine ⟨50416023367289432900439469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67221364489719243867252625 50416023367289432900439469)
      ·
        refine ⟨18906008762733537337664801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50416023367289432900439469 18906008762733537337664801)
        ·
          refine ⟨14179506572050153003248601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18906008762733537337664801 14179506572050153003248601)
          ·
            refine ⟨10634629929037614752436451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14179506572050153003248601 10634629929037614752436451)
            ·
              refine ⟨15951944893556422128654677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10634629929037614752436451 15951944893556422128654677)
              ·
                refine ⟨46734213555341080455043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15951944893556422128654677 46734213555341080455043)
                ·
                  rfl

theorem cell23_2457393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 10].length) (baseStart_2457393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457393 prefixEnd_2457393 := by exact prefixLift 2457393
  have htrace : WordTrace (prefixWord ++ tailWord_2457393) baseStart_2457393 baseEnd_2457393 := by
    simpa [prefixWord, tailWord_2457393, baseEnd_2457393] using wordTrace_append hprefix tailTrace_2457393
  have hstable : (prefixWord ++ tailWord_2457393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457393).length < 2 ^ (prefixWord ++ tailWord_2457393).sum := by decide
  have hdescent : baseEnd_2457393 < baseStart_2457393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457401 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 1, 5]
def baseStart_2457401 : Nat := 118140960795 + 2457401 * 2 ^ 59
def prefixEnd_2457401 : Nat := 4983230072969 + 3 ^ 40 * 2457401 * 2
def baseEnd_2457401 : Nat := 420609291279815046995375

theorem tailTrace_2457401 : CollatzResearch.WordTrace tailWord_2457401 prefixEnd_2457401 420609291279815046995375 := by
  unfold tailWord_2457401
  simp only [CollatzResearch.WordTrace]
  refine ⟨89628777770263342522628057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59752518513508895015085371 89628777770263342522628057)
  ·
    refine ⟨67221583327697506891971043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89628777770263342522628057 67221583327697506891971043)
    ·
      refine ⟨100832374991546260337956565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67221583327697506891971043 100832374991546260337956565)
      ·
        refine ⟨2363258788864365476670857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 100832374991546260337956565 2363258788864365476670857)
        ·
          refine ⟨1772444091648274107503143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2363258788864365476670857 1772444091648274107503143)
          ·
            refine ⟨2658666137472411161254715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772444091648274107503143 2658666137472411161254715)
            ·
              refine ⟨3987999206208616741882073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658666137472411161254715 3987999206208616741882073)
              ·
                refine ⟨2990999404656462556411555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3987999206208616741882073 2990999404656462556411555)
                ·
                  refine ⟨4486499106984693834617333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990999404656462556411555 4486499106984693834617333)
                  ·
                    refine ⟨420609291279815046995375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4486499106984693834617333 420609291279815046995375)
                    ·
                      rfl

theorem cell23_2457401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 5].length) (baseStart_2457401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457401 prefixEnd_2457401 := by exact prefixLift 2457401
  have htrace : WordTrace (prefixWord ++ tailWord_2457401) baseStart_2457401 baseEnd_2457401 := by
    simpa [prefixWord, tailWord_2457401, baseEnd_2457401] using wordTrace_append hprefix tailTrace_2457401
  have hstable : (prefixWord ++ tailWord_2457401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457401).length < 2 ^ (prefixWord ++ tailWord_2457401).sum := by decide
  have hdescent : baseEnd_2457401 < baseStart_2457401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457407 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 3]
def baseStart_2457407 : Nat := 118140960795 + 2457407 * 2 ^ 59
def prefixEnd_2457407 : Nat := 4983230072969 + 3 ^ 40 * 2457407 * 2
def baseEnd_2457407 : Nat := 1261830954723372117511097

theorem tailTrace_2457407 : CollatzResearch.WordTrace tailWord_2457407 prefixEnd_2457407 1261830954723372117511097 := by
  unfold tailWord_2457407
  simp only [CollatzResearch.WordTrace]
  refine ⟨89628996608241605547346475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59752664405494403698230983 89628996608241605547346475)
  ·
    refine ⟨134443494912362408321019713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89628996608241605547346475 134443494912362408321019713)
    ·
      refine ⟨100832621184271806240764785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134443494912362408321019713 100832621184271806240764785)
      ·
        refine ⟨75624465888203854680573589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100832621184271806240764785 75624465888203854680573589)
        ·
          refine ⟨3544896838509555688151887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75624465888203854680573589 3544896838509555688151887)
          ·
            refine ⟨5317345257764333532227831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544896838509555688151887 5317345257764333532227831)
            ·
              refine ⟨7976017886646500298341747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5317345257764333532227831 7976017886646500298341747)
              ·
                refine ⟨11964026829969750447512621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7976017886646500298341747 11964026829969750447512621)
                ·
                  refine ⟨4486510061238656417817233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11964026829969750447512621 4486510061238656417817233)
                  ·
                    refine ⟨3364882545928992313362925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4486510061238656417817233 3364882545928992313362925)
                    ·
                      refine ⟨1261830954723372117511097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3364882545928992313362925 1261830954723372117511097)
                      ·
                        rfl

theorem cell23_2457407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_2457407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457407 prefixEnd_2457407 := by exact prefixLift 2457407
  have htrace : WordTrace (prefixWord ++ tailWord_2457407) baseStart_2457407 baseEnd_2457407 := by
    simpa [prefixWord, tailWord_2457407, baseEnd_2457407] using wordTrace_append hprefix tailTrace_2457407
  have hstable : (prefixWord ++ tailWord_2457407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457407).length < 2 ^ (prefixWord ++ tailWord_2457407).sum := by decide
  have hdescent : baseEnd_2457407 < baseStart_2457407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457414 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_2457414 : Nat := 118140960795 + 2457414 * 2 ^ 59
def prefixEnd_2457414 : Nat := 4983230072969 + 3 ^ 40 * 2457414 * 2
def baseEnd_2457414 : Nat := 420611516362651196707855

theorem tailTrace_2457414 : CollatzResearch.WordTrace tailWord_2457414 prefixEnd_2457414 420611516362651196707855 := by
  unfold tailWord_2457414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800914122475507679464103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59752834612810830495234197 2800914122475507679464103)
  ·
    refine ⟨4201371183713261519196155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2800914122475507679464103 4201371183713261519196155)
    ·
      refine ⟨6302056775569892278794233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4201371183713261519196155 6302056775569892278794233)
      ·
        refine ⟨4726542581677419209095675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6302056775569892278794233 4726542581677419209095675)
        ·
          refine ⟨7089813872516128813643513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4726542581677419209095675 7089813872516128813643513)
          ·
            refine ⟨5317360404387096610232635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7089813872516128813643513 5317360404387096610232635)
            ·
              refine ⟨7976040606580644915348953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5317360404387096610232635 7976040606580644915348953)
              ·
                refine ⟨5982030454935483686511715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7976040606580644915348953 5982030454935483686511715)
                ·
                  refine ⟨8973045682403225529767573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5982030454935483686511715 8973045682403225529767573)
                  ·
                    refine ⟨420611516362651196707855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8973045682403225529767573 420611516362651196707855)
                    ·
                      rfl

theorem cell23_2457414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_2457414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457414 prefixEnd_2457414 := by exact prefixLift 2457414
  have htrace : WordTrace (prefixWord ++ tailWord_2457414) baseStart_2457414 baseEnd_2457414 := by
    simpa [prefixWord, tailWord_2457414, baseEnd_2457414] using wordTrace_append hprefix tailTrace_2457414
  have hstable : (prefixWord ++ tailWord_2457414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457414).length < 2 ^ (prefixWord ++ tailWord_2457414).sum := by decide
  have hdescent : baseEnd_2457414 < baseStart_2457414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457421 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_2457421 : Nat := 118140960795 + 2457421 * 2 ^ 59
def prefixEnd_2457421 : Nat := 4983230072969 + 3 ^ 40 * 2457421 * 2
def baseEnd_2457421 : Nat := 1261838143452535062736033

theorem tailTrace_2457421 : CollatzResearch.WordTrace tailWord_2457421 prefixEnd_2457421 1261838143452535062736033 := by
  unfold tailWord_2457421
  simp only [CollatzResearch.WordTrace]
  refine ⟨89629507230190885938356117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59753004820127257292237411 89629507230190885938356117)
  ·
    refine ⟨4201383151415197778360443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89629507230190885938356117 4201383151415197778360443)
    ·
      refine ⟨6302074727122796667540665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4201383151415197778360443 6302074727122796667540665)
      ·
        refine ⟨4726556045342097500655499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6302074727122796667540665 4726556045342097500655499)
        ·
          refine ⟨7089834068013146250983249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4726556045342097500655499 7089834068013146250983249)
          ·
            refine ⟨5317375551009859688237437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7089834068013146250983249 5317375551009859688237437)
            ·
              refine ⟨1994015831628697383089039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5317375551009859688237437 1994015831628697383089039)
              ·
                refine ⟨2991023747443046074633559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1994015831628697383089039 2991023747443046074633559)
                ·
                  refine ⟨4486535621164569111950339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991023747443046074633559 4486535621164569111950339)
                  ·
                    refine ⟨6729803431746853667925509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4486535621164569111950339 6729803431746853667925509)
                    ·
                      refine ⟨1261838143452535062736033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6729803431746853667925509 1261838143452535062736033)
                      ·
                        rfl

theorem cell23_2457421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_2457421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457421 prefixEnd_2457421 := by exact prefixLift 2457421
  have htrace : WordTrace (prefixWord ++ tailWord_2457421) baseStart_2457421 baseEnd_2457421 := by
    simpa [prefixWord, tailWord_2457421, baseEnd_2457421] using wordTrace_append hprefix tailTrace_2457421
  have hstable : (prefixWord ++ tailWord_2457421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457421).length < 2 ^ (prefixWord ++ tailWord_2457421).sum := by decide
  have hdescent : baseEnd_2457421 < baseStart_2457421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457447 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_2457447 : Nat := 118140960795 + 2457447 * 2 ^ 59
def prefixEnd_2457447 : Nat := 4983230072969 + 3 ^ 40 * 2457447 * 2
def baseEnd_2457447 : Nat := 1261851493949551961010913

theorem tailTrace_2457447 : CollatzResearch.WordTrace tailWord_2457447 prefixEnd_2457447 1261851493949551961010913 := by
  unfold tailWord_2457447
  simp only [CollatzResearch.WordTrace]
  refine ⟨89630455528096692378802595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59753637018731128252535063 89630455528096692378802595)
  ·
    refine ⟨134445683292145038568203893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89630455528096692378802595 134445683292145038568203893)
    ·
      refine ⟨12604282808638597365769115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134445683292145038568203893 12604282808638597365769115)
      ·
        refine ⟨18906424212957896048653673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12604282808638597365769115 18906424212957896048653673)
        ·
          refine ⟨14179818159718422036490255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18906424212957896048653673 14179818159718422036490255)
          ·
            refine ⟨21269727239577633054735383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14179818159718422036490255 21269727239577633054735383)
            ·
              refine ⟨31904590859366449582103075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21269727239577633054735383 31904590859366449582103075)
              ·
                refine ⟨47856886289049674373154613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31904590859366449582103075 47856886289049674373154613)
                ·
                  refine ⟨4486583089598406972483245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47856886289049674373154613 4486583089598406972483245)
                  ·
                    refine ⟨1682468658599402614681217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4486583089598406972483245 1682468658599402614681217)
                    ·
                      refine ⟨1261851493949551961010913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682468658599402614681217 1261851493949551961010913)
                      ·
                        rfl

theorem cell23_2457447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_2457447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457447 prefixEnd_2457447 := by exact prefixLift 2457447
  have htrace : WordTrace (prefixWord ++ tailWord_2457447) baseStart_2457447 baseEnd_2457447 := by
    simpa [prefixWord, tailWord_2457447, baseEnd_2457447] using wordTrace_append hprefix tailTrace_2457447
  have hstable : (prefixWord ++ tailWord_2457447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457447).length < 2 ^ (prefixWord ++ tailWord_2457447).sum := by decide
  have hdescent : baseEnd_2457447 < baseStart_2457447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457454 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2457454 : Nat := 118140960795 + 2457454 * 2 ^ 59
def prefixEnd_2457454 : Nat := 4983230072969 + 3 ^ 40 * 2457454 * 2
def baseEnd_2457454 : Nat := 1261855088314133433623381

theorem tailTrace_2457454 : CollatzResearch.WordTrace tailWord_2457454 prefixEnd_2457454 1261855088314133433623381 := by
  unfold tailWord_2457454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11203838854883916571788427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59753807226047555049538277 11203838854883916571788427)
  ·
    refine ⟨16805758282325874857682641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11203838854883916571788427 16805758282325874857682641)
    ·
      refine ⟨12604318711744406143261981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16805758282325874857682641 12604318711744406143261981)
      ·
        refine ⟨4726619516904152303723243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12604318711744406143261981 4726619516904152303723243)
        ·
          refine ⟨7089929275356228455584865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4726619516904152303723243 7089929275356228455584865)
          ·
            refine ⟨5317446956517171341688649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7089929275356228455584865 5317446956517171341688649)
            ·
              refine ⟨3988085217387878506266487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5317446956517171341688649 3988085217387878506266487)
              ·
                refine ⟨5982127826081817759399731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988085217387878506266487 5982127826081817759399731)
                ·
                  refine ⟨8973191739122726639099597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5982127826081817759399731 8973191739122726639099597)
                  ·
                    refine ⟨3364946902171022489662349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8973191739122726639099597 3364946902171022489662349)
                    ·
                      refine ⟨1261855088314133433623381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3364946902171022489662349 1261855088314133433623381)
                      ·
                        rfl

theorem cell23_2457454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2457454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457454 prefixEnd_2457454 := by exact prefixLift 2457454
  have htrace : WordTrace (prefixWord ++ tailWord_2457454) baseStart_2457454 baseEnd_2457454 := by
    simpa [prefixWord, tailWord_2457454, baseEnd_2457454] using wordTrace_append hprefix tailTrace_2457454
  have hstable : (prefixWord ++ tailWord_2457454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457454).length < 2 ^ (prefixWord ++ tailWord_2457454).sum := by decide
  have hdescent : baseEnd_2457454 < baseStart_2457454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457477 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 1, 4, 2]
def baseStart_2457477 : Nat := 118140960795 + 2457477 * 2 ^ 59
def prefixEnd_2457477 : Nat := 4983230072969 + 3 ^ 40 * 2457477 * 2
def baseEnd_2457477 : Nat := 1261866898369186843635775

theorem tailTrace_2457477 : CollatzResearch.WordTrace tailWord_2457477 prefixEnd_2457477 1261866898369186843635775 := by
  unfold tailWord_2457477
  simp only [CollatzResearch.WordTrace]
  refine ⟨89631549717988007502394685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59754366478658671668263123 89631549717988007502394685)
  ·
    refine ⟨33611831144245502813398007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89631549717988007502394685 33611831144245502813398007)
    ·
      refine ⟨50417746716368254220097011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33611831144245502813398007 50417746716368254220097011)
      ·
        refine ⟨75626620074552381330145517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50417746716368254220097011 75626620074552381330145517)
        ·
          refine ⟨28359982527957142998804569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75626620074552381330145517 28359982527957142998804569)
          ·
            refine ⟨21269986895967857249103427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28359982527957142998804569 21269986895967857249103427)
            ·
              refine ⟨31904980343951785873655141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21269986895967857249103427 31904980343951785873655141)
              ·
                refine ⟨5982183814490959851310339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31904980343951785873655141 5982183814490959851310339)
                ·
                  refine ⟨8973275721736439776965509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5982183814490959851310339 8973275721736439776965509)
                  ·
                    refine ⟨1682489197825582458181033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8973275721736439776965509 1682489197825582458181033)
                    ·
                      refine ⟨1261866898369186843635775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682489197825582458181033 1261866898369186843635775)
                      ·
                        rfl

theorem cell23_2457477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 4, 2].length) (baseStart_2457477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457477 prefixEnd_2457477 := by exact prefixLift 2457477
  have htrace : WordTrace (prefixWord ++ tailWord_2457477) baseStart_2457477 baseEnd_2457477 := by
    simpa [prefixWord, tailWord_2457477, baseEnd_2457477] using wordTrace_append hprefix tailTrace_2457477
  have hstable : (prefixWord ++ tailWord_2457477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457477).length < 2 ^ (prefixWord ++ tailWord_2457477).sum := by decide
  have hdescent : baseEnd_2457477 < baseStart_2457477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457483 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 11]
def baseStart_2457483 : Nat := 118140960795 + 2457483 * 2 ^ 59
def prefixEnd_2457483 : Nat := 4983230072969 + 3 ^ 40 * 2457483 * 2
def baseEnd_2457483 : Nat := 140207775472568202240083

theorem tailTrace_2457483 : CollatzResearch.WordTrace tailWord_2457483 prefixEnd_2457483 140207775472568202240083 := by
  unfold tailWord_2457483
  simp only [CollatzResearch.WordTrace]
  refine ⟨89631768555966270527113103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59754512370644180351408735 89631768555966270527113103)
  ·
    refine ⟨134447652833949405790669655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89631768555966270527113103 134447652833949405790669655)
    ·
      refine ⟨201671479250924108686004483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134447652833949405790669655 201671479250924108686004483)
      ·
        refine ⟨302507218876386163029006725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201671479250924108686004483 302507218876386163029006725)
        ·
          refine ⟨56720103539322405567938761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302507218876386163029006725 56720103539322405567938761)
          ·
            refine ⟨42540077654491804175954071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56720103539322405567938761 42540077654491804175954071)
            ·
              refine ⟨63810116481737706263931107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42540077654491804175954071 63810116481737706263931107)
              ·
                refine ⟨95715174722606559395896661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63810116481737706263931107 95715174722606559395896661)
                ·
                  refine ⟨140207775472568202240083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 95715174722606559395896661 140207775472568202240083)
                  ·
                    rfl

theorem cell23_2457483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 11].length) (baseStart_2457483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457483 prefixEnd_2457483 := by exact prefixLift 2457483
  have htrace : WordTrace (prefixWord ++ tailWord_2457483) baseStart_2457483 baseEnd_2457483 := by
    simpa [prefixWord, tailWord_2457483, baseEnd_2457483] using wordTrace_append hprefix tailTrace_2457483
  have hstable : (prefixWord ++ tailWord_2457483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457483).length < 2 ^ (prefixWord ++ tailWord_2457483).sum := by decide
  have hdescent : baseEnd_2457483 < baseStart_2457483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457511 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_2457511 : Nat := 118140960795 + 2457511 * 2 ^ 59
def prefixEnd_2457511 : Nat := 4983230072969 + 3 ^ 40 * 2457511 * 2
def baseEnd_2457511 : Nat := 1261884356711439710610619

theorem tailTrace_2457511 : CollatzResearch.WordTrace tailWord_2457511 prefixEnd_2457511 1261884356711439710610619 := by
  unfold tailWord_2457511
  simp only [CollatzResearch.WordTrace]
  refine ⟨89632789799864831309132387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59755193199909887539421591 89632789799864831309132387)
  ·
    refine ⟨134449184699797246963698581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89632789799864831309132387 134449184699797246963698581)
    ·
      refine ⟨6302305532802995951423371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 134449184699797246963698581 6302305532802995951423371)
      ·
        refine ⟨9453458299204493927135057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6302305532802995951423371 9453458299204493927135057)
        ·
          refine ⟨7090093724403370445351293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9453458299204493927135057 7090093724403370445351293)
          ·
            refine ⟨2658785146651263917006735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7090093724403370445351293 2658785146651263917006735)
            ·
              refine ⟨3988177719976895875510103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658785146651263917006735 3988177719976895875510103)
              ·
                refine ⟨5982266579965343813265155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988177719976895875510103 5982266579965343813265155)
                ·
                  refine ⟨8973399869948015719897733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5982266579965343813265155 8973399869948015719897733)
                  ·
                    refine ⟨1682512475615252947480825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8973399869948015719897733 1682512475615252947480825)
                    ·
                      refine ⟨1261884356711439710610619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682512475615252947480825 1261884356711439710610619)
                      ·
                        rfl

theorem cell23_2457511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_2457511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457511 prefixEnd_2457511 := by exact prefixLift 2457511
  have htrace : WordTrace (prefixWord ++ tailWord_2457511) baseStart_2457511 baseEnd_2457511 := by
    simpa [prefixWord, tailWord_2457511, baseEnd_2457511] using wordTrace_append hprefix tailTrace_2457511
  have hstable : (prefixWord ++ tailWord_2457511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457511).length < 2 ^ (prefixWord ++ tailWord_2457511).sum := by decide
  have hdescent : baseEnd_2457511 < baseStart_2457511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457534 : List Nat := [4, 2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_2457534 : Nat := 118140960795 + 2457534 * 2 ^ 59
def prefixEnd_2457534 : Nat := 4983230072969 + 3 ^ 40 * 2457534 * 2
def baseEnd_2457534 : Nat := 140210685196277013402557

theorem tailTrace_2457534 : CollatzResearch.WordTrace tailWord_2457534 prefixEnd_2457534 140210685196277013402557 := by
  unfold tailWord_2457534
  simp only [CollatzResearch.WordTrace]
  refine ⟨11204203584847688279652457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59755752452521004158146437 11204203584847688279652457)
  ·
    refine ⟨8403152688635766209739343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11204203584847688279652457 8403152688635766209739343)
    ·
      refine ⟨12604729032953649314609015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8403152688635766209739343 12604729032953649314609015)
      ·
        refine ⟨18907093549430473971913523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12604729032953649314609015 18907093549430473971913523)
        ·
          refine ⟨28360640324145710957870285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18907093549430473971913523 28360640324145710957870285)
          ·
            refine ⟨10635240121554641609201357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28360640324145710957870285 10635240121554641609201357)
            ·
              refine ⟨3988215045582990603450509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10635240121554641609201357 3988215045582990603450509)
              ·
                refine ⟨1495580642093621476293941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3988215045582990603450509 1495580642093621476293941)
                ·
                  refine ⟨140210685196277013402557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1495580642093621476293941 140210685196277013402557)
                  ·
                    rfl

theorem cell23_2457534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_2457534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457534 prefixEnd_2457534 := by exact prefixLift 2457534
  have htrace : WordTrace (prefixWord ++ tailWord_2457534) baseStart_2457534 baseEnd_2457534 := by
    simpa [prefixWord, tailWord_2457534, baseEnd_2457534] using wordTrace_append hprefix tailTrace_2457534
  have hstable : (prefixWord ++ tailWord_2457534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457534).length < 2 ^ (prefixWord ++ tailWord_2457534).sum := by decide
  have hdescent : baseEnd_2457534 < baseStart_2457534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457557 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2457557 : Nat := 118140960795 + 2457557 * 2 ^ 59
def prefixEnd_2457557 : Nat := 4983230072969 + 3 ^ 40 * 2457557 * 2
def baseEnd_2457557 : Nat := 1261907976821546530635407

theorem tailTrace_2457557 : CollatzResearch.WordTrace tailWord_2457557 prefixEnd_2457557 1261907976821546530635407 := by
  unfold tailWord_2457557
  simp only [CollatzResearch.WordTrace]
  refine ⟨89634467557698181165306925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59756311705132120776871283 89634467557698181165306925)
  ·
    refine ⟨33612925334136817936990097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89634467557698181165306925 33612925334136817936990097)
    ·
      refine ⟨25209694000602613452742573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33612925334136817936990097 25209694000602613452742573)
      ·
        refine ⟨9453635250225980044778465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25209694000602613452742573 9453635250225980044778465)
        ·
          refine ⟨7090226437669485033583849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9453635250225980044778465 7090226437669485033583849)
          ·
            refine ⟨5317669828252113775187887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7090226437669485033583849 5317669828252113775187887)
            ·
              refine ⟨7976504742378170662781831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5317669828252113775187887 7976504742378170662781831)
              ·
                refine ⟨11964757113567255994172747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7976504742378170662781831 11964757113567255994172747)
                ·
                  refine ⟨17947135670350883991259121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11964757113567255994172747 17947135670350883991259121)
                  ·
                    refine ⟨13460351752763162993444341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17947135670350883991259121 13460351752763162993444341)
                    ·
                      refine ⟨1261907976821546530635407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13460351752763162993444341 1261907976821546530635407)
                      ·
                        rfl

theorem cell23_2457557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2457557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457557 prefixEnd_2457557 := by exact prefixLift 2457557
  have htrace : WordTrace (prefixWord ++ tailWord_2457557) baseStart_2457557 baseEnd_2457557 := by
    simpa [prefixWord, tailWord_2457557, baseEnd_2457557] using wordTrace_append hprefix tailTrace_2457557
  have hstable : (prefixWord ++ tailWord_2457557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457557).length < 2 ^ (prefixWord ++ tailWord_2457557).sum := by decide
  have hdescent : baseEnd_2457557 < baseStart_2457557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457580 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_2457580 : Nat := 118140960795 + 2457580 * 2 ^ 59
def prefixEnd_2457580 : Nat := 4983230072969 + 3 ^ 40 * 2457580 * 2
def baseEnd_2457580 : Nat := 1261919786876599940647801

theorem tailTrace_2457580 : CollatzResearch.WordTrace tailWord_2457580 prefixEnd_2457580 1261919786876599940647801 := by
  unfold tailWord_2457580
  simp only [CollatzResearch.WordTrace]
  refine ⟨44817653218307428046697097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59756870957743237395596129 44817653218307428046697097)
  ·
    refine ⟨33613239913730571035022823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44817653218307428046697097 33613239913730571035022823)
    ·
      refine ⟨50419859870595856552534235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33613239913730571035022823 50419859870595856552534235)
      ·
        refine ⟨75629789805893784828801353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50419859870595856552534235 75629789805893784828801353)
        ·
          refine ⟨56722342354420338621601015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75629789805893784828801353 56722342354420338621601015)
          ·
            refine ⟨85083513531630507932401523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56722342354420338621601015 85083513531630507932401523)
            ·
              refine ⟨127625270297445761898602285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85083513531630507932401523 127625270297445761898602285)
              ·
                refine ⟨47859476361542160711975857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127625270297445761898602285 47859476361542160711975857)
                ·
                  refine ⟨35894607271156620533981893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47859476361542160711975857 35894607271156620533981893)
                  ·
                    refine ⟨6730238863341866350121605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35894607271156620533981893 6730238863341866350121605)
                    ·
                      refine ⟨1261919786876599940647801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6730238863341866350121605 1261919786876599940647801)
                      ·
                        rfl

theorem cell23_2457580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_2457580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457580 prefixEnd_2457580 := by exact prefixLift 2457580
  have htrace : WordTrace (prefixWord ++ tailWord_2457580) baseStart_2457580 baseEnd_2457580 := by
    simpa [prefixWord, tailWord_2457580, baseEnd_2457580] using wordTrace_append hprefix tailTrace_2457580
  have hstable : (prefixWord ++ tailWord_2457580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457580).length < 2 ^ (prefixWord ++ tailWord_2457580).sum := by decide
  have hdescent : baseEnd_2457580 < baseStart_2457580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457581 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_2457581 : Nat := 118140960795 + 2457581 * 2 ^ 59
def prefixEnd_2457581 : Nat := 4983230072969 + 3 ^ 40 * 2457581 * 2
def baseEnd_2457581 : Nat := 420640100119084812245099

theorem tailTrace_2457581 : CollatzResearch.WordTrace tailWord_2457581 prefixEnd_2457581 420640100119084812245099 := by
  unfold tailWord_2457581
  simp only [CollatzResearch.WordTrace]
  refine ⟨89635342909611233264180597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59756895273074155509453731 89635342909611233264180597)
  ·
    refine ⟨8403313397776053118516931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89635342909611233264180597 8403313397776053118516931)
    ·
      refine ⟨12604970096664079677775397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8403313397776053118516931 12604970096664079677775397)
      ·
        refine ⟨2363431893124514939582887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12604970096664079677775397 2363431893124514939582887)
        ·
          refine ⟨3545147839686772409374331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363431893124514939582887 3545147839686772409374331)
          ·
            refine ⟨5317721759530158614061497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545147839686772409374331 5317721759530158614061497)
            ·
              refine ⟨3988291319647618960546123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5317721759530158614061497 3988291319647618960546123)
              ·
                refine ⟨5982436979471428440819185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988291319647618960546123 5982436979471428440819185)
                ·
                  refine ⟨4486827734603571330614389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5982436979471428440819185 4486827734603571330614389)
                  ·
                    refine ⟨420640100119084812245099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4486827734603571330614389 420640100119084812245099)
                    ·
                      rfl

theorem cell23_2457581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_2457581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457581 prefixEnd_2457581 := by exact prefixLift 2457581
  have htrace : WordTrace (prefixWord ++ tailWord_2457581) baseStart_2457581 baseEnd_2457581 := by
    simpa [prefixWord, tailWord_2457581, baseEnd_2457581] using wordTrace_append hprefix tailTrace_2457581
  have hstable : (prefixWord ++ tailWord_2457581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457581).length < 2 ^ (prefixWord ++ tailWord_2457581).sum := by decide
  have hdescent : baseEnd_2457581 < baseStart_2457581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457607 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 6]
def baseStart_2457607 : Nat := 118140960795 + 2457607 * 2 ^ 59
def prefixEnd_2457607 : Nat := 4983230072969 + 3 ^ 40 * 2457607 * 2
def baseEnd_2457607 : Nat := 140214850094919037223353

theorem tailTrace_2457607 : CollatzResearch.WordTrace tailWord_2457607 prefixEnd_2457607 140214850094919037223353 := by
  unfold tailWord_2457607
  simp only [CollatzResearch.WordTrace]
  refine ⟨89636291207517039704627075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59757527471678026469751383 89636291207517039704627075)
  ·
    refine ⟨134454436811275559556940613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89636291207517039704627075 134454436811275559556940613)
    ·
      refine ⟨25210206902114167416926365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134454436811275559556940613 25210206902114167416926365)
      ·
        refine ⟨9453827588292812781347387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25210206902114167416926365 9453827588292812781347387)
        ·
          refine ⟨14180741382439219172021081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9453827588292812781347387 14180741382439219172021081)
          ·
            refine ⟨10635556036829414379015811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14180741382439219172021081 10635556036829414379015811)
            ·
              refine ⟨15953334055244121568523717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10635556036829414379015811 15953334055244121568523717)
              ·
                refine ⟨2991250135358272794098197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15953334055244121568523717 2991250135358272794098197)
                ·
                  refine ⟨140214850094919037223353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2991250135358272794098197 140214850094919037223353)
                  ·
                    rfl

theorem cell23_2457607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 6].length) (baseStart_2457607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457607 prefixEnd_2457607 := by exact prefixLift 2457607
  have htrace : WordTrace (prefixWord ++ tailWord_2457607) baseStart_2457607 baseEnd_2457607 := by
    simpa [prefixWord, tailWord_2457607, baseEnd_2457607] using wordTrace_append hprefix tailTrace_2457607
  have hstable : (prefixWord ++ tailWord_2457607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457607).length < 2 ^ (prefixWord ++ tailWord_2457607).sum := by decide
  have hdescent : baseEnd_2457607 < baseStart_2457607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457637 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_2457637 : Nat := 118140960795 + 2457637 * 2 ^ 59
def prefixEnd_2457637 : Nat := 4983230072969 + 3 ^ 40 * 2457637 * 2
def baseEnd_2457637 : Nat := 420649685091302072545013

theorem tailTrace_2457637 : CollatzResearch.WordTrace tailWord_2457637 prefixEnd_2457637 420649685091302072545013 := by
  unfold tailWord_2457637
  simp only [CollatzResearch.WordTrace]
  refine ⟨89637385397408354828219165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59758256931605569885479443 89637385397408354828219165)
  ·
    refine ⟨33614019524028133060582187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89637385397408354828219165 33614019524028133060582187)
    ·
      refine ⟨50421029286042199590873281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33614019524028133060582187 50421029286042199590873281)
      ·
        refine ⟨37815771964531649693154961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50421029286042199590873281 37815771964531649693154961)
        ·
          refine ⟨28361828973398737269866221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37815771964531649693154961 28361828973398737269866221)
          ·
            refine ⟨10635685865024526476199833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28361828973398737269866221 10635685865024526476199833)
            ·
              refine ⟨7976764398768394857149875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10635685865024526476199833 7976764398768394857149875)
              ·
                refine ⟨11965146598152592285724813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7976764398768394857149875 11965146598152592285724813)
                ·
                  refine ⟨4486929974307222107146805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11965146598152592285724813 4486929974307222107146805)
                  ·
                    refine ⟨420649685091302072545013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4486929974307222107146805 420649685091302072545013)
                    ·
                      rfl

theorem cell23_2457637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_2457637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457637 prefixEnd_2457637 := by exact prefixLift 2457637
  have htrace : WordTrace (prefixWord ++ tailWord_2457637) baseStart_2457637 baseEnd_2457637 := by
    simpa [prefixWord, tailWord_2457637, baseEnd_2457637] using wordTrace_append hprefix tailTrace_2457637
  have hstable : (prefixWord ++ tailWord_2457637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457637).length < 2 ^ (prefixWord ++ tailWord_2457637).sum := by decide
  have hdescent : baseEnd_2457637 < baseStart_2457637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457644 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 2, 3, 2]
def baseStart_2457644 : Nat := 118140960795 + 2457644 * 2 ^ 59
def prefixEnd_2457644 : Nat := 4983230072969 + 3 ^ 40 * 2457644 * 2
def baseEnd_2457644 : Nat := 1261952649638487690247507

theorem tailTrace_2457644 : CollatzResearch.WordTrace tailWord_2457644 prefixEnd_2457644 1261952649638487690247507 := by
  unfold tailWord_2457644
  simp only [CollatzResearch.WordTrace]
  refine ⟨44818820354191497511861993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59758427138921996682482657 44818820354191497511861993)
  ·
    refine ⟨33614115265643623133896495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44818820354191497511861993 33614115265643623133896495)
    ·
      refine ⟨50421172898465434700844743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33614115265643623133896495 50421172898465434700844743)
      ·
        refine ⟨75631759347698152051267115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50421172898465434700844743 75631759347698152051267115)
        ·
          refine ⟨113447639021547228076900673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75631759347698152051267115 113447639021547228076900673)
          ·
            refine ⟨85085729266160421057675505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113447639021547228076900673 85085729266160421057675505)
            ·
              refine ⟨63814296949620315793256629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85085729266160421057675505 63814296949620315793256629)
              ·
                refine ⟨5982590339026904605617809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63814296949620315793256629 5982590339026904605617809)
                ·
                  refine ⟨4486942754270178454213357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5982590339026904605617809 4486942754270178454213357)
                  ·
                    refine ⟨1682603532851316920330009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4486942754270178454213357 1682603532851316920330009)
                    ·
                      refine ⟨1261952649638487690247507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682603532851316920330009 1261952649638487690247507)
                      ·
                        rfl

theorem cell23_2457644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 3, 2].length) (baseStart_2457644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457644 prefixEnd_2457644 := by exact prefixLift 2457644
  have htrace : WordTrace (prefixWord ++ tailWord_2457644) baseStart_2457644 baseEnd_2457644 := by
    simpa [prefixWord, tailWord_2457644, baseEnd_2457644] using wordTrace_append hprefix tailTrace_2457644
  have hstable : (prefixWord ++ tailWord_2457644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457644).length < 2 ^ (prefixWord ++ tailWord_2457644).sum := by decide
  have hdescent : baseEnd_2457644 < baseStart_2457644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457651 : List Nat := [1, 1, 1, 2, 4, 1, 3, 5, 1, 1, 3]
def baseStart_2457651 : Nat := 118140960795 + 2457651 * 2 ^ 59
def prefixEnd_2457651 : Nat := 4983230072969 + 3 ^ 40 * 2457651 * 2
def baseEnd_2457651 : Nat := 1261956244003069162859975

theorem tailTrace_2457651 : CollatzResearch.WordTrace tailWord_2457651 prefixEnd_2457651 1261956244003069162859975 := by
  unfold tailWord_2457651
  simp only [CollatzResearch.WordTrace]
  refine ⟨89637896019357635219228807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59758597346238423479485871 89637896019357635219228807)
  ·
    refine ⟨134456844029036452828843211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89637896019357635219228807 134456844029036452828843211)
    ·
      refine ⟨201685266043554679243264817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134456844029036452828843211 201685266043554679243264817)
      ·
        refine ⟨151263949532666009432448613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201685266043554679243264817 151263949532666009432448613)
        ·
          refine ⟨28361990537374876768584115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151263949532666009432448613 28361990537374876768584115)
          ·
            refine ⟨42542985806062315152876173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28361990537374876768584115 42542985806062315152876173)
            ·
              refine ⟨15953619677273368182328565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42542985806062315152876173 15953619677273368182328565)
              ·
                refine ⟨1495651844744378267093303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15953619677273368182328565 1495651844744378267093303)
                ·
                  refine ⟨2243477767116567400639955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495651844744378267093303 2243477767116567400639955)
                  ·
                    refine ⟨3365216650674851100959933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2243477767116567400639955 3365216650674851100959933)
                    ·
                      refine ⟨1261956244003069162859975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3365216650674851100959933 1261956244003069162859975)
                      ·
                        rfl

theorem cell23_2457651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 1, 1, 3].length) (baseStart_2457651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457651 prefixEnd_2457651 := by exact prefixLift 2457651
  have htrace : WordTrace (prefixWord ++ tailWord_2457651) baseStart_2457651 baseEnd_2457651 := by
    simpa [prefixWord, tailWord_2457651, baseEnd_2457651] using wordTrace_append hprefix tailTrace_2457651
  have hstable : (prefixWord ++ tailWord_2457651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457651).length < 2 ^ (prefixWord ++ tailWord_2457651).sum := by decide
  have hdescent : baseEnd_2457651 < baseStart_2457651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457758 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_2457758 : Nat := 118140960795 + 2457758 * 2 ^ 59
def prefixEnd_2457758 : Nat := 4983230072969 + 3 ^ 40 * 2457758 * 2
def baseEnd_2457758 : Nat := 1262011186433100244221983

theorem tailTrace_2457758 : CollatzResearch.WordTrace tailWord_2457758 prefixEnd_2457758 1262011186433100244221983 := by
  unfold tailWord_2457758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11205224828746249061671741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59761199086646661662249285 11205224828746249061671741)
  ·
    refine ⟨4201959310779843398126903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11205224828746249061671741 4201959310779843398126903)
    ·
      refine ⟨6302938966169765097190355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4201959310779843398126903 6302938966169765097190355)
      ·
        refine ⟨9454408449254647645785533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6302938966169765097190355 9454408449254647645785533)
        ·
          refine ⟨3545403168470492867169575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9454408449254647645785533 3545403168470492867169575)
          ·
            refine ⟨5318104752705739300754363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545403168470492867169575 5318104752705739300754363)
            ·
              refine ⟨7977157129058608951131545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5318104752705739300754363 7977157129058608951131545)
              ·
                refine ⟨5982867846793956713348659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7977157129058608951131545 5982867846793956713348659)
                ·
                  refine ⟨8974301770190935070022989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5982867846793956713348659 8974301770190935070022989)
                  ·
                    refine ⟨3365363163821600651258621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8974301770190935070022989 3365363163821600651258621)
                    ·
                      refine ⟨1262011186433100244221983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3365363163821600651258621 1262011186433100244221983)
                      ·
                        rfl

theorem cell23_2457758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_2457758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457758 prefixEnd_2457758 := by exact prefixLift 2457758
  have htrace : WordTrace (prefixWord ++ tailWord_2457758) baseStart_2457758 baseEnd_2457758 := by
    simpa [prefixWord, tailWord_2457758, baseEnd_2457758] using wordTrace_append hprefix tailTrace_2457758
  have hstable : (prefixWord ++ tailWord_2457758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457758).length < 2 ^ (prefixWord ++ tailWord_2457758).sum := by decide
  have hdescent : baseEnd_2457758 < baseStart_2457758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457787 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 7]
def baseStart_2457787 : Nat := 118140960795 + 2457787 * 2 ^ 59
def prefixEnd_2457787 : Nat := 4983230072969 + 3 ^ 40 * 2457787 * 2
def baseEnd_2457787 : Nat := 140225119708008958973261

theorem tailTrace_2457787 : CollatzResearch.WordTrace tailWord_2457787 prefixEnd_2457787 140225119708008958973261 := by
  unfold tailWord_2457787
  simp only [CollatzResearch.WordTrace]
  refine ⟨89642856346864930446179615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59761904231243286964119743 89642856346864930446179615)
  ·
    refine ⟨134464284520297395669269423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89642856346864930446179615 134464284520297395669269423)
    ·
      refine ⟨201696426780446093503904135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134464284520297395669269423 201696426780446093503904135)
      ·
        refine ⟨302544640170669140255856203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201696426780446093503904135 302544640170669140255856203)
        ·
          refine ⟨453816960256003710383784305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302544640170669140255856203 453816960256003710383784305)
          ·
            refine ⟨340362720192002782787838229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453816960256003710383784305 340362720192002782787838229)
            ·
              refine ⟨15954502509000130443179917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 340362720192002782787838229 15954502509000130443179917)
              ·
                refine ⟨5982938440875048916192469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15954502509000130443179917 5982938440875048916192469)
                ·
                  refine ⟨140225119708008958973261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5982938440875048916192469 140225119708008958973261)
                  ·
                    rfl

theorem cell23_2457787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 7].length) (baseStart_2457787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457787 prefixEnd_2457787 := by exact prefixLift 2457787
  have htrace : WordTrace (prefixWord ++ tailWord_2457787) baseStart_2457787 baseEnd_2457787 := by
    simpa [prefixWord, tailWord_2457787, baseEnd_2457787] using wordTrace_append hprefix tailTrace_2457787
  have hstable : (prefixWord ++ tailWord_2457787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457787).length < 2 ^ (prefixWord ++ tailWord_2457787).sum := by decide
  have hdescent : baseEnd_2457787 < baseStart_2457787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457826 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2457826 : Nat := 118140960795 + 2457826 * 2 ^ 59
def prefixEnd_2457826 : Nat := 4983230072969 + 3 ^ 40 * 2457826 * 2
def baseEnd_2457826 : Nat := 1262046103117605978171671

theorem tailTrace_2457826 : CollatzResearch.WordTrace tailWord_2457826 prefixEnd_2457826 1262046103117605978171671 := by
  unfold tailWord_2457826
  simp only [CollatzResearch.WordTrace]
  refine ⟨22411069698430910026712333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59762852529149093404566221 22411069698430910026712333)
  ·
    refine ⟨8404151136911591260017125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22411069698430910026712333 8404151136911591260017125)
    ·
      refine ⟨1575778338170923361253211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8404151136911591260017125 1575778338170923361253211)
      ·
        refine ⟨2363667507256385041879817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1575778338170923361253211 2363667507256385041879817)
        ·
          refine ⟨1772750630442288781409863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2363667507256385041879817 1772750630442288781409863)
          ·
            refine ⟨2659125945663433172114795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772750630442288781409863 2659125945663433172114795)
            ·
              refine ⟨3988688918495149758172193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2659125945663433172114795 3988688918495149758172193)
              ·
                refine ⟨2991516688871362318629145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3988688918495149758172193 2991516688871362318629145)
                ·
                  refine ⟨2243637516653521738971859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2991516688871362318629145 2243637516653521738971859)
                  ·
                    refine ⟨3365456274980282608457789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2243637516653521738971859 3365456274980282608457789)
                    ·
                      refine ⟨1262046103117605978171671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3365456274980282608457789 1262046103117605978171671)
                      ·
                        rfl

theorem cell23_2457826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2457826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457826 prefixEnd_2457826 := by exact prefixLift 2457826
  have htrace : WordTrace (prefixWord ++ tailWord_2457826) baseStart_2457826 baseEnd_2457826 := by
    simpa [prefixWord, tailWord_2457826, baseEnd_2457826] using wordTrace_append hprefix tailTrace_2457826
  have hstable : (prefixWord ++ tailWord_2457826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457826).length < 2 ^ (prefixWord ++ tailWord_2457826).sum := by decide
  have hdescent : baseEnd_2457826 < baseStart_2457826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457831 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2457831 : Nat := 118140960795 + 2457831 * 2 ^ 59
def prefixEnd_2457831 : Nat := 4983230072969 + 3 ^ 40 * 2457831 * 2
def baseEnd_2457831 : Nat := 1262048670520878458609147

theorem tailTrace_2457831 : CollatzResearch.WordTrace tailWord_2457831 prefixEnd_2457831 1262048670520878458609147 := by
  unfold tailWord_2457831
  simp only [CollatzResearch.WordTrace]
  refine ⟨89644461158705525960781347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59762974105803683973854231 89644461158705525960781347)
  ·
    refine ⟨134466691738058288941172021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89644461158705525960781347 134466691738058288941172021)
    ·
      refine ⟨12606252350442964588234877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134466691738058288941172021 12606252350442964588234877)
      ·
        refine ⟨4727344631416111720588079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12606252350442964588234877 4727344631416111720588079)
        ·
          refine ⟨7091016947124167580882119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4727344631416111720588079 7091016947124167580882119)
          ·
            refine ⟨10636525420686251371323179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7091016947124167580882119 10636525420686251371323179)
            ·
              refine ⟨15954788131029377056984769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10636525420686251371323179 15954788131029377056984769)
              ·
                refine ⟨11966091098272032792738577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15954788131029377056984769 11966091098272032792738577)
                ·
                  refine ⟨8974568323704024594553933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11966091098272032792738577 8974568323704024594553933)
                  ·
                    refine ⟨3365463121389009222957725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8974568323704024594553933 3365463121389009222957725)
                    ·
                      refine ⟨1262048670520878458609147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3365463121389009222957725 1262048670520878458609147)
                      ·
                        rfl

theorem cell23_2457831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2457831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457831 prefixEnd_2457831 := by exact prefixLift 2457831
  have htrace : WordTrace (prefixWord ++ tailWord_2457831) baseStart_2457831 baseEnd_2457831 := by
    simpa [prefixWord, tailWord_2457831, baseEnd_2457831] using wordTrace_append hprefix tailTrace_2457831
  have hstable : (prefixWord ++ tailWord_2457831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457831).length < 2 ^ (prefixWord ++ tailWord_2457831).sum := by decide
  have hdescent : baseEnd_2457831 < baseStart_2457831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457834 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_2457834 : Nat := 118140960795 + 2457834 * 2 ^ 59
def prefixEnd_2457834 : Nat := 4983230072969 + 3 ^ 40 * 2457834 * 2
def baseEnd_2457834 : Nat := 420683403654280648957211

theorem tailTrace_2457834 : CollatzResearch.WordTrace tailWord_2457834 prefixEnd_2457834 420683403654280648957211 := by
  unfold tailWord_2457834
  simp only [CollatzResearch.WordTrace]
  refine ⟨22411142644423664368285139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59763047051796438315427037 22411142644423664368285139)
  ·
    refine ⟨33616713966635496552427709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22411142644423664368285139 33616713966635496552427709)
    ·
      refine ⟨12606267737488311207160391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33616713966635496552427709 12606267737488311207160391)
      ·
        refine ⟨18909401606232466810740587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12606267737488311207160391 18909401606232466810740587)
        ·
          refine ⟨28364102409348700216110881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18909401606232466810740587 28364102409348700216110881)
          ·
            refine ⟨21273076807011525162083161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28364102409348700216110881 21273076807011525162083161)
            ·
              refine ⟨15954807605258643871562371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21273076807011525162083161 15954807605258643871562371)
              ·
                refine ⟨23932211407887965807343557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15954807605258643871562371 23932211407887965807343557)
                ·
                  refine ⟨4487289638978993588876917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23932211407887965807343557 4487289638978993588876917)
                  ·
                    refine ⟨420683403654280648957211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4487289638978993588876917 420683403654280648957211)
                    ·
                      rfl

theorem cell23_2457834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_2457834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457834 prefixEnd_2457834 := by exact prefixLift 2457834
  have htrace : WordTrace (prefixWord ++ tailWord_2457834) baseStart_2457834 baseEnd_2457834 := by
    simpa [prefixWord, tailWord_2457834, baseEnd_2457834] using wordTrace_append hprefix tailTrace_2457834
  have hstable : (prefixWord ++ tailWord_2457834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457834).length < 2 ^ (prefixWord ++ tailWord_2457834).sum := by decide
  have hdescent : baseEnd_2457834 < baseStart_2457834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457847 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 4, 8]
def baseStart_2457847 : Nat := 118140960795 + 2457847 * 2 ^ 59
def prefixEnd_2457847 : Nat := 4983230072969 + 3 ^ 40 * 2457847 * 2
def baseEnd_2457847 : Nat := 420685628737116798669691

theorem tailTrace_2457847 : CollatzResearch.WordTrace tailWord_2457847 prefixEnd_2457847 420685628737116798669691 := by
  unfold tailWord_2457847
  simp only [CollatzResearch.WordTrace]
  refine ⟨89645044726647560693363795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59763363151098373795575863 89645044726647560693363795)
  ·
    refine ⟨134467567089971341040045693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89645044726647560693363795 134467567089971341040045693)
    ·
      refine ⟨50425337658739252890017135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134467567089971341040045693 50425337658739252890017135)
      ·
        refine ⟨75638006488108879335025703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50425337658739252890017135 75638006488108879335025703)
        ·
          refine ⟨113457009732163319002538555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75638006488108879335025703 113457009732163319002538555)
          ·
            refine ⟨170185514598244978503807833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113457009732163319002538555 170185514598244978503807833)
            ·
              refine ⟨127639135948683733877855875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170185514598244978503807833 127639135948683733877855875)
              ·
                refine ⟨191458703923025600816783813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127639135948683733877855875 191458703923025600816783813)
                ·
                  refine ⟨35898506985567300153146965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191458703923025600816783813 35898506985567300153146965)
                  ·
                    refine ⟨420685628737116798669691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35898506985567300153146965 420685628737116798669691)
                    ·
                      rfl

theorem cell23_2457847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_2457847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457847 prefixEnd_2457847 := by exact prefixLift 2457847
  have htrace : WordTrace (prefixWord ++ tailWord_2457847) baseStart_2457847 baseEnd_2457847 := by
    simpa [prefixWord, tailWord_2457847, baseEnd_2457847] using wordTrace_append hprefix tailTrace_2457847
  have hstable : (prefixWord ++ tailWord_2457847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457847).length < 2 ^ (prefixWord ++ tailWord_2457847).sum := by decide
  have hdescent : baseEnd_2457847 < baseStart_2457847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457891 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 3]
def baseStart_2457891 : Nat := 118140960795 + 2457891 * 2 ^ 59
def prefixEnd_2457891 : Nat := 4983230072969 + 3 ^ 40 * 2457891 * 2
def baseEnd_2457891 : Nat := 1262079479360148223858871

theorem tailTrace_2457891 : CollatzResearch.WordTrace tailWord_2457891 prefixEnd_2457891 1262079479360148223858871 := by
  unfold tailWord_2457891
  simp only [CollatzResearch.WordTrace]
  refine ⟨89646649538488156207965527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59764433025658770805310351 89646649538488156207965527)
  ·
    refine ⟨134469974307732234311948291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89646649538488156207965527 134469974307732234311948291)
    ·
      refine ⟨201704961461598351467922437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134469974307732234311948291 201704961461598351467922437)
      ·
        refine ⟨37819680274049690900235457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201704961461598351467922437 37819680274049690900235457)
        ·
          refine ⟨28364760205537268175176593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37819680274049690900235457 28364760205537268175176593)
          ·
            refine ⟨21273570154152951131382445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28364760205537268175176593 21273570154152951131382445)
            ·
              refine ⟨7977588807807356674268417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21273570154152951131382445 7977588807807356674268417)
              ·
                refine ⟨5983191605855517505701313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7977588807807356674268417 5983191605855517505701313)
                ·
                  refine ⟨4487393704391638129275985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5983191605855517505701313 4487393704391638129275985)
                  ·
                    refine ⟨3365545278293728596956989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4487393704391638129275985 3365545278293728596956989)
                    ·
                      refine ⟨1262079479360148223858871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3365545278293728596956989 1262079479360148223858871)
                      ·
                        rfl

theorem cell23_2457891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_2457891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457891 prefixEnd_2457891 := by exact prefixLift 2457891
  have htrace : WordTrace (prefixWord ++ tailWord_2457891) baseStart_2457891 baseEnd_2457891 := by
    simpa [prefixWord, tailWord_2457891, baseEnd_2457891] using wordTrace_append hprefix tailTrace_2457891
  have hstable : (prefixWord ++ tailWord_2457891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457891).length < 2 ^ (prefixWord ++ tailWord_2457891).sum := by decide
  have hdescent : baseEnd_2457891 < baseStart_2457891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457895 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2457895 : Nat := 118140960795 + 2457895 * 2 ^ 59
def prefixEnd_2457895 : Nat := 4983230072969 + 3 ^ 40 * 2457895 * 2
def baseEnd_2457895 : Nat := 1262081533282766208208853

theorem tailTrace_2457895 : CollatzResearch.WordTrace tailWord_2457895 prefixEnd_2457895 1262081533282766208208853 := by
  unfold tailWord_2457895
  simp only [CollatzResearch.WordTrace]
  refine ⟨89646795430473664891111139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59764530286982443260740759 89646795430473664891111139)
  ·
    refine ⟨134470193145710497336666709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89646795430473664891111139 134470193145710497336666709)
    ·
      refine ⟨1575822575926294890664063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 134470193145710497336666709 1575822575926294890664063)
      ·
        refine ⟨2363733863889442335996095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1575822575926294890664063 2363733863889442335996095)
        ·
          refine ⟨3545600795834163503994143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363733863889442335996095 3545600795834163503994143)
          ·
            refine ⟨5318401193751245255991215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545600795834163503994143 5318401193751245255991215)
            ·
              refine ⟨7977601790626867883986823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5318401193751245255991215 7977601790626867883986823)
              ·
                refine ⟨11966402685940301825980235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7977601790626867883986823 11966402685940301825980235)
                ·
                  refine ⟨17949604028910452738970353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11966402685940301825980235 17949604028910452738970353)
                  ·
                    refine ⟨13462203021682839554227765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17949604028910452738970353 13462203021682839554227765)
                    ·
                      refine ⟨1262081533282766208208853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13462203021682839554227765 1262081533282766208208853)
                      ·
                        rfl

theorem cell23_2457895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2457895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457895 prefixEnd_2457895 := by exact prefixLift 2457895
  have htrace : WordTrace (prefixWord ++ tailWord_2457895) baseStart_2457895 baseEnd_2457895 := by
    simpa [prefixWord, tailWord_2457895, baseEnd_2457895] using wordTrace_append hprefix tailTrace_2457895
  have hstable : (prefixWord ++ tailWord_2457895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457895).length < 2 ^ (prefixWord ++ tailWord_2457895).sum := by decide
  have hdescent : baseEnd_2457895 < baseStart_2457895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457904 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 3]
def baseStart_2457904 : Nat := 118140960795 + 2457904 * 2 ^ 59
def prefixEnd_2457904 : Nat := 4983230072969 + 3 ^ 40 * 2457904 * 2
def baseEnd_2457904 : Nat := 1262086154608656672996311

theorem tailTrace_2457904 : CollatzResearch.WordTrace tailWord_2457904 prefixEnd_2457904 1262086154608656672996311 := by
  unfold tailWord_2457904
  simp only [CollatzResearch.WordTrace]
  refine ⟨44823561843720529714094383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59764749124960706285459177 44823561843720529714094383)
  ·
    refine ⟨67235342765580794571141575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44823561843720529714094383 67235342765580794571141575)
    ·
      refine ⟨100853014148371191856712363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67235342765580794571141575 100853014148371191856712363)
      ·
        refine ⟨151279521222556787785068545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100853014148371191856712363 151279521222556787785068545)
        ·
          refine ⟨113459640916917590838801409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151279521222556787785068545 113459640916917590838801409)
          ·
            refine ⟨85094730687688193129101057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113459640916917590838801409 85094730687688193129101057)
            ·
              refine ⟨63821048015766144846825793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85094730687688193129101057 63821048015766144846825793)
              ·
                refine ⟨47865786011824608635119345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63821048015766144846825793 47865786011824608635119345)
                ·
                  refine ⟨35899339508868456476339509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47865786011824608635119345 35899339508868456476339509)
                  ·
                    refine ⟨3365563078956417794656829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35899339508868456476339509 3365563078956417794656829)
                    ·
                      refine ⟨1262086154608656672996311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3365563078956417794656829 1262086154608656672996311)
                      ·
                        rfl

theorem cell23_2457904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 3].length) (baseStart_2457904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457904 prefixEnd_2457904 := by exact prefixLift 2457904
  have htrace : WordTrace (prefixWord ++ tailWord_2457904) baseStart_2457904 baseEnd_2457904 := by
    simpa [prefixWord, tailWord_2457904, baseEnd_2457904] using wordTrace_append hprefix tailTrace_2457904
  have hstable : (prefixWord ++ tailWord_2457904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457904).length < 2 ^ (prefixWord ++ tailWord_2457904).sum := by decide
  have hdescent : baseEnd_2457904 < baseStart_2457904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457934 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_2457934 : Nat := 118140960795 + 2457934 * 2 ^ 59
def prefixEnd_2457934 : Nat := 4983230072969 + 3 ^ 40 * 2457934 * 2
def baseEnd_2457934 : Nat := 1262101559028291555621173

theorem tailTrace_2457934 : CollatzResearch.WordTrace tailWord_2457934 prefixEnd_2457934 1262101559028291555621173 := by
  unfold tailWord_2457934
  simp only [CollatzResearch.WordTrace]
  refine ⟨11206027234666546818972607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59765478584888249701187237 11206027234666546818972607)
  ·
    refine ⟨16809040851999820228458911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11206027234666546818972607 16809040851999820228458911)
    ·
      refine ⟨25213561277999730342688367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16809040851999820228458911 25213561277999730342688367)
      ·
        refine ⟨37820341916999595514032551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25213561277999730342688367 37820341916999595514032551)
        ·
          refine ⟨56730512875499393271048827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37820341916999595514032551 56730512875499393271048827)
          ·
            refine ⟨85095769313249089906573241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56730512875499393271048827 85095769313249089906573241)
            ·
              refine ⟨63821826984936817429929931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85095769313249089906573241 63821826984936817429929931)
              ·
                refine ⟨95732740477405226144894897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63821826984936817429929931 95732740477405226144894897)
                ·
                  refine ⟨71799555358053919608671173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95732740477405226144894897 71799555358053919608671173)
                  ·
                    refine ⟨13462416629635109926625845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71799555358053919608671173 13462416629635109926625845)
                    ·
                      refine ⟨1262101559028291555621173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13462416629635109926625845 1262101559028291555621173)
                      ·
                        rfl

theorem cell23_2457934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_2457934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457934 prefixEnd_2457934 := by exact prefixLift 2457934
  have htrace : WordTrace (prefixWord ++ tailWord_2457934) baseStart_2457934 baseEnd_2457934 := by
    simpa [prefixWord, tailWord_2457934, baseEnd_2457934] using wordTrace_append hprefix tailTrace_2457934
  have hstable : (prefixWord ++ tailWord_2457934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457934).length < 2 ^ (prefixWord ++ tailWord_2457934).sum := by decide
  have hdescent : baseEnd_2457934 < baseStart_2457934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457955 : List Nat := [1, 1, 1, 5, 2, 1, 3, 4, 1, 1, 3]
def baseStart_2457955 : Nat := 118140960795 + 2457955 * 2 ^ 59
def prefixEnd_2457955 : Nat := 4983230072969 + 3 ^ 40 * 2457955 * 2
def baseEnd_2457955 : Nat := 1262112342122035973458577

theorem tailTrace_2457955 : CollatzResearch.WordTrace tailWord_2457955 prefixEnd_2457955 1262112342122035973458577 := by
  unfold tailWord_2457955
  simp only [CollatzResearch.WordTrace]
  refine ⟨89648983810256295138295319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59765989206837530092196879 89648983810256295138295319)
  ·
    refine ⟨134473475715384442707442979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89648983810256295138295319 134473475715384442707442979)
    ·
      refine ⟨201710213573076664061164469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134473475715384442707442979 201710213573076664061164469)
      ·
        refine ⟨18910332522475937255734169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201710213573076664061164469 18910332522475937255734169)
        ·
          refine ⟨14182749391856952941800627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18910332522475937255734169 14182749391856952941800627)
          ·
            refine ⟨21274124087785429412700941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14182749391856952941800627 21274124087785429412700941)
            ·
              refine ⟨7977796532919536029762853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21274124087785429412700941 7977796532919536029762853)
              ·
                refine ⟨1495836849922413005580535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7977796532919536029762853 1495836849922413005580535)
                ·
                  refine ⟨2243755274883619508370803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495836849922413005580535 2243755274883619508370803)
                  ·
                    refine ⟨3365632912325429262556205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2243755274883619508370803 3365632912325429262556205)
                    ·
                      refine ⟨1262112342122035973458577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3365632912325429262556205 1262112342122035973458577)
                      ·
                        rfl

theorem cell23_2457955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_2457955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457955 prefixEnd_2457955 := by exact prefixLift 2457955
  have htrace : WordTrace (prefixWord ++ tailWord_2457955) baseStart_2457955 baseEnd_2457955 := by
    simpa [prefixWord, tailWord_2457955, baseEnd_2457955] using wordTrace_append hprefix tailTrace_2457955
  have hstable : (prefixWord ++ tailWord_2457955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457955).length < 2 ^ (prefixWord ++ tailWord_2457955).sum := by decide
  have hdescent : baseEnd_2457955 < baseStart_2457955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457991 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_2457991 : Nat := 118140960795 + 2457991 * 2 ^ 59
def prefixEnd_2457991 : Nat := 4983230072969 + 3 ^ 40 * 2457991 * 2
def baseEnd_2457991 : Nat := 1262130827425597832608411

theorem tailTrace_2457991 : CollatzResearch.WordTrace tailWord_2457991 prefixEnd_2457991 1262130827425597832608411 := by
  unfold tailWord_2457991
  simp only [CollatzResearch.WordTrace]
  refine ⟨89650296838125873286605827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59766864558750582191070551 89650296838125873286605827)
  ·
    refine ⟨134475445257188809929908741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89650296838125873286605827 134475445257188809929908741)
    ·
      refine ⟨25214145985722901861857889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134475445257188809929908741 25214145985722901861857889)
      ·
        refine ⟨18910609489292176396393417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25214145985722901861857889 18910609489292176396393417)
        ·
          refine ⟨14182957116969132297295063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18910609489292176396393417 14182957116969132297295063)
          ·
            refine ⟨21274435675453698445942595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14182957116969132297295063 21274435675453698445942595)
            ·
              refine ⟨31911653513180547668913893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21274435675453698445942595 31911653513180547668913893)
              ·
                refine ⟨5983435033721352687921355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31911653513180547668913893 5983435033721352687921355)
                ·
                  refine ⟨8975152550582029031882033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5983435033721352687921355 8975152550582029031882033)
                  ·
                    refine ⟨6731364412936521773911525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8975152550582029031882033 6731364412936521773911525)
                    ·
                      refine ⟨1262130827425597832608411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6731364412936521773911525 1262130827425597832608411)
                      ·
                        rfl

theorem cell23_2457991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_2457991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457991 prefixEnd_2457991 := by exact prefixLift 2457991
  have htrace : WordTrace (prefixWord ++ tailWord_2457991) baseStart_2457991 baseEnd_2457991 := by
    simpa [prefixWord, tailWord_2457991, baseEnd_2457991] using wordTrace_append hprefix tailTrace_2457991
  have hstable : (prefixWord ++ tailWord_2457991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457991).length < 2 ^ (prefixWord ++ tailWord_2457991).sum := by decide
  have hdescent : baseEnd_2457991 < baseStart_2457991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457995 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 1, 1, 4]
def baseStart_2457995 : Nat := 118140960795 + 2457995 * 2 ^ 59
def prefixEnd_2457995 : Nat := 4983230072969 + 3 ^ 40 * 2457995 * 2
def baseEnd_2457995 : Nat := 1262132881348215816958393

theorem tailTrace_2457995 : CollatzResearch.WordTrace tailWord_2457995 prefixEnd_2457995 1262132881348215816958393 := by
  unfold tailWord_2457995
  simp only [CollatzResearch.WordTrace]
  refine ⟨89650442730111381969751439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59766961820074254646500959 89650442730111381969751439)
  ·
    refine ⟨134475664095167072954627159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89650442730111381969751439 134475664095167072954627159)
    ·
      refine ⟨201713496142750609431940739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134475664095167072954627159 201713496142750609431940739)
      ·
        refine ⟨302570244214125914147911109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201713496142750609431940739 302570244214125914147911109)
        ·
          refine ⟨56731920790148608902733333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302570244214125914147911109 56731920790148608902733333)
          ·
            refine ⟨2659308787038216042315625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56731920790148608902733333 2659308787038216042315625)
            ·
              refine ⟨1994481590278662031736719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2659308787038216042315625 1994481590278662031736719)
              ·
                refine ⟨2991722385417993047605079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1994481590278662031736719 2991722385417993047605079)
                ·
                  refine ⟨4487583578126989571407619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991722385417993047605079 4487583578126989571407619)
                  ·
                    refine ⟨6731375367190484357111429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4487583578126989571407619 6731375367190484357111429)
                    ·
                      refine ⟨1262132881348215816958393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6731375367190484357111429 1262132881348215816958393)
                      ·
                        rfl

theorem cell23_2457995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 1, 4].length) (baseStart_2457995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2457995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2457995 prefixEnd_2457995 := by exact prefixLift 2457995
  have htrace : WordTrace (prefixWord ++ tailWord_2457995) baseStart_2457995 baseEnd_2457995 := by
    simpa [prefixWord, tailWord_2457995, baseEnd_2457995] using wordTrace_append hprefix tailTrace_2457995
  have hstable : (prefixWord ++ tailWord_2457995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457995).length < 2 ^ (prefixWord ++ tailWord_2457995).sum := by decide
  have hdescent : baseEnd_2457995 < baseStart_2457995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458006 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2458006 : Nat := 118140960795 + 2458006 * 2 ^ 59
def prefixEnd_2458006 : Nat := 4983230072969 + 3 ^ 40 * 2458006 * 2
def baseEnd_2458006 : Nat := 1262138529635415273920843

theorem tailTrace_2458006 : CollatzResearch.WordTrace tailWord_2458006 prefixEnd_2458006 1262138529635415273920843 := by
  unfold tailWord_2458006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5603177745816970678025117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59767229288714353898934581 5603177745816970678025117)
  ·
    refine ⟨2101191654681364004259419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5603177745816970678025117 2101191654681364004259419)
    ·
      refine ⟨3151787482022046006389129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2101191654681364004259419 3151787482022046006389129)
      ·
        refine ⟨2363840611516534504791847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3151787482022046006389129 2363840611516534504791847)
        ·
          refine ⟨3545760917274801757187771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363840611516534504791847 3545760917274801757187771)
          ·
            refine ⟨5318641375912202635781657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545760917274801757187771 5318641375912202635781657)
            ·
              refine ⟨3988981031934151976836243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5318641375912202635781657 3988981031934151976836243)
              ·
                refine ⟨5983471547901227965254365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988981031934151976836243 5983471547901227965254365)
                ·
                  refine ⟨2243801830462960486970387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5983471547901227965254365 2243801830462960486970387)
                  ·
                    refine ⟨3365702745694440730455581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2243801830462960486970387 3365702745694440730455581)
                    ·
                      refine ⟨1262138529635415273920843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3365702745694440730455581 1262138529635415273920843)
                      ·
                        rfl

theorem cell23_2458006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2458006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458006 prefixEnd_2458006 := by exact prefixLift 2458006
  have htrace : WordTrace (prefixWord ++ tailWord_2458006) baseStart_2458006 baseEnd_2458006 := by
    simpa [prefixWord, tailWord_2458006, baseEnd_2458006] using wordTrace_append hprefix tailTrace_2458006
  have hstable : (prefixWord ++ tailWord_2458006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458006).length < 2 ^ (prefixWord ++ tailWord_2458006).sum := by decide
  have hdescent : baseEnd_2458006 < baseStart_2458006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458041 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2458041 : Nat := 118140960795 + 2458041 * 2 ^ 59
def prefixEnd_2458041 : Nat := 4983230072969 + 3 ^ 40 * 2458041 * 2
def baseEnd_2458041 : Nat := 1262156501458322636983181

theorem tailTrace_2458041 : CollatzResearch.WordTrace tailWord_2458041 prefixEnd_2458041 1262156501458322636983181 := by
  unfold tailWord_2458041
  simp only [CollatzResearch.WordTrace]
  refine ⟨89652120487944731825925977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59768080325296487883950651 89652120487944731825925977)
  ·
    refine ⟨67239090365958548869444483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89652120487944731825925977 67239090365958548869444483)
    ·
      refine ⟨100858635548937823304166725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67239090365958548869444483 100858635548937823304166725)
      ·
        refine ⟨18910994165425841869531261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100858635548937823304166725 18910994165425841869531261)
        ·
          refine ⟨7091622812034690701074223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18910994165425841869531261 7091622812034690701074223)
          ·
            refine ⟨10637434218052036051611335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7091622812034690701074223 10637434218052036051611335)
            ·
              refine ⟨15956151327078054077417003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10637434218052036051611335 15956151327078054077417003)
              ·
                refine ⟨23934226990617081116125505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15956151327078054077417003 23934226990617081116125505)
                ·
                  refine ⟨17950670242962810837094129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23934226990617081116125505 17950670242962810837094129)
                  ·
                    refine ⟨13463002682222108127820597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17950670242962810837094129 13463002682222108127820597)
                    ·
                      refine ⟨1262156501458322636983181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13463002682222108127820597 1262156501458322636983181)
                      ·
                        rfl

theorem cell23_2458041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2458041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458041 prefixEnd_2458041 := by exact prefixLift 2458041
  have htrace : WordTrace (prefixWord ++ tailWord_2458041) baseStart_2458041 baseEnd_2458041 := by
    simpa [prefixWord, tailWord_2458041, baseEnd_2458041] using wordTrace_append hprefix tailTrace_2458041
  have hstable : (prefixWord ++ tailWord_2458041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458041).length < 2 ^ (prefixWord ++ tailWord_2458041).sum := by decide
  have hdescent : baseEnd_2458041 < baseStart_2458041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458055 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 1, 3, 2]
def baseStart_2458055 : Nat := 118140960795 + 2458055 * 2 ^ 59
def prefixEnd_2458055 : Nat := 4983230072969 + 3 ^ 40 * 2458055 * 2
def baseEnd_2458055 : Nat := 1262163690187485582208117

theorem tailTrace_2458055 : CollatzResearch.WordTrace tailWord_2458055 prefixEnd_2458055 1262163690187485582208117 := by
  unfold tailWord_2458055
  simp only [CollatzResearch.WordTrace]
  refine ⟨89652631109894012216935619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59768420739929341477957079 89652631109894012216935619)
  ·
    refine ⟨134478946664841018325403429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89652631109894012216935619 134478946664841018325403429)
    ·
      refine ⟨25214802499657690936013143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134478946664841018325403429 25214802499657690936013143)
      ·
        refine ⟨37822203749486536404019715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25214802499657690936013143 37822203749486536404019715)
        ·
          refine ⟨56733305624229804606029573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37822203749486536404019715 56733305624229804606029573)
          ·
            refine ⟨10637494804543088363630545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56733305624229804606029573 10637494804543088363630545)
            ·
              refine ⟨7978121103407316272722909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10637494804543088363630545 7978121103407316272722909)
              ·
                refine ⟨2991795413777743602271091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7978121103407316272722909 2991795413777743602271091)
                ·
                  refine ⟨4487693120666615403406637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991795413777743602271091 4487693120666615403406637)
                  ·
                    refine ⟨1682884920249980776277489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4487693120666615403406637 1682884920249980776277489)
                    ·
                      refine ⟨1262163690187485582208117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682884920249980776277489 1262163690187485582208117)
                      ·
                        rfl

theorem cell23_2458055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_2458055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458055 prefixEnd_2458055 := by exact prefixLift 2458055
  have htrace : WordTrace (prefixWord ++ tailWord_2458055) baseStart_2458055 baseEnd_2458055 := by
    simpa [prefixWord, tailWord_2458055, baseEnd_2458055] using wordTrace_append hprefix tailTrace_2458055
  have hstable : (prefixWord ++ tailWord_2458055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458055).length < 2 ^ (prefixWord ++ tailWord_2458055).sum := by decide
  have hdescent : baseEnd_2458055 < baseStart_2458055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458081 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_2458081 : Nat := 118140960795 + 2458081 * 2 ^ 59
def prefixEnd_2458081 : Nat := 4983230072969 + 3 ^ 40 * 2458081 * 2
def baseEnd_2458081 : Nat := 1262177040684502480482997

theorem tailTrace_2458081 : CollatzResearch.WordTrace tailWord_2458081 prefixEnd_2458081 1262177040684502480482997 := by
  unfold tailWord_2458081
  simp only [CollatzResearch.WordTrace]
  refine ⟨89653579407799818657382097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59769052938533212438254731 89653579407799818657382097)
  ·
    refine ⟨67240184555849863993036573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89653579407799818657382097 67240184555849863993036573)
    ·
      refine ⟨25215069208443698997388715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67240184555849863993036573 25215069208443698997388715)
      ·
        refine ⟨37822603812665548496083073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25215069208443698997388715 37822603812665548496083073)
        ·
          refine ⟨28366952859499161372062305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37822603812665548496083073 28366952859499161372062305)
          ·
            refine ⟨21275214644624371029046729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28366952859499161372062305 21275214644624371029046729)
            ·
              refine ⟨15956410983468278271785047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21275214644624371029046729 15956410983468278271785047)
              ·
                refine ⟨23934616475202417407677571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15956410983468278271785047 23934616475202417407677571)
                ·
                  refine ⟨35901924712803626111516357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23934616475202417407677571 35901924712803626111516357)
                  ·
                    refine ⟨6731610883650679895909317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35901924712803626111516357 6731610883650679895909317)
                    ·
                      refine ⟨1262177040684502480482997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6731610883650679895909317 1262177040684502480482997)
                      ·
                        rfl

theorem cell23_2458081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_2458081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458081 prefixEnd_2458081 := by exact prefixLift 2458081
  have htrace : WordTrace (prefixWord ++ tailWord_2458081) baseStart_2458081 baseEnd_2458081 := by
    simpa [prefixWord, tailWord_2458081, baseEnd_2458081] using wordTrace_append hprefix tailTrace_2458081
  have hstable : (prefixWord ++ tailWord_2458081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458081).length < 2 ^ (prefixWord ++ tailWord_2458081).sum := by decide
  have hdescent : baseEnd_2458081 < baseStart_2458081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458108 : List Nat := [2, 2, 2, 1, 2, 1, 1, 7, 5]
def baseStart_2458108 : Nat := 118140960795 + 2458108 * 2 ^ 59
def prefixEnd_2458108 : Nat := 4983230072969 + 3 ^ 40 * 2458108 * 2
def baseEnd_2458108 : Nat := 140243433851352652760597

theorem tailTrace_2458108 : CollatzResearch.WordTrace tailWord_2458108 prefixEnd_2458108 140243433851352652760597 := by
  unfold tailWord_2458108
  simp only [CollatzResearch.WordTrace]
  refine ⟨44827282089351001134307489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59769709452468001512409985 44827282089351001134307489)
  ·
    refine ⟨33620461567013250850730617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44827282089351001134307489 33620461567013250850730617)
    ·
      refine ⟨25215346175259938138047963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33620461567013250850730617 25215346175259938138047963)
      ·
        refine ⟨37823019262889907207071945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25215346175259938138047963 37823019262889907207071945)
        ·
          refine ⟨28367264447167430405303959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37823019262889907207071945 28367264447167430405303959)
          ·
            refine ⟨42550896670751145607955939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28367264447167430405303959 42550896670751145607955939)
            ·
              refine ⟨63826345006126718411933909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42550896670751145607955939 63826345006126718411933909)
              ·
                refine ⟨1495929961081094962779701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63826345006126718411933909 1495929961081094962779701)
                ·
                  refine ⟨140243433851352652760597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1495929961081094962779701 140243433851352652760597)
                  ·
                    rfl

theorem cell23_2458108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_2458108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458108 prefixEnd_2458108 := by exact prefixLift 2458108
  have htrace : WordTrace (prefixWord ++ tailWord_2458108) baseStart_2458108 baseEnd_2458108 := by
    simpa [prefixWord, tailWord_2458108, baseEnd_2458108] using wordTrace_append hprefix tailTrace_2458108
  have hstable : (prefixWord ++ tailWord_2458108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458108).length < 2 ^ (prefixWord ++ tailWord_2458108).sum := by decide
  have hdescent : baseEnd_2458108 < baseStart_2458108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458119 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 2, 2, 2]
def baseStart_2458119 : Nat := 118140960795 + 2458119 * 2 ^ 59
def prefixEnd_2458119 : Nat := 4983230072969 + 3 ^ 40 * 2458119 * 2
def baseEnd_2458119 : Nat := 1262196552949373331807823

theorem tailTrace_2458119 : CollatzResearch.WordTrace tailWord_2458119 prefixEnd_2458119 1262196552949373331807823 := by
  unfold tailWord_2458119
  simp only [CollatzResearch.WordTrace]
  refine ⟨89654965381662151147265411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59769976921108100764843607 89654965381662151147265411)
  ·
    refine ⟨134482448072493226720898117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89654965381662151147265411 134482448072493226720898117)
    ·
      refine ⟨25215459013592480010168397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134482448072493226720898117 25215459013592480010168397)
      ·
        refine ⟨9455797130097180003813149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25215459013592480010168397 9455797130097180003813149)
        ·
          refine ⟨3545923923786442501429931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9455797130097180003813149 3545923923786442501429931)
          ·
            refine ⟨5318885885679663752144897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545923923786442501429931 5318885885679663752144897)
            ·
              refine ⟨3989164414259747814108673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5318885885679663752144897 3989164414259747814108673)
              ·
                refine ⟨2991873310694810860581505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3989164414259747814108673 2991873310694810860581505)
                ·
                  refine ⟨2243904983021108145436129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2991873310694810860581505 2243904983021108145436129)
                  ·
                    refine ⟨1682928737265831109077097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2243904983021108145436129 1682928737265831109077097)
                    ·
                      refine ⟨1262196552949373331807823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1682928737265831109077097 1262196552949373331807823)
                      ·
                        rfl

theorem cell23_2458119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_2458119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458119 prefixEnd_2458119 := by exact prefixLift 2458119
  have htrace : WordTrace (prefixWord ++ tailWord_2458119) baseStart_2458119 baseEnd_2458119 := by
    simpa [prefixWord, tailWord_2458119, baseEnd_2458119] using wordTrace_append hprefix tailTrace_2458119
  have hstable : (prefixWord ++ tailWord_2458119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458119).length < 2 ^ (prefixWord ++ tailWord_2458119).sum := by decide
  have hdescent : baseEnd_2458119 < baseStart_2458119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458121 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 4, 5]
def baseStart_2458121 : Nat := 118140960795 + 2458121 * 2 ^ 59
def prefixEnd_2458121 : Nat := 4983230072969 + 3 ^ 40 * 2458121 * 2
def baseEnd_2458121 : Nat := 420732526636894107994271

theorem tailTrace_2458121 : CollatzResearch.WordTrace tailWord_2458121 prefixEnd_2458121 420732526636894107994271 := by
  unfold tailWord_2458121
  simp only [CollatzResearch.WordTrace]
  refine ⟨89655038327654905488838217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59770025551769936992558811 89655038327654905488838217)
  ·
    refine ⟨67241278745741179116628663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89655038327654905488838217 67241278745741179116628663)
    ·
      refine ⟨100861918118611768674942995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67241278745741179116628663 100861918118611768674942995)
      ·
        refine ⟨151292877177917653012414493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100861918118611768674942995 151292877177917653012414493)
        ·
          refine ⟨56734828941719119879655435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151292877177917653012414493 56734828941719119879655435)
          ·
            refine ⟨85102243412578679819483153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56734828941719119879655435 85102243412578679819483153)
            ·
              refine ⟨63826682559434009864612365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85102243412578679819483153 63826682559434009864612365)
              ·
                refine ⟨23935005959787753699229637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63826682559434009864612365 23935005959787753699229637)
                ·
                  refine ⟨4487813617460203818605557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23935005959787753699229637 4487813617460203818605557)
                  ·
                    refine ⟨420732526636894107994271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4487813617460203818605557 420732526636894107994271)
                    ·
                      rfl

theorem cell23_2458121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_2458121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458121 prefixEnd_2458121 := by exact prefixLift 2458121
  have htrace : WordTrace (prefixWord ++ tailWord_2458121) baseStart_2458121 baseEnd_2458121 := by
    simpa [prefixWord, tailWord_2458121, baseEnd_2458121] using wordTrace_append hprefix tailTrace_2458121
  have hstable : (prefixWord ++ tailWord_2458121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458121).length < 2 ^ (prefixWord ++ tailWord_2458121).sum := by decide
  have hdescent : baseEnd_2458121 < baseStart_2458121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458131 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 5]
def baseStart_2458131 : Nat := 118140960795 + 2458131 * 2 ^ 59
def prefixEnd_2458131 : Nat := 4983230072969 + 3 ^ 40 * 2458131 * 2
def baseEnd_2458131 : Nat := 1262202714717227284857767

theorem tailTrace_2458131 : CollatzResearch.WordTrace tailWord_2458131 prefixEnd_2458131 1262202714717227284857767 := by
  unfold tailWord_2458131
  simp only [CollatzResearch.WordTrace]
  refine ⟨89655403057618677196702247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59770268705079118131134831 89655403057618677196702247)
  ·
    refine ⟨134483104586428015795053371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89655403057618677196702247 134483104586428015795053371)
    ·
      refine ⟨201724656879642023692580057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134483104586428015795053371 201724656879642023692580057)
      ·
        refine ⟨151293492659731517769435043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201724656879642023692580057 151293492659731517769435043)
        ·
          refine ⟨226940238989597276654152565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151293492659731517769435043 226940238989597276654152565)
          ·
            refine ⟨21275647405274744686326803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 226940238989597276654152565 21275647405274744686326803)
            ·
              refine ⟨31913471107912117029490205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21275647405274744686326803 31913471107912117029490205)
              ·
                refine ⟨11967551665467043886058827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31913471107912117029490205 11967551665467043886058827)
                ·
                  refine ⟨17951327498200565829088241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11967551665467043886058827 17951327498200565829088241)
                  ·
                    refine ⟨13463495623650424371816181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17951327498200565829088241 13463495623650424371816181)
                    ·
                      refine ⟨1262202714717227284857767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13463495623650424371816181 1262202714717227284857767)
                      ·
                        rfl

theorem cell23_2458131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_2458131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458131 prefixEnd_2458131 := by exact prefixLift 2458131
  have htrace : WordTrace (prefixWord ++ tailWord_2458131) baseStart_2458131 baseEnd_2458131 := by
    simpa [prefixWord, tailWord_2458131, baseEnd_2458131] using wordTrace_append hprefix tailTrace_2458131
  have hstable : (prefixWord ++ tailWord_2458131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458131).length < 2 ^ (prefixWord ++ tailWord_2458131).sum := by decide
  have hdescent : baseEnd_2458131 < baseStart_2458131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458168 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 5, 4]
def baseStart_2458168 : Nat := 118140960795 + 2458168 * 2 ^ 59
def prefixEnd_2458168 : Nat := 4983230072969 + 3 ^ 40 * 2458168 * 2
def baseEnd_2458168 : Nat := 420740571167147880031699

theorem tailTrace_2458168 : CollatzResearch.WordTrace tailWord_2458168 prefixEnd_2458168 420740571167147880031699 := by
  unfold tailWord_2458168
  simp only [CollatzResearch.WordTrace]
  refine ⟨44828376279242316257899579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59771168372323088343866105 44828376279242316257899579)
  ·
    refine ⟨67242564418863474386849369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44828376279242316257899579 67242564418863474386849369)
    ·
      refine ⟨50431923314147605790137027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67242564418863474386849369 50431923314147605790137027)
      ·
        refine ⟨75647884971221408685205541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50431923314147605790137027 75647884971221408685205541)
        ·
          refine ⟨14183978432104014128476039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75647884971221408685205541 14183978432104014128476039)
          ·
            refine ⟨21275967648156021192714059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14183978432104014128476039 21275967648156021192714059)
            ·
              refine ⟨31913951472234031789071089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21275967648156021192714059 31913951472234031789071089)
              ·
                refine ⟨23935463604175523841803317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31913951472234031789071089 23935463604175523841803317)
                ·
                  refine ⟨2243949712891455360169061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23935463604175523841803317 2243949712891455360169061)
                  ·
                    refine ⟨420740571167147880031699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2243949712891455360169061 420740571167147880031699)
                    ·
                      rfl

theorem cell23_2458168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_2458168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458168 prefixEnd_2458168 := by exact prefixLift 2458168
  have htrace : WordTrace (prefixWord ++ tailWord_2458168) baseStart_2458168 baseEnd_2458168 := by
    simpa [prefixWord, tailWord_2458168, baseEnd_2458168] using wordTrace_append hprefix tailTrace_2458168
  have hstable : (prefixWord ++ tailWord_2458168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458168).length < 2 ^ (prefixWord ++ tailWord_2458168).sum := by decide
  have hdescent : baseEnd_2458168 < baseStart_2458168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458293 : List Nat := [1, 3, 3, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_2458293 : Nat := 118140960795 + 2458293 * 2 ^ 59
def prefixEnd_2458293 : Nat := 4983230072969 + 3 ^ 40 * 2458293 * 2
def baseEnd_2458293 : Nat := 1262285898583255651032023

theorem tailTrace_2458293 : CollatzResearch.WordTrace tailWord_2458293 prefixEnd_2458293 1262285898583255651032023 := by
  unfold tailWord_2458293
  simp only [CollatzResearch.WordTrace]
  refine ⟨89661311683031778864099533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59774207788687852576066355 89661311683031778864099533)
  ·
    refine ⟨33622991881136917074037325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89661311683031778864099533 33622991881136917074037325)
    ·
      refine ⟨12608621955426343902763997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33622991881136917074037325 12608621955426343902763997)
      ·
        refine ⟨4728233233284878963536499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12608621955426343902763997 4728233233284878963536499)
        ·
          refine ⟨7092349849927318445304749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4728233233284878963536499 7092349849927318445304749)
          ·
            refine ⟨2659631193722744416989281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7092349849927318445304749 2659631193722744416989281)
            ·
              refine ⟨1994723395292058312741961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2659631193722744416989281 1994723395292058312741961)
              ·
                refine ⟨1496042546469043734556471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1994723395292058312741961 1496042546469043734556471)
                ·
                  refine ⟨2244063819703565601834707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496042546469043734556471 2244063819703565601834707)
                  ·
                    refine ⟨3366095729555348402752061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2244063819703565601834707 3366095729555348402752061)
                    ·
                      refine ⟨1262285898583255651032023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3366095729555348402752061 1262285898583255651032023)
                      ·
                        rfl

theorem cell23_2458293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_2458293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458293 prefixEnd_2458293 := by exact prefixLift 2458293
  have htrace : WordTrace (prefixWord ++ tailWord_2458293) baseStart_2458293 baseEnd_2458293 := by
    simpa [prefixWord, tailWord_2458293, baseEnd_2458293] using wordTrace_append hprefix tailTrace_2458293
  have hstable : (prefixWord ++ tailWord_2458293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458293).length < 2 ^ (prefixWord ++ tailWord_2458293).sum := by decide
  have hdescent : baseEnd_2458293 < baseStart_2458293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458315 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 8, 1, 3]
def baseStart_2458315 : Nat := 118140960795 + 2458315 * 2 ^ 59
def prefixEnd_2458315 : Nat := 4983230072969 + 3 ^ 40 * 2458315 * 2
def baseEnd_2458315 : Nat := 1262297195157654564956921

theorem tailTrace_2458315 : CollatzResearch.WordTrace tailWord_2458315 prefixEnd_2458315 1262297195157654564956921 := by
  unfold tailWord_2458315
  simp only [CollatzResearch.WordTrace]
  refine ⟨89662114088952076621400399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59774742725968051080933599 89662114088952076621400399)
  ·
    refine ⟨134493171133428114932100599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89662114088952076621400399 134493171133428114932100599)
    ·
      refine ⟨201739756700142172398150899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134493171133428114932100599 201739756700142172398150899)
      ·
        refine ⟨302609635050213258597226349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201739756700142172398150899 302609635050213258597226349)
        ·
          refine ⟨113478613143829971973959881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302609635050213258597226349 113478613143829971973959881)
          ·
            refine ⟨85108959857872478980469911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113478613143829971973959881 85108959857872478980469911)
            ·
              refine ⟨127663439786808718470704867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85108959857872478980469911 127663439786808718470704867)
              ·
                refine ⟨191495159680213077706057301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127663439786808718470704867 191495159680213077706057301)
                ·
                  refine ⟨2244083902502497004367859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 191495159680213077706057301 2244083902502497004367859)
                  ·
                    refine ⟨3366125853753745506551789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2244083902502497004367859 3366125853753745506551789)
                    ·
                      refine ⟨1262297195157654564956921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3366125853753745506551789 1262297195157654564956921)
                      ·
                        rfl

theorem cell23_2458315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 1, 3].length) (baseStart_2458315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458315 prefixEnd_2458315 := by exact prefixLift 2458315
  have htrace : WordTrace (prefixWord ++ tailWord_2458315) baseStart_2458315 baseEnd_2458315 := by
    simpa [prefixWord, tailWord_2458315, baseEnd_2458315] using wordTrace_append hprefix tailTrace_2458315
  have hstable : (prefixWord ++ tailWord_2458315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458315).length < 2 ^ (prefixWord ++ tailWord_2458315).sum := by decide
  have hdescent : baseEnd_2458315 < baseStart_2458315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458322 : List Nat := [3, 2, 2, 2, 3, 1, 3, 7]
def baseStart_2458322 : Nat := 118140960795 + 2458322 * 2 ^ 59
def prefixEnd_2458322 : Nat := 4983230072969 + 3 ^ 40 * 2458322 * 2
def baseEnd_2458322 : Nat := 46751881093416149539607

theorem tailTrace_2458322 : CollatzResearch.WordTrace tailWord_2458322 prefixEnd_2458322 46751881093416149539607 := by
  unfold tailWord_2458322
  simp only [CollatzResearch.WordTrace]
  refine ⟨22415592349981679204226305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59774912933284477877936813 22415592349981679204226305)
  ·
    refine ⟨16811694262486259403169729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22415592349981679204226305 16811694262486259403169729)
    ·
      refine ⟨12608770696864694552377297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16811694262486259403169729 12608770696864694552377297)
      ·
        refine ⟨9456578022648520914282973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12608770696864694552377297 9456578022648520914282973)
        ·
          refine ⟨3546216758493195342856115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9456578022648520914282973 3546216758493195342856115)
          ·
            refine ⟨5319325137739793014284173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3546216758493195342856115 5319325137739793014284173)
            ·
              refine ⟨1994746926652422380356565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5319325137739793014284173 1994746926652422380356565)
              ·
                refine ⟨46751881093416149539607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1994746926652422380356565 46751881093416149539607)
                ·
                  rfl

theorem cell23_2458322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 7].length) (baseStart_2458322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458322 prefixEnd_2458322 := by exact prefixLift 2458322
  have htrace : WordTrace (prefixWord ++ tailWord_2458322) baseStart_2458322 baseEnd_2458322 := by
    simpa [prefixWord, tailWord_2458322, baseEnd_2458322] using wordTrace_append hprefix tailTrace_2458322
  have hstable : (prefixWord ++ tailWord_2458322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458322).length < 2 ^ (prefixWord ++ tailWord_2458322).sum := by decide
  have hdescent : baseEnd_2458322 < baseStart_2458322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458482 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_2458482 : Nat := 118140960795 + 2458482 * 2 ^ 59
def prefixEnd_2458482 : Nat := 4983230072969 + 3 ^ 40 * 2458482 * 2
def baseEnd_2458482 : Nat := 1262382946426955411568653

theorem tailTrace_2458482 : CollatzResearch.WordTrace tailWord_2458482 prefixEnd_2458482 1262382946426955411568653 := by
  unfold tailWord_2458482
  simp only [CollatzResearch.WordTrace]
  refine ⟨22417051269836766035682425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59778803386231376095153133 22417051269836766035682425)
  ·
    refine ⟨16812788452377574526761819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22417051269836766035682425 16812788452377574526761819)
    ·
      refine ⟨25219182678566361790142729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16812788452377574526761819 25219182678566361790142729)
      ·
        refine ⟨18914387008924771342607047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25219182678566361790142729 18914387008924771342607047)
        ·
          refine ⟨28371580513387157013910571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18914387008924771342607047 28371580513387157013910571)
          ·
            refine ⟨42557370770080735520865857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28371580513387157013910571 42557370770080735520865857)
            ·
              refine ⟨31918028077560551640649393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42557370770080735520865857 31918028077560551640649393)
              ·
                refine ⟨23938521058170413730487045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31918028077560551640649393 23938521058170413730487045)
                ·
                  refine ⟨4488472698406952574466321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23938521058170413730487045 4488472698406952574466321)
                  ·
                    refine ⟨3366354523805214430849741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4488472698406952574466321 3366354523805214430849741)
                    ·
                      refine ⟨1262382946426955411568653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3366354523805214430849741 1262382946426955411568653)
                      ·
                        rfl

theorem cell23_2458482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_2458482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458482 prefixEnd_2458482 := by exact prefixLift 2458482
  have htrace : WordTrace (prefixWord ++ tailWord_2458482) baseStart_2458482 baseEnd_2458482 := by
    simpa [prefixWord, tailWord_2458482, baseEnd_2458482] using wordTrace_append hprefix tailTrace_2458482
  have hstable : (prefixWord ++ tailWord_2458482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458482).length < 2 ^ (prefixWord ++ tailWord_2458482).sum := by decide
  have hdescent : baseEnd_2458482 < baseStart_2458482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458506 : List Nat := [3, 1, 2, 4, 1, 1, 1, 5, 1, 4]
def baseStart_2458506 : Nat := 118140960795 + 2458506 * 2 ^ 59
def prefixEnd_2458506 : Nat := 4983230072969 + 3 ^ 40 * 2458506 * 2
def baseEnd_2458506 : Nat := 420798423320887772556181

theorem tailTrace_2458506 : CollatzResearch.WordTrace tailWord_2458506 prefixEnd_2458506 420798423320887772556181 := by
  unfold tailWord_2458506
  simp only [CollatzResearch.WordTrace]
  refine ⟨22417270107815029060400843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59779386954173410827735581 22417270107815029060400843)
  ·
    refine ⟨33625905161722543590601265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22417270107815029060400843 33625905161722543590601265)
    ·
      refine ⟨25219428871291907692950949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33625905161722543590601265 25219428871291907692950949)
      ·
        refine ⟨4728642913367232692428303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25219428871291907692950949 4728642913367232692428303)
        ·
          refine ⟨7092964370050849038642455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4728642913367232692428303 7092964370050849038642455)
          ·
            refine ⟨10639446555076273557963683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7092964370050849038642455 10639446555076273557963683)
            ·
              refine ⟨15959169832614410336945525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10639446555076273557963683 15959169832614410336945525)
              ·
                refine ⟨1496172171807600969088643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15959169832614410336945525 1496172171807600969088643)
                ·
                  refine ⟨2244258257711401453632965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496172171807600969088643 2244258257711401453632965)
                  ·
                    refine ⟨420798423320887772556181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2244258257711401453632965 420798423320887772556181)
                    ·
                      rfl

theorem cell23_2458506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_2458506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458506 prefixEnd_2458506 := by exact prefixLift 2458506
  have htrace : WordTrace (prefixWord ++ tailWord_2458506) baseStart_2458506 baseEnd_2458506 := by
    simpa [prefixWord, tailWord_2458506, baseEnd_2458506] using wordTrace_append hprefix tailTrace_2458506
  have hstable : (prefixWord ++ tailWord_2458506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458506).length < 2 ^ (prefixWord ++ tailWord_2458506).sum := by decide
  have hdescent : baseEnd_2458506 < baseStart_2458506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458515 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 5, 5]
def baseStart_2458515 : Nat := 118140960795 + 2458515 * 2 ^ 59
def prefixEnd_2458515 : Nat := 4983230072969 + 3 ^ 40 * 2458515 * 2
def baseEnd_2458515 : Nat := 420799963762851260818667

theorem tailTrace_2458515 : CollatzResearch.WordTrace tailWord_2458515 prefixEnd_2458515 420799963762851260818667 := by
  unfold tailWord_2458515
  simp only [CollatzResearch.WordTrace]
  refine ⟨89669408688227510778680999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59779605792151673852453999 89669408688227510778680999)
  ·
    refine ⟨134504113032341266168021499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89669408688227510778680999 134504113032341266168021499)
    ·
      refine ⟨201756169548511899252032249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134504113032341266168021499 201756169548511899252032249)
      ·
        refine ⟨151317127161383924439024187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201756169548511899252032249 151317127161383924439024187)
        ·
          refine ⟨226975690742075886658536281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151317127161383924439024187 226975690742075886658536281)
          ·
            refine ⟨170231768056556914993902211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226975690742075886658536281 170231768056556914993902211)
            ·
              refine ⟨255347652084835372490853317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170231768056556914993902211 255347652084835372490853317)
              ·
                refine ⟨47877684765906632342034997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255347652084835372490853317 47877684765906632342034997)
                ·
                  refine ⟨4488532946803746782065781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47877684765906632342034997 4488532946803746782065781)
                  ·
                    refine ⟨420799963762851260818667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4488532946803746782065781 420799963762851260818667)
                    ·
                      rfl

theorem cell23_2458515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 5].length) (baseStart_2458515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458515 prefixEnd_2458515 := by exact prefixLift 2458515
  have htrace : WordTrace (prefixWord ++ tailWord_2458515) baseStart_2458515 baseEnd_2458515 := by
    simpa [prefixWord, tailWord_2458515, baseEnd_2458515] using wordTrace_append hprefix tailTrace_2458515
  have hstable : (prefixWord ++ tailWord_2458515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458515).length < 2 ^ (prefixWord ++ tailWord_2458515).sum := by decide
  have hdescent : baseEnd_2458515 < baseStart_2458515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458549 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 1, 5]
def baseStart_2458549 : Nat := 118140960795 + 2458549 * 2 ^ 59
def prefixEnd_2458549 : Nat := 4983230072969 + 3 ^ 40 * 2458549 * 2
def baseEnd_2458549 : Nat := 420805783210268883143615

theorem tailTrace_2458549 : CollatzResearch.WordTrace tailWord_2458549 prefixEnd_2458549 420805783210268883143615 := by
  unfold tailWord_2458549
  simp only [CollatzResearch.WordTrace]
  refine ⟨89670648770104334585418701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59780432513402889723612467 89670648770104334585418701)
  ·
    refine ⟨33626493288789125469532013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89670648770104334585418701 33626493288789125469532013)
    ·
      refine ⟨12609934983295922051074505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33626493288789125469532013 12609934983295922051074505)
      ·
        refine ⟨9457451237471941538305879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12609934983295922051074505 9457451237471941538305879)
        ·
          refine ⟨14186176856207912307458819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9457451237471941538305879 14186176856207912307458819)
          ·
            refine ⟨21279265284311868461188229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14186176856207912307458819 21279265284311868461188229)
            ·
              refine ⟨3989862240808475336472793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21279265284311868461188229 3989862240808475336472793)
              ·
                refine ⟨2992396680606356502354595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3989862240808475336472793 2992396680606356502354595)
                ·
                  refine ⟨4488595020909534753531893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992396680606356502354595 4488595020909534753531893)
                  ·
                    refine ⟨420805783210268883143615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4488595020909534753531893 420805783210268883143615)
                    ·
                      rfl

theorem cell23_2458549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_2458549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458549 prefixEnd_2458549 := by exact prefixLift 2458549
  have htrace : WordTrace (prefixWord ++ tailWord_2458549) baseStart_2458549 baseEnd_2458549 := by
    simpa [prefixWord, tailWord_2458549, baseEnd_2458549] using wordTrace_append hprefix tailTrace_2458549
  have hstable : (prefixWord ++ tailWord_2458549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458549).length < 2 ^ (prefixWord ++ tailWord_2458549).sum := by decide
  have hdescent : baseEnd_2458549 < baseStart_2458549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458575 : List Nat := [1, 1, 2, 1, 1, 6, 11]
def baseStart_2458575 : Nat := 118140960795 + 2458575 * 2 ^ 59
def prefixEnd_2458575 : Nat := 4983230072969 + 3 ^ 40 * 2458575 * 2
def baseEnd_2458575 : Nat := 15585564199108932687725

theorem tailTrace_2458575 : CollatzResearch.WordTrace tailWord_2458575 prefixEnd_2458575 15585564199108932687725 := by
  unfold tailWord_2458575
  simp only [CollatzResearch.WordTrace]
  refine ⟨89671597068010141025865179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59781064712006760683910119 89671597068010141025865179)
  ·
    refine ⟨134507395602015211538797769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89671597068010141025865179 134507395602015211538797769)
    ·
      refine ⟨100880546701511408654098327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134507395602015211538797769 100880546701511408654098327)
      ·
        refine ⟨151320820052267112981147491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100880546701511408654098327 151320820052267112981147491)
        ·
          refine ⟨226981230078400669471721237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151320820052267112981147491 226981230078400669471721237)
          ·
            refine ⟨10639745159925031381486933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 226981230078400669471721237 10639745159925031381486933)
            ·
              refine ⟨15585564199108932687725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10639745159925031381486933 15585564199108932687725)
              ·
                rfl

theorem cell23_2458575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 11].length) (baseStart_2458575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458575 prefixEnd_2458575 := by exact prefixLift 2458575
  have htrace : WordTrace (prefixWord ++ tailWord_2458575) baseStart_2458575 baseEnd_2458575 := by
    simpa [prefixWord, tailWord_2458575, baseEnd_2458575] using wordTrace_append hprefix tailTrace_2458575
  have hstable : (prefixWord ++ tailWord_2458575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458575).length < 2 ^ (prefixWord ++ tailWord_2458575).sum := by decide
  have hdescent : baseEnd_2458575 < baseStart_2458575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458580 : List Nat := [2, 4, 1, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_2458580 : Nat := 118140960795 + 2458580 * 2 ^ 59
def prefixEnd_2458580 : Nat := 4983230072969 + 3 ^ 40 * 2458580 * 2
def baseEnd_2458580 : Nat := 1262433267531096028143203

theorem tailTrace_2458580 : CollatzResearch.WordTrace tailWord_2458580 prefixEnd_2458580 1262433267531096028143203 := by
  unfold tailWord_2458580
  simp only [CollatzResearch.WordTrace]
  refine ⟨44835889716496013439898597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59781186288661351253198129 44835889716496013439898597)
  ·
    refine ⟨8406729321843002519980987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44835889716496013439898597 8406729321843002519980987)
    ·
      refine ⟨12610093982764503779971481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8406729321843002519980987 12610093982764503779971481)
      ·
        refine ⟨9457570487073377834978611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12610093982764503779971481 9457570487073377834978611)
        ·
          refine ⟨14186355730610066752467917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9457570487073377834978611 14186355730610066752467917)
          ·
            refine ⟨5319883398978775032175469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14186355730610066752467917 5319883398978775032175469)
            ·
              refine ⟨1994956274617040637065801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5319883398978775032175469 1994956274617040637065801)
              ·
                refine ⟨1496217205962780477799351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1994956274617040637065801 1496217205962780477799351)
                ·
                  refine ⟨2244325808944170716699027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496217205962780477799351 2244325808944170716699027)
                  ·
                    refine ⟨3366488713416256075048541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2244325808944170716699027 3366488713416256075048541)
                    ·
                      refine ⟨1262433267531096028143203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3366488713416256075048541 1262433267531096028143203)
                      ·
                        rfl

theorem cell23_2458580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_2458580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458580 prefixEnd_2458580 := by exact prefixLift 2458580
  have htrace : WordTrace (prefixWord ++ tailWord_2458580) baseStart_2458580 baseEnd_2458580 := by
    simpa [prefixWord, tailWord_2458580, baseEnd_2458580] using wordTrace_append hprefix tailTrace_2458580
  have hstable : (prefixWord ++ tailWord_2458580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458580).length < 2 ^ (prefixWord ++ tailWord_2458580).sum := by decide
  have hdescent : baseEnd_2458580 < baseStart_2458580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458589 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_2458589 : Nat := 118140960795 + 2458589 * 2 ^ 59
def prefixEnd_2458589 : Nat := 4983230072969 + 3 ^ 40 * 2458589 * 2
def baseEnd_2458589 : Nat := 1262437888856986492930661

theorem tailTrace_2458589 : CollatzResearch.WordTrace tailWord_2458589 prefixEnd_2458589 1262437888856986492930661 := by
  unfold tailWord_2458589
  simp only [CollatzResearch.WordTrace]
  refine ⟨89672107689959421416874821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59781405126639614277916547 89672107689959421416874821)
  ·
    refine ⟨16813520191867391515664029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89672107689959421416874821 16813520191867391515664029)
    ·
      refine ⟨6305070071950271818374011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16813520191867391515664029 6305070071950271818374011)
      ·
        refine ⟨9457605107925407727561017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6305070071950271818374011 9457605107925407727561017)
        ·
          refine ⟨7093203830944055795670763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9457605107925407727561017 7093203830944055795670763)
          ·
            refine ⟨10639805746416083693506145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7093203830944055795670763 10639805746416083693506145)
            ·
              refine ⟨7979854309812062770129609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10639805746416083693506145 7979854309812062770129609)
              ·
                refine ⟨5984890732359047077597207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7979854309812062770129609 5984890732359047077597207)
                ·
                  refine ⟨8977336098538570616395811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5984890732359047077597207 8977336098538570616395811)
                  ·
                    refine ⟨13466004147807855924593717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8977336098538570616395811 13466004147807855924593717)
                    ·
                      refine ⟨1262437888856986492930661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13466004147807855924593717 1262437888856986492930661)
                      ·
                        rfl

theorem cell23_2458589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_2458589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458589 prefixEnd_2458589 := by exact prefixLift 2458589
  have htrace : WordTrace (prefixWord ++ tailWord_2458589) baseStart_2458589 baseEnd_2458589 := by
    simpa [prefixWord, tailWord_2458589, baseEnd_2458589] using wordTrace_append hprefix tailTrace_2458589
  have hstable : (prefixWord ++ tailWord_2458589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458589).length < 2 ^ (prefixWord ++ tailWord_2458589).sum := by decide
  have hdescent : baseEnd_2458589 < baseStart_2458589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458606 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_2458606 : Nat := 118140960795 + 2458606 * 2 ^ 59
def prefixEnd_2458606 : Nat := 4983230072969 + 3 ^ 40 * 2458606 * 2
def baseEnd_2458606 : Nat := 1262446618028112926418083

theorem tailTrace_2458606 : CollatzResearch.WordTrace tailWord_2458606 prefixEnd_2458606 1262446618028112926418083 := by
  unfold tailWord_2458606
  simp only [CollatzResearch.WordTrace]
  refine ⟨11209090966362229165030459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59781818487265222213495781 11209090966362229165030459)
  ·
    refine ⟨16813636449543343747545689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11209090966362229165030459 16813636449543343747545689)
    ·
      refine ⟨12610227337157507810659267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16813636449543343747545689 12610227337157507810659267)
      ·
        refine ⟨18915341005736261715988901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12610227337157507810659267 18915341005736261715988901)
        ·
          refine ⟨3546626438575549071747919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18915341005736261715988901 3546626438575549071747919)
          ·
            refine ⟨5319939657863323607621879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3546626438575549071747919 5319939657863323607621879)
            ·
              refine ⟨7979909486794985411432819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5319939657863323607621879 7979909486794985411432819)
              ·
                refine ⟨11969864230192478117149229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7979909486794985411432819 11969864230192478117149229)
                ·
                  refine ⟨4488699086322179293930961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11969864230192478117149229 4488699086322179293930961)
                  ·
                    refine ⟨3366524314741634470448221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4488699086322179293930961 3366524314741634470448221)
                    ·
                      refine ⟨1262446618028112926418083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3366524314741634470448221 1262446618028112926418083)
                      ·
                        rfl

theorem cell23_2458606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_2458606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458606 prefixEnd_2458606 := by exact prefixLift 2458606
  have htrace : WordTrace (prefixWord ++ tailWord_2458606) baseStart_2458606 baseEnd_2458606 := by
    simpa [prefixWord, tailWord_2458606, baseEnd_2458606] using wordTrace_append hprefix tailTrace_2458606
  have hstable : (prefixWord ++ tailWord_2458606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458606).length < 2 ^ (prefixWord ++ tailWord_2458606).sum := by decide
  have hdescent : baseEnd_2458606 < baseStart_2458606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458626 : List Nat := [3, 4, 1, 3, 2, 10]
def baseStart_2458626 : Nat := 118140960795 + 2458626 * 2 ^ 59
def prefixEnd_2458626 : Nat := 4983230072969 + 3 ^ 40 * 2458626 * 2
def baseEnd_2458626 : Nat := 5195295833914415013037

theorem tailTrace_2458626 : CollatzResearch.WordTrace tailWord_2458626 prefixEnd_2458626 5195295833914415013037 := by
  unfold tailWord_2458626
  simp only [CollatzResearch.WordTrace]
  refine ⟨22418364297706344183992933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59782304793883584490647821 22418364297706344183992933)
  ·
    refine ⟨4203443305819939534498675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22418364297706344183992933 4203443305819939534498675)
    ·
      refine ⟨6305164958729909301748013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4203443305819939534498675 6305164958729909301748013)
      ·
        refine ⟨2364436859523715988155505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6305164958729909301748013 2364436859523715988155505)
        ·
          refine ⟨1773327644642786991116629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2364436859523715988155505 1773327644642786991116629)
          ·
            refine ⟨5195295833914415013037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1773327644642786991116629 5195295833914415013037)
            ·
              rfl

theorem cell23_2458626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 10].length) (baseStart_2458626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458626 prefixEnd_2458626 := by exact prefixLift 2458626
  have htrace : WordTrace (prefixWord ++ tailWord_2458626) baseStart_2458626 baseEnd_2458626 := by
    simpa [prefixWord, tailWord_2458626, baseEnd_2458626] using wordTrace_append hprefix tailTrace_2458626
  have hstable : (prefixWord ++ tailWord_2458626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458626).length < 2 ^ (prefixWord ++ tailWord_2458626).sum := by decide
  have hdescent : baseEnd_2458626 < baseStart_2458626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458636 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 2, 1, 3]
def baseStart_2458636 : Nat := 118140960795 + 2458636 * 2 ^ 59
def prefixEnd_2458636 : Nat := 4983230072969 + 3 ^ 40 * 2458636 * 2
def baseEnd_2458636 : Nat := 1262462022447747809042945

theorem tailTrace_2458636 : CollatzResearch.WordTrace tailWord_2458636 prefixEnd_2458636 1262462022447747809042945 := by
  unfold tailWord_2458636
  simp only [CollatzResearch.WordTrace]
  refine ⟨44836910960394574221917881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59782547947192765629223841 44836910960394574221917881)
  ·
    refine ⟨33627683220295930666438411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44836910960394574221917881 33627683220295930666438411)
    ·
      refine ⟨50441524830443895999657617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33627683220295930666438411 50441524830443895999657617)
      ·
        refine ⟨37831143622832921999743213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50441524830443895999657617 37831143622832921999743213)
        ·
          refine ⟨14186678858562345749903705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37831143622832921999743213 14186678858562345749903705)
          ·
            refine ⟨10640009143921759312427779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14186678858562345749903705 10640009143921759312427779)
            ·
              refine ⟨15960013715882638968641669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10640009143921759312427779 15960013715882638968641669)
              ·
                refine ⟨2992502571727994806620313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15960013715882638968641669 2992502571727994806620313)
                ·
                  refine ⟨2244376928795996104965235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2992502571727994806620313 2244376928795996104965235)
                  ·
                    refine ⟨3366565393193994157447853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2244376928795996104965235 3366565393193994157447853)
                    ·
                      refine ⟨1262462022447747809042945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3366565393193994157447853 1262462022447747809042945)
                      ·
                        rfl

theorem cell23_2458636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_2458636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458636 prefixEnd_2458636 := by exact prefixLift 2458636
  have htrace : WordTrace (prefixWord ++ tailWord_2458636) baseStart_2458636 baseEnd_2458636 := by
    simpa [prefixWord, tailWord_2458636, baseEnd_2458636] using wordTrace_append hprefix tailTrace_2458636
  have hstable : (prefixWord ++ tailWord_2458636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458636).length < 2 ^ (prefixWord ++ tailWord_2458636).sum := by decide
  have hdescent : baseEnd_2458636 < baseStart_2458636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458663 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_2458663 : Nat := 118140960795 + 2458663 * 2 ^ 59
def prefixEnd_2458663 : Nat := 4983230072969 + 3 ^ 40 * 2458663 * 2
def baseEnd_2458663 : Nat := 1262475886425419203405321

theorem tailTrace_2458663 : CollatzResearch.WordTrace tailWord_2458663 prefixEnd_2458663 1262475886425419203405321 := by
  unfold tailWord_2458663
  simp only [CollatzResearch.WordTrace]
  refine ⟨89674806691691332055068643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59783204461127554703379095 89674806691691332055068643)
  ·
    refine ⟨134512210037536998082602965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89674806691691332055068643 134512210037536998082602965)
    ·
      refine ⟨3152629922754773392561007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 134512210037536998082602965 3152629922754773392561007)
      ·
        refine ⟨4728944884132160088841511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3152629922754773392561007 4728944884132160088841511)
        ·
          refine ⟨7093417326198240133262267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4728944884132160088841511 7093417326198240133262267)
          ·
            refine ⟨10640125989297360199893401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7093417326198240133262267 10640125989297360199893401)
            ·
              refine ⟨7980094491973020149920051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10640125989297360199893401 7980094491973020149920051)
              ·
                refine ⟨11970141737959530224880077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7980094491973020149920051 11970141737959530224880077)
                ·
                  refine ⟨4488803151734823834330029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11970141737959530224880077 4488803151734823834330029)
                  ·
                    refine ⟨1683301181900558937873761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4488803151734823834330029 1683301181900558937873761)
                    ·
                      refine ⟨1262475886425419203405321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1683301181900558937873761 1262475886425419203405321)
                      ·
                        rfl

theorem cell23_2458663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_2458663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458663 prefixEnd_2458663 := by exact prefixLift 2458663
  have htrace : WordTrace (prefixWord ++ tailWord_2458663) baseStart_2458663 baseEnd_2458663 := by
    simpa [prefixWord, tailWord_2458663, baseEnd_2458663] using wordTrace_append hprefix tailTrace_2458663
  have hstable : (prefixWord ++ tailWord_2458663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458663).length < 2 ^ (prefixWord ++ tailWord_2458663).sum := by decide
  have hdescent : baseEnd_2458663 < baseStart_2458663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458672 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 4]
def baseStart_2458672 : Nat := 118140960795 + 2458672 * 2 ^ 59
def prefixEnd_2458672 : Nat := 4983230072969 + 3 ^ 40 * 2458672 * 2
def baseEnd_2458672 : Nat := 1262480507751309668192779

theorem tailTrace_2458672 : CollatzResearch.WordTrace tailWord_2458672 prefixEnd_2458672 1262480507751309668192779 := by
  unfold tailWord_2458672
  simp only [CollatzResearch.WordTrace]
  refine ⟨44837567474329363296073135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59783423299105817728097513 44837567474329363296073135)
  ·
    refine ⟨67256351211494044944109703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44837567474329363296073135 67256351211494044944109703)
    ·
      refine ⟨100884526817241067416164555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67256351211494044944109703 100884526817241067416164555)
      ·
        refine ⟨151326790225861601124246833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100884526817241067416164555 151326790225861601124246833)
        ·
          refine ⟨113495092669396200843185125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151326790225861601124246833 113495092669396200843185125)
          ·
            refine ⟨21280329875511787658097211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113495092669396200843185125 21280329875511787658097211)
            ·
              refine ⟨31920494813267681487145817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21280329875511787658097211 31920494813267681487145817)
              ·
                refine ⟨23940371109950761115359363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31920494813267681487145817 23940371109950761115359363)
                ·
                  refine ⟨35910556664926141673039045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23940371109950761115359363 35910556664926141673039045)
                  ·
                    refine ⟨6733229374673651563694821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35910556664926141673039045 6733229374673651563694821)
                    ·
                      refine ⟨1262480507751309668192779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6733229374673651563694821 1262480507751309668192779)
                      ·
                        rfl

theorem cell23_2458672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_2458672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458672 prefixEnd_2458672 := by exact prefixLift 2458672
  have htrace : WordTrace (prefixWord ++ tailWord_2458672) baseStart_2458672 baseEnd_2458672 := by
    simpa [prefixWord, tailWord_2458672, baseEnd_2458672] using wordTrace_append hprefix tailTrace_2458672
  have hstable : (prefixWord ++ tailWord_2458672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458672).length < 2 ^ (prefixWord ++ tailWord_2458672).sum := by decide
  have hdescent : baseEnd_2458672 < baseStart_2458672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
