import V185TrunkScan23Chunk0002

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_17370 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2]
def baseStart_17370 : Nat := 118140960795 + 17370 * 2 ^ 59
def prefixEnd_17370 : Nat := 4983230072969 + 3 ^ 40 * 17370 * 2
def baseEnd_17370 : Nat := 8919158968702273495123

theorem tailTrace_17370 : CollatzResearch.WordTrace tailWord_17370 prefixEnd_17370 8919158968702273495123 := by
  unfold tailWord_17370
  simp only [CollatzResearch.WordTrace]
  refine ⟨158383986769732851232391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 422357298052620936619709 158383986769732851232391)
  ·
    refine ⟨237575980154599276848587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158383986769732851232391 237575980154599276848587)
    ·
      refine ⟨356363970231898915272881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237575980154599276848587 356363970231898915272881)
      ·
        refine ⟨267272977673924186454661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356363970231898915272881 267272977673924186454661)
        ·
          refine ⟨50113683313860784960249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267272977673924186454661 50113683313860784960249)
          ·
            refine ⟨37585262485395588720187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50113683313860784960249 37585262485395588720187)
            ·
              refine ⟨56377893728093383080281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37585262485395588720187 56377893728093383080281)
              ·
                refine ⟨42283420296070037310211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56377893728093383080281 42283420296070037310211)
                ·
                  refine ⟨63425130444105055965317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42283420296070037310211 63425130444105055965317)
                  ·
                    refine ⟨11892211958269697993497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63425130444105055965317 11892211958269697993497)
                    ·
                      refine ⟨8919158968702273495123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11892211958269697993497 8919158968702273495123)
                      ·
                        rfl

theorem cell23_17370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_17370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17370 prefixEnd_17370 := by exact prefixLift 17370
  have htrace : WordTrace (prefixWord ++ tailWord_17370) baseStart_17370 baseEnd_17370 := by
    simpa [prefixWord, tailWord_17370, baseEnd_17370] using wordTrace_append hprefix tailTrace_17370
  have hstable : (prefixWord ++ tailWord_17370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17370).length < 2 ^ (prefixWord ++ tailWord_17370).sum := by decide
  have hdescent : baseEnd_17370 < baseStart_17370 := by decide
  rcases family_descends (prefixWord ++ tailWord_17370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17373 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_17373 : Nat := 118140960795 + 17373 * 2 ^ 59
def prefixEnd_17373 : Nat := 4983230072969 + 3 ^ 40 * 17373 * 2
def baseEnd_17373 : Nat := 8920699410665761757609

theorem tailTrace_17373 : CollatzResearch.WordTrace tailWord_17373 prefixEnd_17373 8920699410665761757609 := by
  unfold tailWord_17373
  simp only [CollatzResearch.WordTrace]
  refine ⟨633645366068062917288773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 422430244045375278192515 633645366068062917288773)
  ·
    refine ⟨118808506137761796991645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 633645366068062917288773 118808506137761796991645)
    ·
      refine ⟨44553189801660673871867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118808506137761796991645 44553189801660673871867)
      ·
        refine ⟨66829784702491010807801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44553189801660673871867 66829784702491010807801)
        ·
          refine ⟨50122338526868258105851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66829784702491010807801 50122338526868258105851)
          ·
            refine ⟨75183507790302387158777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50122338526868258105851 75183507790302387158777)
            ·
              refine ⟨56387630842726790369083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75183507790302387158777 56387630842726790369083)
              ·
                refine ⟨84581446264090185553625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56387630842726790369083 84581446264090185553625)
                ·
                  refine ⟨63436084698067639165219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84581446264090185553625 63436084698067639165219)
                  ·
                    refine ⟨95154127047101458747829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63436084698067639165219 95154127047101458747829)
                    ·
                      refine ⟨8920699410665761757609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 95154127047101458747829 8920699410665761757609)
                      ·
                        rfl

theorem cell23_17373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_17373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17373 prefixEnd_17373 := by exact prefixLift 17373
  have htrace : WordTrace (prefixWord ++ tailWord_17373) baseStart_17373 baseEnd_17373 := by
    simpa [prefixWord, tailWord_17373, baseEnd_17373] using wordTrace_append hprefix tailTrace_17373
  have hstable : (prefixWord ++ tailWord_17373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17373).length < 2 ^ (prefixWord ++ tailWord_17373).sum := by decide
  have hdescent : baseEnd_17373 < baseStart_17373 := by decide
  rcases family_descends (prefixWord ++ tailWord_17373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17413 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 2, 5, 2]
def baseStart_17413 : Nat := 118140960795 + 17413 * 2 ^ 59
def prefixEnd_17413 : Nat := 4983230072969 + 3 ^ 40 * 17413 * 2
def baseEnd_17413 : Nat := 8941238636845605257425

theorem tailTrace_17413 : CollatzResearch.WordTrace tailWord_17413 prefixEnd_17413 8941238636845605257425 := by
  unfold tailWord_17413
  simp only [CollatzResearch.WordTrace]
  refine ⟨635104285923149748744893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 423402857282099832496595 635104285923149748744893)
  ·
    refine ⟨238164107221181155779335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 635104285923149748744893 238164107221181155779335)
    ·
      refine ⟨357246160831771733669003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238164107221181155779335 357246160831771733669003)
      ·
        refine ⟨535869241247657600503505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357246160831771733669003 535869241247657600503505)
        ·
          refine ⟨401901930935743200377629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535869241247657600503505 401901930935743200377629)
          ·
            refine ⟨150713224100903700141611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 401901930935743200377629 150713224100903700141611)
            ·
              refine ⟨226069836151355550212417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150713224100903700141611 226069836151355550212417)
              ·
                refine ⟨169552377113516662659313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226069836151355550212417 169552377113516662659313)
                ·
                  refine ⟨127164282835137496994485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169552377113516662659313 127164282835137496994485)
                  ·
                    refine ⟨11921651515794140343233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 127164282835137496994485 11921651515794140343233)
                    ·
                      refine ⟨8941238636845605257425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11921651515794140343233 8941238636845605257425)
                      ·
                        rfl

theorem cell23_17413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 5, 2].length) (baseStart_17413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17413 prefixEnd_17413 := by exact prefixLift 17413
  have htrace : WordTrace (prefixWord ++ tailWord_17413) baseStart_17413 baseEnd_17413 := by
    simpa [prefixWord, tailWord_17413, baseEnd_17413] using wordTrace_append hprefix tailTrace_17413
  have hstable : (prefixWord ++ tailWord_17413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17413).length < 2 ^ (prefixWord ++ tailWord_17413).sum := by decide
  have hdescent : baseEnd_17413 < baseStart_17413 := by decide
  rcases family_descends (prefixWord ++ tailWord_17413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17456 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_17456 : Nat := 118140960795 + 17456 * 2 ^ 59
def prefixEnd_17456 : Nat := 4983230072969 + 3 ^ 40 * 17456 * 2
def baseEnd_17456 : Nat := 8963318304988937019727

theorem tailTrace_17456 : CollatzResearch.WordTrace tailWord_17456 prefixEnd_17456 8963318304988937019727 := by
  unfold tailWord_17456
  simp only [CollatzResearch.WordTrace]
  refine ⟨318336312383684046280111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 424448416511578728373481 318336312383684046280111)
  ·
    refine ⟨477504468575526069420167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 318336312383684046280111 477504468575526069420167)
    ·
      refine ⟨716256702863289104130251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477504468575526069420167 716256702863289104130251)
      ·
        refine ⟨1074385054294933656195377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 716256702863289104130251 1074385054294933656195377)
        ·
          refine ⟨805788790721200242146533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1074385054294933656195377 805788790721200242146533)
          ·
            refine ⟨151085398260225045402475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 805788790721200242146533 151085398260225045402475)
            ·
              refine ⟨226628097390337568103713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151085398260225045402475 226628097390337568103713)
              ·
                refine ⟨169971073042753176077785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226628097390337568103713 169971073042753176077785)
                ·
                  refine ⟨127478304782064882058339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169971073042753176077785 127478304782064882058339)
                  ·
                    refine ⟨191217457173097323087509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127478304782064882058339 191217457173097323087509)
                    ·
                      refine ⟨8963318304988937019727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 191217457173097323087509 8963318304988937019727)
                      ·
                        rfl

theorem cell23_17456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_17456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17456 prefixEnd_17456 := by exact prefixLift 17456
  have htrace : WordTrace (prefixWord ++ tailWord_17456) baseStart_17456 baseEnd_17456 := by
    simpa [prefixWord, tailWord_17456, baseEnd_17456] using wordTrace_append hprefix tailTrace_17456
  have hstable : (prefixWord ++ tailWord_17456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17456).length < 2 ^ (prefixWord ++ tailWord_17456).sum := by decide
  have hdescent : baseEnd_17456 < baseStart_17456 := by decide
  rcases family_descends (prefixWord ++ tailWord_17456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17460 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_17460 : Nat := 118140960795 + 17460 * 2 ^ 59
def prefixEnd_17460 : Nat := 4983230072969 + 3 ^ 40 * 17460 * 2
def baseEnd_17460 : Nat := 8965372227606921369709

theorem tailTrace_17460 : CollatzResearch.WordTrace tailWord_17460 prefixEnd_17460 8965372227606921369709 := by
  unfold tailWord_17460
  simp only [CollatzResearch.WordTrace]
  refine ⟨318409258376438387852917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 424545677835251183803889 318409258376438387852917)
  ·
    refine ⟨29850867972791098861211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 318409258376438387852917 29850867972791098861211)
    ·
      refine ⟨44776301959186648291817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29850867972791098861211 44776301959186648291817)
      ·
        refine ⟨33582226469389986218863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44776301959186648291817 33582226469389986218863)
        ·
          refine ⟨50373339704084979328295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33582226469389986218863 50373339704084979328295)
          ·
            refine ⟨75560009556127468992443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50373339704084979328295 75560009556127468992443)
            ·
              refine ⟨113340014334191203488665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75560009556127468992443 113340014334191203488665)
              ·
                refine ⟨85005010750643402616499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113340014334191203488665 85005010750643402616499)
                ·
                  refine ⟨127507516125965103924749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85005010750643402616499 127507516125965103924749)
                  ·
                    refine ⟨47815318547236913971781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127507516125965103924749 47815318547236913971781)
                    ·
                      refine ⟨8965372227606921369709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 47815318547236913971781 8965372227606921369709)
                      ·
                        rfl

theorem cell23_17460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_17460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17460 prefixEnd_17460 := by exact prefixLift 17460
  have htrace : WordTrace (prefixWord ++ tailWord_17460) baseStart_17460 baseEnd_17460 := by
    simpa [prefixWord, tailWord_17460, baseEnd_17460] using wordTrace_append hprefix tailTrace_17460
  have hstable : (prefixWord ++ tailWord_17460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17460).length < 2 ^ (prefixWord ++ tailWord_17460).sum := by decide
  have hdescent : baseEnd_17460 < baseStart_17460 := by decide
  rcases family_descends (prefixWord ++ tailWord_17460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17494 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_17494 : Nat := 118140960795 + 17494 * 2 ^ 59
def prefixEnd_17494 : Nat := 4983230072969 + 3 ^ 40 * 17494 * 2
def baseEnd_17494 : Nat := 8982830569859788344553

theorem tailTrace_17494 : CollatzResearch.WordTrace tailWord_17494 prefixEnd_17494 8982830569859788344553 := by
  unfold tailWord_17494
  simp only [CollatzResearch.WordTrace]
  refine ⟨39878662414356286402721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 425372399086467054962357 39878662414356286402721)
  ·
    refine ⟨29908996810767214802041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39878662414356286402721 29908996810767214802041)
    ·
      refine ⟨22431747608075411101531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29908996810767214802041 22431747608075411101531)
      ·
        refine ⟨33647621412113116652297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22431747608075411101531 33647621412113116652297)
        ·
          refine ⟨25235716059084837489223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33647621412113116652297 25235716059084837489223)
          ·
            refine ⟨37853574088627256233835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25235716059084837489223 37853574088627256233835)
            ·
              refine ⟨56780361132940884350753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37853574088627256233835 56780361132940884350753)
              ·
                refine ⟨42585270849705663263065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56780361132940884350753 42585270849705663263065)
                ·
                  refine ⟨31938953137279247447299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42585270849705663263065 31938953137279247447299)
                  ·
                    refine ⟨47908429705918871170949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31938953137279247447299 47908429705918871170949)
                    ·
                      refine ⟨8982830569859788344553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 47908429705918871170949 8982830569859788344553)
                      ·
                        rfl

theorem cell23_17494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_17494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17494 prefixEnd_17494 := by exact prefixLift 17494
  have htrace : WordTrace (prefixWord ++ tailWord_17494) baseStart_17494 baseEnd_17494 := by
    simpa [prefixWord, tailWord_17494, baseEnd_17494] using wordTrace_append hprefix tailTrace_17494
  have hstable : (prefixWord ++ tailWord_17494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17494).length < 2 ^ (prefixWord ++ tailWord_17494).sum := by decide
  have hdescent : baseEnd_17494 < baseStart_17494 := by decide
  rcases family_descends (prefixWord ++ tailWord_17494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17517 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 6]
def baseStart_17517 : Nat := 118140960795 + 17517 * 2 ^ 59
def prefixEnd_17517 : Nat := 4983230072969 + 3 ^ 40 * 17517 * 2
def baseEnd_17517 : Nat := 999404513879244261883

theorem tailTrace_17517 : CollatzResearch.WordTrace tailWord_17517 prefixEnd_17517 999404513879244261883 := by
  unfold tailWord_17517
  simp only [CollatzResearch.WordTrace]
  refine ⟨638897477546375510530805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 425931651697583673687203 638897477546375510530805)
  ·
    refine ⟨59896638519972704112263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 638897477546375510530805 59896638519972704112263)
    ·
      refine ⟨89844957779959056168395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59896638519972704112263 89844957779959056168395)
      ·
        refine ⟨134767436669938584252593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89844957779959056168395 134767436669938584252593)
        ·
          refine ⟨101075577502453938189445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134767436669938584252593 101075577502453938189445)
          ·
            refine ⟨18951670781710113410521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101075577502453938189445 18951670781710113410521)
            ·
              refine ⟨14213753086282585057891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18951670781710113410521 14213753086282585057891)
              ·
                refine ⟨21320629629423877586837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14213753086282585057891 21320629629423877586837)
                ·
                  refine ⟨999404513879244261883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21320629629423877586837 999404513879244261883)
                  ·
                    rfl

theorem cell23_17517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_17517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17517 prefixEnd_17517 := by exact prefixLift 17517
  have htrace : WordTrace (prefixWord ++ tailWord_17517) baseStart_17517 baseEnd_17517 := by
    simpa [prefixWord, tailWord_17517, baseEnd_17517] using wordTrace_append hprefix tailTrace_17517
  have hstable : (prefixWord ++ tailWord_17517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17517).length < 2 ^ (prefixWord ++ tailWord_17517).sum := by decide
  have hdescent : baseEnd_17517 < baseStart_17517 := by decide
  rcases family_descends (prefixWord ++ tailWord_17517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17520 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 4, 3, 2]
def baseStart_17520 : Nat := 118140960795 + 17520 * 2 ^ 59
def prefixEnd_17520 : Nat := 4983230072969 + 3 ^ 40 * 17520 * 2
def baseEnd_17520 : Nat := 8996181066876686619433

theorem tailTrace_17520 : CollatzResearch.WordTrace tailWord_17520 prefixEnd_17520 8996181066876686619433 := by
  unfold tailWord_17520
  simp only [CollatzResearch.WordTrace]
  refine ⟨319503448267753511445007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 426004597690338015260009 319503448267753511445007)
  ·
    refine ⟨479255172401630267167511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 319503448267753511445007 479255172401630267167511)
    ·
      refine ⟨718882758602445400751267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 479255172401630267167511 718882758602445400751267)
      ·
        refine ⟨1078324137903668101126901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718882758602445400751267 1078324137903668101126901)
        ·
          refine ⟨101092887928468884480647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1078324137903668101126901 101092887928468884480647)
          ·
            refine ⟨151639331892703326720971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101092887928468884480647 151639331892703326720971)
            ·
              refine ⟨227458997839054990081457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151639331892703326720971 227458997839054990081457)
              ·
                refine ⟨170594248379291242561093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227458997839054990081457 170594248379291242561093)
                ·
                  refine ⟨31986421571117107980205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170594248379291242561093 31986421571117107980205)
                  ·
                    refine ⟨11994908089168915492577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31986421571117107980205 11994908089168915492577)
                    ·
                      refine ⟨8996181066876686619433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11994908089168915492577 8996181066876686619433)
                      ·
                        rfl

theorem cell23_17520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 3, 2].length) (baseStart_17520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17520 prefixEnd_17520 := by exact prefixLift 17520
  have htrace : WordTrace (prefixWord ++ tailWord_17520) baseStart_17520 baseEnd_17520 := by
    simpa [prefixWord, tailWord_17520, baseEnd_17520] using wordTrace_append hprefix tailTrace_17520
  have hstable : (prefixWord ++ tailWord_17520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17520).length < 2 ^ (prefixWord ++ tailWord_17520).sum := by decide
  have hdescent : baseEnd_17520 < baseStart_17520 := by decide
  rcases family_descends (prefixWord ++ tailWord_17520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17537 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_17537 : Nat := 118140960795 + 17537 * 2 ^ 59
def prefixEnd_17537 : Nat := 4983230072969 + 3 ^ 40 * 17537 * 2
def baseEnd_17537 : Nat := 9004910238003120106855

theorem tailTrace_17537 : CollatzResearch.WordTrace tailWord_17537 prefixEnd_17537 9004910238003120106855 := by
  unfold tailWord_17537
  simp only [CollatzResearch.WordTrace]
  refine ⟨639626937473918926258865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 426417958315945950839243 639626937473918926258865)
  ·
    refine ⟨479720203105439194694149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 639626937473918926258865 479720203105439194694149)
    ·
      refine ⟨89947538082269849005153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 479720203105439194694149 89947538082269849005153)
      ·
        refine ⟨67460653561702386753865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89947538082269849005153 67460653561702386753865)
        ·
          refine ⟨50595490171276790065399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67460653561702386753865 50595490171276790065399)
          ·
            refine ⟨75893235256915185098099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50595490171276790065399 75893235256915185098099)
            ·
              refine ⟨113839852885372777647149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75893235256915185098099 113839852885372777647149)
              ·
                refine ⟨42689944832014791617681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113839852885372777647149 42689944832014791617681)
                ·
                  refine ⟨32017458624011093713261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42689944832014791617681 32017458624011093713261)
                  ·
                    refine ⟨12006546984004160142473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32017458624011093713261 12006546984004160142473)
                    ·
                      refine ⟨9004910238003120106855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12006546984004160142473 9004910238003120106855)
                      ·
                        rfl

theorem cell23_17537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_17537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17537 prefixEnd_17537 := by exact prefixLift 17537
  have htrace : WordTrace (prefixWord ++ tailWord_17537) baseStart_17537 baseEnd_17537 := by
    simpa [prefixWord, tailWord_17537, baseEnd_17537] using wordTrace_append hprefix tailTrace_17537
  have hstable : (prefixWord ++ tailWord_17537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17537).length < 2 ^ (prefixWord ++ tailWord_17537).sum := by decide
  have hdescent : baseEnd_17537 < baseStart_17537 := by decide
  rcases family_descends (prefixWord ++ tailWord_17537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17573 : List Nat := [1, 3, 1, 2, 1, 4, 3, 8]
def baseStart_17573 : Nat := 118140960795 + 17573 * 2 ^ 59
def prefixEnd_17573 : Nat := 4983230072969 + 3 ^ 40 * 17573 * 2
def baseEnd_17573 : Nat := 334199834872777009507

theorem tailTrace_17573 : CollatzResearch.WordTrace tailWord_17573 prefixEnd_17573 334199834872777009507 := by
  unfold tailWord_17573
  simp only [CollatzResearch.WordTrace]
  refine ⟨640939965343497074569373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 427293310228998049712915 640939965343497074569373)
  ·
    refine ⟨240352487003811402963515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 640939965343497074569373 240352487003811402963515)
    ·
      refine ⟨360528730505717104445273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240352487003811402963515 360528730505717104445273)
      ·
        refine ⟨270396547879287828333955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360528730505717104445273 270396547879287828333955)
        ·
          refine ⟨405594821818931742500933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270396547879287828333955 405594821818931742500933)
          ·
            refine ⟨76049029091049701718925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 405594821818931742500933 76049029091049701718925)
            ·
              refine ⟨28518385909143638144597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76049029091049701718925 28518385909143638144597)
              ·
                refine ⟨334199834872777009507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28518385909143638144597 334199834872777009507)
                ·
                  rfl

theorem cell23_17573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 8].length) (baseStart_17573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17573 prefixEnd_17573 := by exact prefixLift 17573
  have htrace : WordTrace (prefixWord ++ tailWord_17573) baseStart_17573 baseEnd_17573 := by
    simpa [prefixWord, tailWord_17573, baseEnd_17573] using wordTrace_append hprefix tailTrace_17573
  have hstable : (prefixWord ++ tailWord_17573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17573).length < 2 ^ (prefixWord ++ tailWord_17573).sum := by decide
  have hdescent : baseEnd_17573 < baseStart_17573 := by decide
  rcases family_descends (prefixWord ++ tailWord_17573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17601 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_17601 : Nat := 118140960795 + 17601 * 2 ^ 59
def prefixEnd_17601 : Nat := 4983230072969 + 3 ^ 40 * 17601 * 2
def baseEnd_17601 : Nat := 9037772999890869706561

theorem tailTrace_17601 : CollatzResearch.WordTrace tailWord_17601 prefixEnd_17601 9037772999890869706561 := by
  unfold tailWord_17601
  simp only [CollatzResearch.WordTrace]
  refine ⟨641961209242057856588657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 427974139494705237725771 641961209242057856588657)
  ·
    refine ⟨481470906931543392441493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 641961209242057856588657 481470906931543392441493)
    ·
      refine ⟨22568948762416096520695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 481470906931543392441493 22568948762416096520695)
      ·
        refine ⟨33853423143624144781043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22568948762416096520695 33853423143624144781043)
        ·
          refine ⟨50780134715436217171565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33853423143624144781043 50780134715436217171565)
          ·
            refine ⟨19042550518288581439337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50780134715436217171565 19042550518288581439337)
            ·
              refine ⟨14281912888716436079503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19042550518288581439337 14281912888716436079503)
              ·
                refine ⟨21422869333074654119255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14281912888716436079503 21422869333074654119255)
                ·
                  refine ⟨32134303999611981178883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21422869333074654119255 32134303999611981178883)
                  ·
                    refine ⟨48201455999417971768325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32134303999611981178883 48201455999417971768325)
                    ·
                      refine ⟨9037772999890869706561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 48201455999417971768325 9037772999890869706561)
                      ·
                        rfl

theorem cell23_17601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_17601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17601 prefixEnd_17601 := by exact prefixLift 17601
  have htrace : WordTrace (prefixWord ++ tailWord_17601) baseStart_17601 baseEnd_17601 := by
    simpa [prefixWord, tailWord_17601, baseEnd_17601] using wordTrace_append hprefix tailTrace_17601
  have hstable : (prefixWord ++ tailWord_17601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17601).length < 2 ^ (prefixWord ++ tailWord_17601).sum := by decide
  have hdescent : baseEnd_17601 < baseStart_17601 := by decide
  rcases family_descends (prefixWord ++ tailWord_17601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17604 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_17604 : Nat := 118140960795 + 17604 * 2 ^ 59
def prefixEnd_17604 : Nat := 4983230072969 + 3 ^ 40 * 17604 * 2
def baseEnd_17604 : Nat := 9039313441854357969047

theorem tailTrace_17604 : CollatzResearch.WordTrace tailWord_17604 prefixEnd_17604 9039313441854357969047 := by
  unfold tailWord_17604
  simp only [CollatzResearch.WordTrace]
  refine ⟨321035314115594684473933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 428047085487459579298577 321035314115594684473933)
  ·
    refine ⟨120388242793348006677725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 321035314115594684473933 120388242793348006677725)
    ·
      refine ⟨45145591047505502504147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120388242793348006677725 45145591047505502504147)
      ·
        refine ⟨67718386571258253756221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45145591047505502504147 67718386571258253756221)
        ·
          refine ⟨25394394964221845158583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67718386571258253756221 25394394964221845158583)
          ·
            refine ⟨38091592446332767737875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25394394964221845158583 38091592446332767737875)
            ·
              refine ⟨57137388669499151606813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38091592446332767737875 57137388669499151606813)
              ·
                refine ⟨21426520751062181852555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57137388669499151606813 21426520751062181852555)
                ·
                  refine ⟨32139781126593272778833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21426520751062181852555 32139781126593272778833)
                  ·
                    refine ⟨24104835844944954584125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32139781126593272778833 24104835844944954584125)
                    ·
                      refine ⟨9039313441854357969047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 24104835844944954584125 9039313441854357969047)
                      ·
                        rfl

theorem cell23_17604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_17604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17604 prefixEnd_17604 := by exact prefixLift 17604
  have htrace : WordTrace (prefixWord ++ tailWord_17604) baseStart_17604 baseEnd_17604 := by
    simpa [prefixWord, tailWord_17604, baseEnd_17604] using wordTrace_append hprefix tailTrace_17604
  have hstable : (prefixWord ++ tailWord_17604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17604).length < 2 ^ (prefixWord ++ tailWord_17604).sum := by decide
  have hdescent : baseEnd_17604 < baseStart_17604 := by decide
  rcases family_descends (prefixWord ++ tailWord_17604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17623 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_17623 : Nat := 118140960795 + 17623 * 2 ^ 59
def prefixEnd_17623 : Nat := 4983230072969 + 3 ^ 40 * 17623 * 2
def baseEnd_17623 : Nat := 9049069574289783631459

theorem tailTrace_17623 : CollatzResearch.WordTrace tailWord_17623 prefixEnd_17623 9049069574289783631459 := by
  unfold tailWord_17623
  simp only [CollatzResearch.WordTrace]
  refine ⟨642763615162355613889523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 428509076774903742593015 642763615162355613889523)
  ·
    refine ⟨964145422743533420834285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 642763615162355613889523 964145422743533420834285)
    ·
      refine ⟨361554533528825032812857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 964145422743533420834285 361554533528825032812857)
      ·
        refine ⟨271165900146618774609643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361554533528825032812857 271165900146618774609643)
        ·
          refine ⟨406748850219928161914465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271165900146618774609643 406748850219928161914465)
          ·
            refine ⟨305061637664946121435849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406748850219928161914465 305061637664946121435849)
            ·
              refine ⟨228796228248709591076887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305061637664946121435849 228796228248709591076887)
              ·
                refine ⟨343194342373064386615331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228796228248709591076887 343194342373064386615331)
                ·
                  refine ⟨514791513559596579922997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343194342373064386615331 514791513559596579922997)
                  ·
                    refine ⟨48261704396212179367781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 514791513559596579922997 48261704396212179367781)
                    ·
                      refine ⟨9049069574289783631459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 48261704396212179367781 9049069574289783631459)
                      ·
                        rfl

theorem cell23_17623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_17623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17623 prefixEnd_17623 := by exact prefixLift 17623
  have htrace : WordTrace (prefixWord ++ tailWord_17623) baseStart_17623 baseEnd_17623 := by
    simpa [prefixWord, tailWord_17623, baseEnd_17623] using wordTrace_append hprefix tailTrace_17623
  have hstable : (prefixWord ++ tailWord_17623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17623).length < 2 ^ (prefixWord ++ tailWord_17623).sum := by decide
  have hdescent : baseEnd_17623 < baseStart_17623 := by decide
  rcases family_descends (prefixWord ++ tailWord_17623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17644 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 1, 3, 2]
def baseStart_17644 : Nat := 118140960795 + 17644 * 2 ^ 59
def prefixEnd_17644 : Nat := 4983230072969 + 3 ^ 40 * 17644 * 2
def baseEnd_17644 : Nat := 9059852668034201468863

theorem tailTrace_17644 : CollatzResearch.WordTrace tailWord_17644 prefixEnd_17644 9059852668034201468863 := by
  unfold tailWord_17644
  simp only [CollatzResearch.WordTrace]
  refine ⟨321764774043138100201993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 429019698724184133602657 321764774043138100201993)
  ·
    refine ⟨241323580532353575151495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 321764774043138100201993 241323580532353575151495)
    ·
      refine ⟨361985370798530362727243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241323580532353575151495 361985370798530362727243)
      ·
        refine ⟨542978056197795544090865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361985370798530362727243 542978056197795544090865)
        ·
          refine ⟨407233542148346658068149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542978056197795544090865 407233542148346658068149)
          ·
            refine ⟨38178144576407499193889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 407233542148346658068149 38178144576407499193889)
            ·
              refine ⟨28633608432305624395417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38178144576407499193889 28633608432305624395417)
              ·
                refine ⟨21475206324229218296563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28633608432305624395417 21475206324229218296563)
                ·
                  refine ⟨32212809486343827444845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21475206324229218296563 32212809486343827444845)
                  ·
                    refine ⟨12079803557378935291817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32212809486343827444845 12079803557378935291817)
                    ·
                      refine ⟨9059852668034201468863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12079803557378935291817 9059852668034201468863)
                      ·
                        rfl

theorem cell23_17644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 3, 2].length) (baseStart_17644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17644 prefixEnd_17644 := by exact prefixLift 17644
  have htrace : WordTrace (prefixWord ++ tailWord_17644) baseStart_17644 baseEnd_17644 := by
    simpa [prefixWord, tailWord_17644, baseEnd_17644] using wordTrace_append hprefix tailTrace_17644
  have hstable : (prefixWord ++ tailWord_17644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17644).length < 2 ^ (prefixWord ++ tailWord_17644).sum := by decide
  have hdescent : baseEnd_17644 < baseStart_17644 := by decide
  rcases family_descends (prefixWord ++ tailWord_17644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17657 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 6, 2, 2]
def baseStart_17657 : Nat := 118140960795 + 17657 * 2 ^ 59
def prefixEnd_17657 : Nat := 4983230072969 + 3 ^ 40 * 17657 * 2
def baseEnd_17657 : Nat := 9066527916542650606303

theorem tailTrace_17657 : CollatzResearch.WordTrace tailWord_17657 prefixEnd_17657 9066527916542650606303 := by
  unfold tailWord_17657
  simp only [CollatzResearch.WordTrace]
  refine ⟨644003697039179420627225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 429335798026119613751483 644003697039179420627225)
  ·
    refine ⟨483002772779384565470419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 644003697039179420627225 483002772779384565470419)
    ·
      refine ⟨724504159169076848205629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483002772779384565470419 724504159169076848205629)
      ·
        refine ⟨271689059688403818077111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 724504159169076848205629 271689059688403818077111)
        ·
          refine ⟨407533589532605727115667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271689059688403818077111 407533589532605727115667)
          ·
            refine ⟨611300384298908590673501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407533589532605727115667 611300384298908590673501)
            ·
              refine ⟨229237644112090721502563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 611300384298908590673501 229237644112090721502563)
              ·
                refine ⟨343856466168136082253845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229237644112090721502563 343856466168136082253845)
                ·
                  refine ⟨16118271851631378855649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 343856466168136082253845 16118271851631378855649)
                  ·
                    refine ⟨12088703888723534141737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16118271851631378855649 12088703888723534141737)
                    ·
                      refine ⟨9066527916542650606303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12088703888723534141737 9066527916542650606303)
                      ·
                        rfl

theorem cell23_17657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_17657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17657 prefixEnd_17657 := by exact prefixLift 17657
  have htrace : WordTrace (prefixWord ++ tailWord_17657) baseStart_17657 baseEnd_17657 := by
    simpa [prefixWord, tailWord_17657, baseEnd_17657] using wordTrace_append hprefix tailTrace_17657
  have hstable : (prefixWord ++ tailWord_17657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17657).length < 2 ^ (prefixWord ++ tailWord_17657).sum := by decide
  have hdescent : baseEnd_17657 < baseStart_17657 := by decide
  rcases family_descends (prefixWord ++ tailWord_17657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17673 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_17673 : Nat := 118140960795 + 17673 * 2 ^ 59
def prefixEnd_17673 : Nat := 4983230072969 + 3 ^ 40 * 17673 * 2
def baseEnd_17673 : Nat := 9074743607014588006229

theorem tailTrace_17673 : CollatzResearch.WordTrace tailWord_17673 prefixEnd_17673 9074743607014588006229 := by
  unfold tailWord_17673
  simp only [CollatzResearch.WordTrace]
  refine ⟨644587264981214153209673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 429724843320809435473115 644587264981214153209673)
  ·
    refine ⟨483440448735910614907255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 644587264981214153209673 483440448735910614907255)
    ·
      refine ⟨725160673103865922360883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483440448735910614907255 725160673103865922360883)
      ·
        refine ⟨1087741009655798883541325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725160673103865922360883 1087741009655798883541325)
        ·
          refine ⟨407902878620924581327997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1087741009655798883541325 407902878620924581327997)
          ·
            refine ⟨152963579482846717997999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 407902878620924581327997 152963579482846717997999)
            ·
              refine ⟨229445369224270076996999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152963579482846717997999 229445369224270076996999)
              ·
                refine ⟨344168053836405115495499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229445369224270076996999 344168053836405115495499)
                ·
                  refine ⟨516252080754607673243249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344168053836405115495499 516252080754607673243249)
                  ·
                    refine ⟨387189060565955754932437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 516252080754607673243249 387189060565955754932437)
                    ·
                      refine ⟨9074743607014588006229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 387189060565955754932437 9074743607014588006229)
                      ·
                        rfl

theorem cell23_17673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_17673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17673 prefixEnd_17673 := by exact prefixLift 17673
  have htrace : WordTrace (prefixWord ++ tailWord_17673) baseStart_17673 baseEnd_17673 := by
    simpa [prefixWord, tailWord_17673, baseEnd_17673] using wordTrace_append hprefix tailTrace_17673
  have hstable : (prefixWord ++ tailWord_17673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17673).length < 2 ^ (prefixWord ++ tailWord_17673).sum := by decide
  have hdescent : baseEnd_17673 < baseStart_17673 := by decide
  rcases family_descends (prefixWord ++ tailWord_17673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17674 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2]
def baseStart_17674 : Nat := 118140960795 + 17674 * 2 ^ 59
def prefixEnd_17674 : Nat := 4983230072969 + 3 ^ 40 * 17674 * 2
def baseEnd_17674 : Nat := 9075257087669084093725

theorem tailTrace_17674 : CollatzResearch.WordTrace tailWord_17674 prefixEnd_17674 9075257087669084093725 := by
  unfold tailWord_17674
  simp only [CollatzResearch.WordTrace]
  refine ⟨161155934494397830999019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 429749158651727549330717 161155934494397830999019)
  ·
    refine ⟨241733901741596746498529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161155934494397830999019 241733901741596746498529)
    ·
      refine ⟨181300426306197559873897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241733901741596746498529 181300426306197559873897)
      ·
        refine ⟨135975319729648169905423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181300426306197559873897 135975319729648169905423)
        ·
          refine ⟨203962979594472254858135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135975319729648169905423 203962979594472254858135)
          ·
            refine ⟨305944469391708382287203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203962979594472254858135 305944469391708382287203)
            ·
              refine ⟨458916704087562573430805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305944469391708382287203 458916704087562573430805)
              ·
                refine ⟨21511720504104495629569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 458916704087562573430805 21511720504104495629569)
                ·
                  refine ⟨16133790378078371722177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21511720504104495629569 16133790378078371722177)
                  ·
                    refine ⟨12100342783558778791633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16133790378078371722177 12100342783558778791633)
                    ·
                      refine ⟨9075257087669084093725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12100342783558778791633 9075257087669084093725)
                      ·
                        rfl

theorem cell23_17674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_17674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17674 prefixEnd_17674 := by exact prefixLift 17674
  have htrace : WordTrace (prefixWord ++ tailWord_17674) baseStart_17674 baseEnd_17674 := by
    simpa [prefixWord, tailWord_17674, baseEnd_17674] using wordTrace_append hprefix tailTrace_17674
  have hstable : (prefixWord ++ tailWord_17674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17674).length < 2 ^ (prefixWord ++ tailWord_17674).sum := by decide
  have hdescent : baseEnd_17674 < baseStart_17674 := by decide
  rcases family_descends (prefixWord ++ tailWord_17674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17723 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 6, 8]
def baseStart_17723 : Nat := 118140960795 + 17723 * 2 ^ 59
def prefixEnd_17723 : Nat := 4983230072969 + 3 ^ 40 * 17723 * 2
def baseEnd_17723 : Nat := 3033472546579797460333

theorem tailTrace_17723 : CollatzResearch.WordTrace tailWord_17723 prefixEnd_17723 3033472546579797460333 := by
  unfold tailWord_17723
  simp only [CollatzResearch.WordTrace]
  refine ⟨646410914800072692529823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 430940609866715128353215 646410914800072692529823)
  ·
    refine ⟨969616372200109038794735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 646410914800072692529823 969616372200109038794735)
    ·
      refine ⟨1454424558300163558192103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 969616372200109038794735 1454424558300163558192103)
      ·
        refine ⟨2181636837450245337288155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454424558300163558192103 2181636837450245337288155)
        ·
          refine ⟨3272455256175368005932233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2181636837450245337288155 3272455256175368005932233)
          ·
            refine ⟨2454341442131526004449175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3272455256175368005932233 2454341442131526004449175)
            ·
              refine ⟨3681512163197289006673763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2454341442131526004449175 3681512163197289006673763)
              ·
                refine ⟨5522268244795933510010645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3681512163197289006673763 5522268244795933510010645)
                ·
                  refine ⟨258856323974809383281749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5522268244795933510010645 258856323974809383281749)
                  ·
                    refine ⟨3033472546579797460333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 258856323974809383281749 3033472546579797460333)
                    ·
                      rfl

theorem cell23_17723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 8].length) (baseStart_17723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17723 prefixEnd_17723 := by exact prefixLift 17723
  have htrace : WordTrace (prefixWord ++ tailWord_17723) baseStart_17723 baseEnd_17723 := by
    simpa [prefixWord, tailWord_17723, baseEnd_17723] using wordTrace_append hprefix tailTrace_17723
  have hstable : (prefixWord ++ tailWord_17723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17723).length < 2 ^ (prefixWord ++ tailWord_17723).sum := by decide
  have hdescent : baseEnd_17723 < baseStart_17723 := by decide
  rcases family_descends (prefixWord ++ tailWord_17723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17741 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_17741 : Nat := 118140960795 + 17741 * 2 ^ 59
def prefixEnd_17741 : Nat := 4983230072969 + 3 ^ 40 * 17741 * 2
def baseEnd_17741 : Nat := 9109660291520321955917

theorem tailTrace_17741 : CollatzResearch.WordTrace tailWord_17741 prefixEnd_17741 9109660291520321955917 := by
  unfold tailWord_17741
  simp only [CollatzResearch.WordTrace]
  refine ⟨647067428734861766685077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 431378285823241177790051 647067428734861766685077)
  ·
    refine ⟨30331285721946645313363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 647067428734861766685077 30331285721946645313363)
    ·
      refine ⟨45496928582919967970045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30331285721946645313363 45496928582919967970045)
      ·
        refine ⟨17061348218594987988767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45496928582919967970045 17061348218594987988767)
        ·
          refine ⟨25592022327892481983151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17061348218594987988767 25592022327892481983151)
          ·
            refine ⟨38388033491838722974727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25592022327892481983151 38388033491838722974727)
            ·
              refine ⟨57582050237758084462091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38388033491838722974727 57582050237758084462091)
              ·
                refine ⟨86373075356637126693137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57582050237758084462091 86373075356637126693137)
                ·
                  refine ⟨64779806517477845019853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86373075356637126693137 64779806517477845019853)
                  ·
                    refine ⟨24292427444054191882445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64779806517477845019853 24292427444054191882445)
                    ·
                      refine ⟨9109660291520321955917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 24292427444054191882445 9109660291520321955917)
                      ·
                        rfl

theorem cell23_17741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_17741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17741 prefixEnd_17741 := by exact prefixLift 17741
  have htrace : WordTrace (prefixWord ++ tailWord_17741) baseStart_17741 baseEnd_17741 := by
    simpa [prefixWord, tailWord_17741, baseEnd_17741] using wordTrace_append hprefix tailTrace_17741
  have hstable : (prefixWord ++ tailWord_17741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17741).length < 2 ^ (prefixWord ++ tailWord_17741).sum := by decide
  have hdescent : baseEnd_17741 < baseStart_17741 := by decide
  rcases family_descends (prefixWord ++ tailWord_17741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17747 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 2, 4, 2]
def baseStart_17747 : Nat := 118140960795 + 17747 * 2 ^ 59
def prefixEnd_17747 : Nat := 4983230072969 + 3 ^ 40 * 17747 * 2
def baseEnd_17747 : Nat := 9112741175447298480889

theorem tailTrace_17747 : CollatzResearch.WordTrace tailWord_17747 prefixEnd_17747 9112741175447298480889 := by
  unfold tailWord_17747
  simp only [CollatzResearch.WordTrace]
  refine ⟨647286266713124791403495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 431524177808749860935663 647286266713124791403495)
  ·
    refine ⟨970929400069687187105243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 647286266713124791403495 970929400069687187105243)
    ·
      refine ⟨1456394100104530780657865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 970929400069687187105243 1456394100104530780657865)
      ·
        refine ⟨1092295575078398085493399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1456394100104530780657865 1092295575078398085493399)
        ·
          refine ⟨1638443362617597128240099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092295575078398085493399 1638443362617597128240099)
          ·
            refine ⟨2457665043926395692360149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638443362617597128240099 2457665043926395692360149)
            ·
              refine ⟨57601524467024899039691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2457665043926395692360149 57601524467024899039691)
              ·
                refine ⟨86402286700537348559537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57601524467024899039691 86402286700537348559537)
                ·
                  refine ⟨64801715025403011419653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86402286700537348559537 64801715025403011419653)
                  ·
                    refine ⟨12150321567263064641185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64801715025403011419653 12150321567263064641185)
                    ·
                      refine ⟨9112741175447298480889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12150321567263064641185 9112741175447298480889)
                      ·
                        rfl

theorem cell23_17747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 4, 2].length) (baseStart_17747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17747 prefixEnd_17747 := by exact prefixLift 17747
  have htrace : WordTrace (prefixWord ++ tailWord_17747) baseStart_17747 baseEnd_17747 := by
    simpa [prefixWord, tailWord_17747, baseEnd_17747] using wordTrace_append hprefix tailTrace_17747
  have hstable : (prefixWord ++ tailWord_17747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17747).length < 2 ^ (prefixWord ++ tailWord_17747).sum := by decide
  have hdescent : baseEnd_17747 < baseStart_17747 := by decide
  rcases family_descends (prefixWord ++ tailWord_17747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17764 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_17764 : Nat := 118140960795 + 17764 * 2 ^ 59
def prefixEnd_17764 : Nat := 4983230072969 + 3 ^ 40 * 17764 * 2
def baseEnd_17764 : Nat := 9121470346573731968311

theorem tailTrace_17764 : CollatzResearch.WordTrace tailWord_17764 prefixEnd_17764 9121470346573731968311 := by
  unfold tailWord_17764
  simp only [CollatzResearch.WordTrace]
  refine ⟨323953153825768347386173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 431937538434357796514897 323953153825768347386173)
  ·
    refine ⟨121482432684663130269815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 323953153825768347386173 121482432684663130269815)
    ·
      refine ⟨182223649026994695404723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121482432684663130269815 182223649026994695404723)
      ·
        refine ⟨273335473540492043107085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182223649026994695404723 273335473540492043107085)
        ·
          refine ⟨102500802577684516165157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273335473540492043107085 102500802577684516165157)
          ·
            refine ⟨19218900483315846780967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102500802577684516165157 19218900483315846780967)
            ·
              refine ⟨28828350724973770171451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19218900483315846780967 28828350724973770171451)
              ·
                refine ⟨43242526087460655257177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28828350724973770171451 43242526087460655257177)
                ·
                  refine ⟨32431894565595491442883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43242526087460655257177 32431894565595491442883)
                  ·
                    refine ⟨48647841848393237164325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32431894565595491442883 48647841848393237164325)
                    ·
                      refine ⟨9121470346573731968311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 48647841848393237164325 9121470346573731968311)
                      ·
                        rfl

theorem cell23_17764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_17764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17764 prefixEnd_17764 := by exact prefixLift 17764
  have htrace : WordTrace (prefixWord ++ tailWord_17764) baseStart_17764 baseEnd_17764 := by
    simpa [prefixWord, tailWord_17764, baseEnd_17764] using wordTrace_append hprefix tailTrace_17764
  have hstable : (prefixWord ++ tailWord_17764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17764).length < 2 ^ (prefixWord ++ tailWord_17764).sum := by decide
  have hdescent : baseEnd_17764 < baseStart_17764 := by decide
  rcases family_descends (prefixWord ++ tailWord_17764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17817 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 1, 5]
def baseStart_17817 : Nat := 118140960795 + 17817 * 2 ^ 59
def prefixEnd_17817 : Nat := 4983230072969 + 3 ^ 40 * 17817 * 2
def baseEnd_17817 : Nat := 3049561607087341535189

theorem tailTrace_17817 : CollatzResearch.WordTrace tailWord_17817 prefixEnd_17817 3049561607087341535189 := by
  unfold tailWord_17817
  simp only [CollatzResearch.WordTrace]
  refine ⟨649839376459526746451705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 433226250973017830967803 649839376459526746451705)
  ·
    refine ⟨487379532344645059838779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 649839376459526746451705 487379532344645059838779)
    ·
      refine ⟨731069298516967589758169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 487379532344645059838779 731069298516967589758169)
      ·
        refine ⟨548301973887725692318627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 731069298516967589758169 548301973887725692318627)
        ·
          refine ⟨822452960831588538477941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548301973887725692318627 822452960831588538477941)
          ·
            refine ⟨77104965077961425482307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 822452960831588538477941 77104965077961425482307)
            ·
              refine ⟨115657447616942138223461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77104965077961425482307 115657447616942138223461)
              ·
                refine ⟨21685771428176650916899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115657447616942138223461 21685771428176650916899)
                ·
                  refine ⟨32528657142264976375349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21685771428176650916899 32528657142264976375349)
                  ·
                    refine ⟨3049561607087341535189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32528657142264976375349 3049561607087341535189)
                    ·
                      rfl

theorem cell23_17817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 5].length) (baseStart_17817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17817 prefixEnd_17817 := by exact prefixLift 17817
  have htrace : WordTrace (prefixWord ++ tailWord_17817) baseStart_17817 baseEnd_17817 := by
    simpa [prefixWord, tailWord_17817, baseEnd_17817] using wordTrace_append hprefix tailTrace_17817
  have hstable : (prefixWord ++ tailWord_17817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17817).length < 2 ^ (prefixWord ++ tailWord_17817).sum := by decide
  have hdescent : baseEnd_17817 < baseStart_17817 := by decide
  rcases family_descends (prefixWord ++ tailWord_17817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17824 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 2, 3, 2]
def baseStart_17824 : Nat := 118140960795 + 17824 * 2 ^ 59
def prefixEnd_17824 : Nat := 4983230072969 + 3 ^ 40 * 17824 * 2
def baseEnd_17824 : Nat := 9152279185843497218035

theorem tailTrace_17824 : CollatzResearch.WordTrace tailWord_17824 prefixEnd_17824 9152279185843497218035 := by
  unfold tailWord_17824
  simp only [CollatzResearch.WordTrace]
  refine ⟨325047343717083470978263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 433396458289444627971017 325047343717083470978263)
  ·
    refine ⟨487571015575625206467395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 325047343717083470978263 487571015575625206467395)
    ·
      refine ⟨731356523363437809701093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 487571015575625206467395 731356523363437809701093)
      ·
        refine ⟨137129348130644589318955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 731356523363437809701093 137129348130644589318955)
        ·
          refine ⟨205694022195966883978433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137129348130644589318955 205694022195966883978433)
          ·
            refine ⟨154270516646975162983825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205694022195966883978433 154270516646975162983825)
            ·
              refine ⟨115702887485231372237869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154270516646975162983825 115702887485231372237869)
              ·
                refine ⟨43388582806961764589201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115702887485231372237869 43388582806961764589201)
                ·
                  refine ⟨32541437105221323441901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43388582806961764589201 32541437105221323441901)
                  ·
                    refine ⟨12203038914457996290713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32541437105221323441901 12203038914457996290713)
                    ·
                      refine ⟨9152279185843497218035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12203038914457996290713 9152279185843497218035)
                      ·
                        rfl

theorem cell23_17824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_17824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17824 prefixEnd_17824 := by exact prefixLift 17824
  have htrace : WordTrace (prefixWord ++ tailWord_17824) baseStart_17824 baseEnd_17824 := by
    simpa [prefixWord, tailWord_17824, baseEnd_17824] using wordTrace_append hprefix tailTrace_17824
  have hstable : (prefixWord ++ tailWord_17824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17824).length < 2 ^ (prefixWord ++ tailWord_17824).sum := by decide
  have hdescent : baseEnd_17824 < baseStart_17824 := by decide
  rcases family_descends (prefixWord ++ tailWord_17824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17847 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 4, 4]
def baseStart_17847 : Nat := 118140960795 + 17847 * 2 ^ 59
def prefixEnd_17847 : Nat := 4983230072969 + 3 ^ 40 * 17847 * 2
def baseEnd_17847 : Nat := 3054696413632302410143

theorem tailTrace_17847 : CollatzResearch.WordTrace tailWord_17847 prefixEnd_17847 3054696413632302410143 := by
  unfold tailWord_17847
  simp only [CollatzResearch.WordTrace]
  refine ⟨650933566350841870043795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 433955710900561246695863 650933566350841870043795)
  ·
    refine ⟨976400349526262805065693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 650933566350841870043795 976400349526262805065693)
    ·
      refine ⟨366150131072348551899635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 976400349526262805065693 366150131072348551899635)
      ·
        refine ⟨549225196608522827849453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366150131072348551899635 549225196608522827849453)
        ·
          refine ⟨205959448728196060443545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 549225196608522827849453 205959448728196060443545)
          ·
            refine ⟨154469586546147045332659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205959448728196060443545 154469586546147045332659)
            ·
              refine ⟨231704379819220567998989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154469586546147045332659 231704379819220567998989)
              ·
                refine ⟨86889142432207712999621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231704379819220567998989 86889142432207712999621)
                ·
                  refine ⟨16291714206038946187429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86889142432207712999621 16291714206038946187429)
                  ·
                    refine ⟨3054696413632302410143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16291714206038946187429 3054696413632302410143)
                    ·
                      rfl

theorem cell23_17847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_17847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17847 prefixEnd_17847 := by exact prefixLift 17847
  have htrace : WordTrace (prefixWord ++ tailWord_17847) baseStart_17847 baseEnd_17847 := by
    simpa [prefixWord, tailWord_17847, baseEnd_17847] using wordTrace_append hprefix tailTrace_17847
  have hstable : (prefixWord ++ tailWord_17847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17847).length < 2 ^ (prefixWord ++ tailWord_17847).sum := by decide
  have hdescent : baseEnd_17847 < baseStart_17847 := by decide
  rcases family_descends (prefixWord ++ tailWord_17847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17864 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 2, 4]
def baseStart_17864 : Nat := 118140960795 + 17864 * 2 ^ 59
def prefixEnd_17864 : Nat := 4983230072969 + 3 ^ 40 * 17864 * 2
def baseEnd_17864 : Nat := 3057606137341113572617

theorem tailTrace_17864 : CollatzResearch.WordTrace tailWord_17864 prefixEnd_17864 3057606137341113572617 := by
  unfold tailWord_17864
  simp only [CollatzResearch.WordTrace]
  refine ⟨325776803644626886706323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 434369071526169182275097 325776803644626886706323)
  ·
    refine ⟨488665205466940330059485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 325776803644626886706323 488665205466940330059485)
    ·
      refine ⟨183249452050102623772307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 488665205466940330059485 183249452050102623772307)
      ·
        refine ⟨274874178075153935658461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183249452050102623772307 274874178075153935658461)
        ·
          refine ⟨103077816778182725871923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274874178075153935658461 103077816778182725871923)
          ·
            refine ⟨154616725167274088807885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103077816778182725871923 154616725167274088807885)
            ·
              refine ⟨57981271937727783302957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154616725167274088807885 57981271937727783302957)
              ·
                refine ⟨21742976976647918738609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57981271937727783302957 21742976976647918738609)
                ·
                  refine ⟨16307232732485939053957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21742976976647918738609 16307232732485939053957)
                  ·
                    refine ⟨3057606137341113572617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16307232732485939053957 3057606137341113572617)
                    ·
                      rfl

theorem cell23_17864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_17864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17864 prefixEnd_17864 := by exact prefixLift 17864
  have htrace : WordTrace (prefixWord ++ tailWord_17864) baseStart_17864 baseEnd_17864 := by
    simpa [prefixWord, tailWord_17864, baseEnd_17864] using wordTrace_append hprefix tailTrace_17864
  have hstable : (prefixWord ++ tailWord_17864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17864).length < 2 ^ (prefixWord ++ tailWord_17864).sum := by decide
  have hdescent : baseEnd_17864 < baseStart_17864 := by decide
  rcases family_descends (prefixWord ++ tailWord_17864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17905 : List Nat := [1, 2, 2, 2, 3, 2, 4, 2, 1, 2, 2]
def baseStart_17905 : Nat := 118140960795 + 17905 * 2 ^ 59
def prefixEnd_17905 : Nat := 4983230072969 + 3 ^ 40 * 17905 * 2
def baseEnd_17905 : Nat := 9193871118857680305163

theorem tailTrace_17905 : CollatzResearch.WordTrace tailWord_17905 prefixEnd_17905 9193871118857680305163 := by
  unfold tailWord_17905
  simp only [CollatzResearch.WordTrace]
  refine ⟨653049000140717775655169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 435366000093811850436779 653049000140717775655169)
  ·
    refine ⟨489786750105538331741377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 653049000140717775655169 489786750105538331741377)
    ·
      refine ⟨367340062579153748806033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 489786750105538331741377 367340062579153748806033)
      ·
        refine ⟨275505046934365311604525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367340062579153748806033 275505046934365311604525)
        ·
          refine ⟨103314392600386991851697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275505046934365311604525 103314392600386991851697)
          ·
            refine ⟨77485794450290243888773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103314392600386991851697 77485794450290243888773)
            ·
              refine ⟨14528586459429420729145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77485794450290243888773 14528586459429420729145)
              ·
                refine ⟨10896439844572065546859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14528586459429420729145 10896439844572065546859)
                ·
                  refine ⟨16344659766858098320289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10896439844572065546859 16344659766858098320289)
                  ·
                    refine ⟨12258494825143573740217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16344659766858098320289 12258494825143573740217)
                    ·
                      refine ⟨9193871118857680305163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12258494825143573740217 9193871118857680305163)
                      ·
                        rfl

theorem cell23_17905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_17905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17905 prefixEnd_17905 := by exact prefixLift 17905
  have htrace : WordTrace (prefixWord ++ tailWord_17905) baseStart_17905 baseEnd_17905 := by
    simpa [prefixWord, tailWord_17905, baseEnd_17905] using wordTrace_append hprefix tailTrace_17905
  have hstable : (prefixWord ++ tailWord_17905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17905).length < 2 ^ (prefixWord ++ tailWord_17905).sum := by decide
  have hdescent : baseEnd_17905 < baseStart_17905 := by decide
  rcases family_descends (prefixWord ++ tailWord_17905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17914 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2]
def baseStart_17914 : Nat := 118140960795 + 17914 * 2 ^ 59
def prefixEnd_17914 : Nat := 4983230072969 + 3 ^ 40 * 17914 * 2
def baseEnd_17914 : Nat := 9198492444748145092621

theorem tailTrace_17914 : CollatzResearch.WordTrace tailWord_17914 prefixEnd_17914 9198492444748145092621 := by
  unfold tailWord_17914
  simp only [CollatzResearch.WordTrace]
  refine ⟨163344314277028078183199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 435584838072074875155197 163344314277028078183199)
  ·
    refine ⟨245016471415542117274799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163344314277028078183199 245016471415542117274799)
    ·
      refine ⟨367524707123313175912199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245016471415542117274799 367524707123313175912199)
      ·
        refine ⟨551287060684969763868299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367524707123313175912199 551287060684969763868299)
        ·
          refine ⟨826930591027454645802449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551287060684969763868299 826930591027454645802449)
          ·
            refine ⟨620197943270590984351837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826930591027454645802449 620197943270590984351837)
            ·
              refine ⟨232574228726471619131939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 620197943270590984351837 232574228726471619131939)
              ·
                refine ⟨348861343089707428697909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232574228726471619131939 348861343089707428697909)
                ·
                  refine ⟨32705750914660071440429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 348861343089707428697909 32705750914660071440429)
                  ·
                    refine ⟨12264656592997526790161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32705750914660071440429 12264656592997526790161)
                    ·
                      refine ⟨9198492444748145092621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12264656592997526790161 9198492444748145092621)
                      ·
                        rfl

theorem cell23_17914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2].length) (baseStart_17914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17914 prefixEnd_17914 := by exact prefixLift 17914
  have htrace : WordTrace (prefixWord ++ tailWord_17914) baseStart_17914 baseEnd_17914 := by
    simpa [prefixWord, tailWord_17914, baseEnd_17914] using wordTrace_append hprefix tailTrace_17914
  have hstable : (prefixWord ++ tailWord_17914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17914).length < 2 ^ (prefixWord ++ tailWord_17914).sum := by decide
  have hdescent : baseEnd_17914 < baseStart_17914 := by decide
  rcases family_descends (prefixWord ++ tailWord_17914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17918 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_17918 : Nat := 118140960795 + 17918 * 2 ^ 59
def prefixEnd_17918 : Nat := 4983230072969 + 3 ^ 40 * 17918 * 2
def baseEnd_17918 : Nat := 9200546367366129442603

theorem tailTrace_17918 : CollatzResearch.WordTrace tailWord_17918 prefixEnd_17918 9200546367366129442603 := by
  unfold tailWord_17918
  simp only [CollatzResearch.WordTrace]
  refine ⟨81690393636702624484801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 435682099395747330585605 81690393636702624484801)
  ·
    refine ⟨61267795227526968363601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81690393636702624484801 61267795227526968363601)
    ·
      refine ⟨45950846420645226272701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61267795227526968363601 45950846420645226272701)
      ·
        refine ⟨17231567407741959852263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45950846420645226272701 17231567407741959852263)
        ·
          refine ⟨25847351111612939778395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17231567407741959852263 25847351111612939778395)
          ·
            refine ⟨38771026667419409667593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25847351111612939778395 38771026667419409667593)
            ·
              refine ⟨29078270000564557250695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38771026667419409667593 29078270000564557250695)
              ·
                refine ⟨43617405000846835876043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29078270000564557250695 43617405000846835876043)
                ·
                  refine ⟨65426107501270253814065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43617405000846835876043 65426107501270253814065)
                  ·
                    refine ⟨49069580625952690360549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65426107501270253814065 49069580625952690360549)
                    ·
                      refine ⟨9200546367366129442603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 49069580625952690360549 9200546367366129442603)
                      ·
                        rfl

theorem cell23_17918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_17918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17918 prefixEnd_17918 := by exact prefixLift 17918
  have htrace : WordTrace (prefixWord ++ tailWord_17918) baseStart_17918 baseEnd_17918 := by
    simpa [prefixWord, tailWord_17918, baseEnd_17918] using wordTrace_append hprefix tailTrace_17918
  have hstable : (prefixWord ++ tailWord_17918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17918).length < 2 ^ (prefixWord ++ tailWord_17918).sum := by decide
  have hdescent : baseEnd_17918 < baseStart_17918 := by decide
  rcases family_descends (prefixWord ++ tailWord_17918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17921 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_17921 : Nat := 118140960795 + 17921 * 2 ^ 59
def prefixEnd_17921 : Nat := 4983230072969 + 3 ^ 40 * 17921 * 2
def baseEnd_17921 : Nat := 9202086809329617705089

theorem tailTrace_17921 : CollatzResearch.WordTrace tailWord_17921 prefixEnd_17921 9202086809329617705089 := by
  unfold tailWord_17921
  simp only [CollatzResearch.WordTrace]
  refine ⟨653632568082752508237617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 435755045388501672158411 653632568082752508237617)
  ·
    refine ⟨490224426062064381178213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 653632568082752508237617 490224426062064381178213)
    ·
      refine ⟨91917079886637071470915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 490224426062064381178213 91917079886637071470915)
      ·
        refine ⟨137875619829955607206373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91917079886637071470915 137875619829955607206373)
        ·
          refine ⟨25851678718116676351195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137875619829955607206373 25851678718116676351195)
          ·
            refine ⟨38777518077175014526793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25851678718116676351195 38777518077175014526793)
            ·
              refine ⟨29083138557881260895095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38777518077175014526793 29083138557881260895095)
              ·
                refine ⟨43624707836821891342643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29083138557881260895095 43624707836821891342643)
                ·
                  refine ⟨65437061755232837013965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43624707836821891342643 65437061755232837013965)
                  ·
                    refine ⟨24538898158212313880237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65437061755232837013965 24538898158212313880237)
                    ·
                      refine ⟨9202086809329617705089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 24538898158212313880237 9202086809329617705089)
                      ·
                        rfl

theorem cell23_17921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_17921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17921 prefixEnd_17921 := by exact prefixLift 17921
  have htrace : WordTrace (prefixWord ++ tailWord_17921) baseStart_17921 baseEnd_17921 := by
    simpa [prefixWord, tailWord_17921, baseEnd_17921] using wordTrace_append hprefix tailTrace_17921
  have hstable : (prefixWord ++ tailWord_17921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17921).length < 2 ^ (prefixWord ++ tailWord_17921).sum := by decide
  have hdescent : baseEnd_17921 < baseStart_17921 := by decide
  rcases family_descends (prefixWord ++ tailWord_17921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17955 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 2, 1, 3]
def baseStart_17955 : Nat := 118140960795 + 17955 * 2 ^ 59
def prefixEnd_17955 : Nat := 4983230072969 + 3 ^ 40 * 17955 * 2
def baseEnd_17955 : Nat := 9219545151582484679933

theorem tailTrace_17955 : CollatzResearch.WordTrace tailWord_17955 prefixEnd_17955 9219545151582484679933 := by
  unfold tailWord_17955
  simp only [CollatzResearch.WordTrace]
  refine ⟨654872649959576314975319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 436581766639717543316879 654872649959576314975319)
  ·
    refine ⟨982308974939364472462979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 654872649959576314975319 982308974939364472462979)
    ·
      refine ⟨1473463462409046708694469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982308974939364472462979 1473463462409046708694469)
      ·
        refine ⟨276274399201696257880213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1473463462409046708694469 276274399201696257880213)
        ·
          refine ⟨12950362462579512088135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 276274399201696257880213 12950362462579512088135)
          ·
            refine ⟨19425543693869268132203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12950362462579512088135 19425543693869268132203)
            ·
              refine ⟨29138315540803902198305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19425543693869268132203 29138315540803902198305)
              ·
                refine ⟨21853736655602926648729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29138315540803902198305 21853736655602926648729)
                ·
                  refine ⟨16390302491702194986547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21853736655602926648729 16390302491702194986547)
                  ·
                    refine ⟨24585453737553292479821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16390302491702194986547 24585453737553292479821)
                    ·
                      refine ⟨9219545151582484679933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 24585453737553292479821 9219545151582484679933)
                      ·
                        rfl

theorem cell23_17955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_17955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17955 prefixEnd_17955 := by exact prefixLift 17955
  have htrace : WordTrace (prefixWord ++ tailWord_17955) baseStart_17955 baseEnd_17955 := by
    simpa [prefixWord, tailWord_17955, baseEnd_17955] using wordTrace_append hprefix tailTrace_17955
  have hstable : (prefixWord ++ tailWord_17955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17955).length < 2 ^ (prefixWord ++ tailWord_17955).sum := by decide
  have hdescent : baseEnd_17955 < baseStart_17955 := by decide
  rcases family_descends (prefixWord ++ tailWord_17955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18024 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_18024 : Nat := 118140960795 + 18024 * 2 ^ 59
def prefixEnd_18024 : Nat := 4983230072969 + 3 ^ 40 * 18024 * 2
def baseEnd_18024 : Nat := 9254975316742714717115

theorem tailTrace_18024 : CollatzResearch.WordTrace tailWord_18024 prefixEnd_18024 9254975316742714717115 := by
  unfold tailWord_18024
  simp only [CollatzResearch.WordTrace]
  refine ⟨328694643354800549618563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 438259524473067399491417 328694643354800549618563)
  ·
    refine ⟨493041965032200824427845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328694643354800549618563 493041965032200824427845)
    ·
      refine ⟨92445368443537654580221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 493041965032200824427845 92445368443537654580221)
      ·
        refine ⟨34667013166326620467583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92445368443537654580221 34667013166326620467583)
        ·
          refine ⟨52000519749489930701375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34667013166326620467583 52000519749489930701375)
          ·
            refine ⟨78000779624234896052063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52000519749489930701375 78000779624234896052063)
            ·
              refine ⟨117001169436352344078095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78000779624234896052063 117001169436352344078095)
              ·
                refine ⟨175501754154528516117143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117001169436352344078095 175501754154528516117143)
                ·
                  refine ⟨263252631231792774175715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175501754154528516117143 263252631231792774175715)
                  ·
                    refine ⟨394878946847689161263573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 263252631231792774175715 394878946847689161263573)
                    ·
                      refine ⟨9254975316742714717115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 394878946847689161263573 9254975316742714717115)
                      ·
                        rfl

theorem cell23_18024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_18024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18024 prefixEnd_18024 := by exact prefixLift 18024
  have htrace : WordTrace (prefixWord ++ tailWord_18024) baseStart_18024 baseEnd_18024 := by
    simpa [prefixWord, tailWord_18024, baseEnd_18024] using wordTrace_append hprefix tailTrace_18024
  have hstable : (prefixWord ++ tailWord_18024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18024).length < 2 ^ (prefixWord ++ tailWord_18024).sum := by decide
  have hdescent : baseEnd_18024 < baseStart_18024 := by decide
  rcases family_descends (prefixWord ++ tailWord_18024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18029 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_18029 : Nat := 118140960795 + 18029 * 2 ^ 59
def prefixEnd_18029 : Nat := 4983230072969 + 3 ^ 40 * 18029 * 2
def baseEnd_18029 : Nat := 9257542720015195154593

theorem tailTrace_18029 : CollatzResearch.WordTrace tailWord_18029 prefixEnd_18029 9257542720015195154593 := by
  unfold tailWord_18029
  simp only [CollatzResearch.WordTrace]
  refine ⟨657571651691486953169141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 438381101127657968779427 657571651691486953169141)
  ·
    refine ⟨61647342346076901859607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 657571651691486953169141 61647342346076901859607)
    ·
      refine ⟨92471013519115352789411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61647342346076901859607 92471013519115352789411)
      ·
        refine ⟨138706520278673029184117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92471013519115352789411 138706520278673029184117)
        ·
          refine ⟨13003736276125596486011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138706520278673029184117 13003736276125596486011)
          ·
            refine ⟨19505604414188394729017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13003736276125596486011 19505604414188394729017)
            ·
              refine ⟨14629203310641296046763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19505604414188394729017 14629203310641296046763)
              ·
                refine ⟨21943804965961944070145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14629203310641296046763 21943804965961944070145)
                ·
                  refine ⟨16457853724471458052609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21943804965961944070145 16457853724471458052609)
                  ·
                    refine ⟨12343390293353593539457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16457853724471458052609 12343390293353593539457)
                    ·
                      refine ⟨9257542720015195154593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12343390293353593539457 9257542720015195154593)
                      ·
                        rfl

theorem cell23_18029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_18029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18029 prefixEnd_18029 := by exact prefixLift 18029
  have htrace : WordTrace (prefixWord ++ tailWord_18029) baseStart_18029 baseEnd_18029 := by
    simpa [prefixWord, tailWord_18029, baseEnd_18029] using wordTrace_append hprefix tailTrace_18029
  have hstable : (prefixWord ++ tailWord_18029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18029).length < 2 ^ (prefixWord ++ tailWord_18029).sum := by decide
  have hdescent : baseEnd_18029 < baseStart_18029 := by decide
  rcases family_descends (prefixWord ++ tailWord_18029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18044 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 5, 4]
def baseStart_18044 : Nat := 118140960795 + 18044 * 2 ^ 59
def prefixEnd_18044 : Nat := 4983230072969 + 3 ^ 40 * 18044 * 2
def baseEnd_18044 : Nat := 3088414976610878822341

theorem tailTrace_18044 : CollatzResearch.WordTrace tailWord_18044 prefixEnd_18044 3088414976610878822341 := by
  unfold tailWord_18044
  simp only [CollatzResearch.WordTrace]
  refine ⟨329059373318572257482593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 438745831091429676643457 329059373318572257482593)
  ·
    refine ⟨246794529988929193111945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 329059373318572257482593 246794529988929193111945)
    ·
      refine ⟨185095897491696894833959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246794529988929193111945 185095897491696894833959)
      ·
        refine ⟨277643846237545342250939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185095897491696894833959 277643846237545342250939)
        ·
          refine ⟨416465769356318013376409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277643846237545342250939 416465769356318013376409)
          ·
            refine ⟨312349327017238510032307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416465769356318013376409 312349327017238510032307)
            ·
              refine ⟨468523990525857765048461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312349327017238510032307 468523990525857765048461)
              ·
                refine ⟨175696496447196661893173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 468523990525857765048461 175696496447196661893173)
                ·
                  refine ⟨16471546541924687052485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 175696496447196661893173 16471546541924687052485)
                  ·
                    refine ⟨3088414976610878822341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16471546541924687052485 3088414976610878822341)
                    ·
                      rfl

theorem cell23_18044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_18044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18044 prefixEnd_18044 := by exact prefixLift 18044
  have htrace : WordTrace (prefixWord ++ tailWord_18044) baseStart_18044 baseEnd_18044 := by
    simpa [prefixWord, tailWord_18044, baseEnd_18044] using wordTrace_append hprefix tailTrace_18044
  have hstable : (prefixWord ++ tailWord_18044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18044).length < 2 ^ (prefixWord ++ tailWord_18044).sum := by decide
  have hdescent : baseEnd_18044 < baseStart_18044 := by decide
  rcases family_descends (prefixWord ++ tailWord_18044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18057 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 10]
def baseStart_18057 : Nat := 118140960795 + 18057 * 2 ^ 59
def prefixEnd_18057 : Nat := 4983230072969 + 3 ^ 40 * 18057 * 2
def baseEnd_18057 : Nat := 1030213353149009511607

theorem tailTrace_18057 : CollatzResearch.WordTrace tailWord_18057 prefixEnd_18057 1030213353149009511607 := by
  unfold tailWord_18057
  simp only [CollatzResearch.WordTrace]
  refine ⟨658592895590047735188425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 439061930393365156792283 658592895590047735188425)
  ·
    refine ⟨493944671692535801391319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 658592895590047735188425 493944671692535801391319)
    ·
      refine ⟨740917007538803702086979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 493944671692535801391319 740917007538803702086979)
      ·
        refine ⟨1111375511308205553130469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740917007538803702086979 1111375511308205553130469)
        ·
          refine ⟨208382908370288541211963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1111375511308205553130469 208382908370288541211963)
          ·
            refine ⟨312574362555432811817945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208382908370288541211963 312574362555432811817945)
            ·
              refine ⟨234430771916574608863459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312574362555432811817945 234430771916574608863459)
              ·
                refine ⟨351646157874861913295189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234430771916574608863459 351646157874861913295189)
                ·
                  refine ⟨1030213353149009511607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 351646157874861913295189 1030213353149009511607)
                  ·
                    rfl

theorem cell23_18057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 10].length) (baseStart_18057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18057 prefixEnd_18057 := by exact prefixLift 18057
  have htrace : WordTrace (prefixWord ++ tailWord_18057) baseStart_18057 baseEnd_18057 := by
    simpa [prefixWord, tailWord_18057, baseEnd_18057] using wordTrace_append hprefix tailTrace_18057
  have hstable : (prefixWord ++ tailWord_18057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18057).length < 2 ^ (prefixWord ++ tailWord_18057).sum := by decide
  have hdescent : baseEnd_18057 < baseStart_18057 := by decide
  rcases family_descends (prefixWord ++ tailWord_18057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18071 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 3]
def baseStart_18071 : Nat := 118140960795 + 18071 * 2 ^ 59
def prefixEnd_18071 : Nat := 4983230072969 + 3 ^ 40 * 18071 * 2
def baseEnd_18071 : Nat := 9279108907504030829399

theorem tailTrace_18071 : CollatzResearch.WordTrace tailWord_18071 prefixEnd_18071 9279108907504030829399 := by
  unfold tailWord_18071
  simp only [CollatzResearch.WordTrace]
  refine ⟨659103517539328126198067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 439402345026218750798711 659103517539328126198067)
  ·
    refine ⟨988655276308992189297101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 659103517539328126198067 988655276308992189297101)
    ·
      refine ⟨370745728615872070986413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 988655276308992189297101 370745728615872070986413)
      ·
        refine ⟨139029648230952026619905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 370745728615872070986413 139029648230952026619905)
        ·
          refine ⟨104272236173214019964929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139029648230952026619905 104272236173214019964929)
          ·
            refine ⟨78204177129910514973697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104272236173214019964929 78204177129910514973697)
            ·
              refine ⟨58653132847432886230273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78204177129910514973697 58653132847432886230273)
              ·
                refine ⟨43989849635574664672705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58653132847432886230273 43989849635574664672705)
                ·
                  refine ⟨32992387226680998504529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43989849635574664672705 32992387226680998504529)
                  ·
                    refine ⟨24744290420010748878397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32992387226680998504529 24744290420010748878397)
                    ·
                      refine ⟨9279108907504030829399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 24744290420010748878397 9279108907504030829399)
                      ·
                        rfl

theorem cell23_18071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_18071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18071 prefixEnd_18071 := by exact prefixLift 18071
  have htrace : WordTrace (prefixWord ++ tailWord_18071) baseStart_18071 baseEnd_18071 := by
    simpa [prefixWord, tailWord_18071, baseEnd_18071] using wordTrace_append hprefix tailTrace_18071
  have hstable : (prefixWord ++ tailWord_18071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18071).length < 2 ^ (prefixWord ++ tailWord_18071).sum := by decide
  have hdescent : baseEnd_18071 < baseStart_18071 := by decide
  rcases family_descends (prefixWord ++ tailWord_18071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18111 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 1, 5, 2]
def baseStart_18111 : Nat := 118140960795 + 18111 * 2 ^ 59
def prefixEnd_18111 : Nat := 4983230072969 + 3 ^ 40 * 18111 * 2
def baseEnd_18111 : Nat := 9299648133683874329215

theorem tailTrace_18111 : CollatzResearch.WordTrace tailWord_18111 prefixEnd_18111 9299648133683874329215 := by
  unfold tailWord_18111
  simp only [CollatzResearch.WordTrace]
  refine ⟨660562437394414957654187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 440374958262943305102791 660562437394414957654187)
  ·
    refine ⟨990843656091622436481281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 660562437394414957654187 990843656091622436481281)
    ·
      refine ⟨743132742068716827360961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 990843656091622436481281 743132742068716827360961)
      ·
        refine ⟨557349556551537620520721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 743132742068716827360961 557349556551537620520721)
        ·
          refine ⟨418012167413653215390541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557349556551537620520721 418012167413653215390541)
          ·
            refine ⟨156754562780119955771453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418012167413653215390541 156754562780119955771453)
            ·
              refine ⟨58782961042544983414295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156754562780119955771453 58782961042544983414295)
              ·
                refine ⟨88174441563817475121443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58782961042544983414295 88174441563817475121443)
                ·
                  refine ⟨132261662345726212682165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88174441563817475121443 132261662345726212682165)
                  ·
                    refine ⟨12399530844911832438953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 132261662345726212682165 12399530844911832438953)
                    ·
                      refine ⟨9299648133683874329215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12399530844911832438953 9299648133683874329215)
                      ·
                        rfl

theorem cell23_18111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 5, 2].length) (baseStart_18111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18111 prefixEnd_18111 := by exact prefixLift 18111
  have htrace : WordTrace (prefixWord ++ tailWord_18111) baseStart_18111 baseEnd_18111 := by
    simpa [prefixWord, tailWord_18111, baseEnd_18111] using wordTrace_append hprefix tailTrace_18111
  have hstable : (prefixWord ++ tailWord_18111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18111).length < 2 ^ (prefixWord ++ tailWord_18111).sum := by decide
  have hdescent : baseEnd_18111 < baseStart_18111 := by decide
  rcases family_descends (prefixWord ++ tailWord_18111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18125 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 6]
def baseStart_18125 : Nat := 118140960795 + 18125 * 2 ^ 59
def prefixEnd_18125 : Nat := 4983230072969 + 3 ^ 40 * 18125 * 2
def baseEnd_18125 : Nat := 1034092984760757728239

theorem tailTrace_18125 : CollatzResearch.WordTrace tailWord_18125 prefixEnd_18125 1034092984760757728239 := by
  unfold tailWord_18125
  simp only [CollatzResearch.WordTrace]
  refine ⟨661073059343695348663829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 440715372895796899109219 661073059343695348663829)
  ·
    refine ⟨30987799656735719468617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 661073059343695348663829 30987799656735719468617)
    ·
      refine ⟨23240849742551789601463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30987799656735719468617 23240849742551789601463)
      ·
        refine ⟨34861274613827684402195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23240849742551789601463 34861274613827684402195)
        ·
          refine ⟨52291911920741526603293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34861274613827684402195 52291911920741526603293)
          ·
            refine ⟨19609466970278072476235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52291911920741526603293 19609466970278072476235)
            ·
              refine ⟨29414200455417108714353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19609466970278072476235 29414200455417108714353)
              ·
                refine ⟨22060650341562831535765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29414200455417108714353 22060650341562831535765)
                ·
                  refine ⟨1034092984760757728239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22060650341562831535765 1034092984760757728239)
                  ·
                    rfl

theorem cell23_18125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_18125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18125 prefixEnd_18125 := by exact prefixLift 18125
  have htrace : WordTrace (prefixWord ++ tailWord_18125) baseStart_18125 baseEnd_18125 := by
    simpa [prefixWord, tailWord_18125, baseEnd_18125] using wordTrace_append hprefix tailTrace_18125
  have hstable : (prefixWord ++ tailWord_18125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18125).length < 2 ^ (prefixWord ++ tailWord_18125).sum := by decide
  have hdescent : baseEnd_18125 < baseStart_18125 := by decide
  rcases family_descends (prefixWord ++ tailWord_18125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18144 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 5]
def baseStart_18144 : Nat := 118140960795 + 18144 * 2 ^ 59
def prefixEnd_18144 : Nat := 4983230072969 + 3 ^ 40 * 18144 * 2
def baseEnd_18144 : Nat := 9316592995282245216563

theorem tailTrace_18144 : CollatzResearch.WordTrace tailWord_18144 prefixEnd_18144 9316592995282245216563 := by
  unfold tailWord_18144
  simp only [CollatzResearch.WordTrace]
  refine ⟨330883023137430796802743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 441177364183241062403657 330883023137430796802743)
  ·
    refine ⟨496324534706146195204115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 330883023137430796802743 496324534706146195204115)
    ·
      refine ⟨744486802059219292806173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 496324534706146195204115 744486802059219292806173)
      ·
        refine ⟨279182550772207234802315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 744486802059219292806173 279182550772207234802315)
        ·
          refine ⟨418773826158310852203473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279182550772207234802315 418773826158310852203473)
          ·
            refine ⟨314080369618733139152605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418773826158310852203473 314080369618733139152605)
            ·
              refine ⟨117780138607024927182227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314080369618733139152605 117780138607024927182227)
              ·
                refine ⟨176670207910537390773341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117780138607024927182227 176670207910537390773341)
                ·
                  refine ⟨66251327966451521540003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176670207910537390773341 66251327966451521540003)
                  ·
                    refine ⟨99376991949677282310005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66251327966451521540003 99376991949677282310005)
                    ·
                      refine ⟨9316592995282245216563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 99376991949677282310005 9316592995282245216563)
                      ·
                        rfl

theorem cell23_18144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_18144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18144 prefixEnd_18144 := by exact prefixLift 18144
  have htrace : WordTrace (prefixWord ++ tailWord_18144) baseStart_18144 baseEnd_18144 := by
    simpa [prefixWord, tailWord_18144, baseEnd_18144] using wordTrace_append hprefix tailTrace_18144
  have hstable : (prefixWord ++ tailWord_18144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18144).length < 2 ^ (prefixWord ++ tailWord_18144).sum := by decide
  have hdescent : baseEnd_18144 < baseStart_18144 := by decide
  rcases family_descends (prefixWord ++ tailWord_18144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18158 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_18158 : Nat := 118140960795 + 18158 * 2 ^ 59
def prefixEnd_18158 : Nat := 4983230072969 + 3 ^ 40 * 18158 * 2
def baseEnd_18158 : Nat := 9323781724445190441499

theorem tailTrace_18158 : CollatzResearch.WordTrace tailWord_18158 prefixEnd_18158 9323781724445190441499 := by
  unfold tailWord_18158
  simp only [CollatzResearch.WordTrace]
  refine ⟨82784583528017748076891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 441517778816094656410085 82784583528017748076891)
  ·
    refine ⟨124176875292026622115337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82784583528017748076891 124176875292026622115337)
    ·
      refine ⟨93132656469019966586503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124176875292026622115337 93132656469019966586503)
      ·
        refine ⟨139698984703529949879755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93132656469019966586503 139698984703529949879755)
        ·
          refine ⟨209548477055294924819633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139698984703529949879755 209548477055294924819633)
          ·
            refine ⟨157161357791471193614725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209548477055294924819633 157161357791471193614725)
            ·
              refine ⟨29467754585900848802761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157161357791471193614725 29467754585900848802761)
              ·
                refine ⟨22100815939425636602071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29467754585900848802761 22100815939425636602071)
                ·
                  refine ⟨33151223909138454903107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22100815939425636602071 33151223909138454903107)
                  ·
                    refine ⟨49726835863707682354661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33151223909138454903107 49726835863707682354661)
                    ·
                      refine ⟨9323781724445190441499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 49726835863707682354661 9323781724445190441499)
                      ·
                        rfl

theorem cell23_18158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_18158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18158 prefixEnd_18158 := by exact prefixLift 18158
  have htrace : WordTrace (prefixWord ++ tailWord_18158) baseStart_18158 baseEnd_18158 := by
    simpa [prefixWord, tailWord_18158, baseEnd_18158] using wordTrace_append hprefix tailTrace_18158
  have hstable : (prefixWord ++ tailWord_18158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18158).length < 2 ^ (prefixWord ++ tailWord_18158).sum := by decide
  have hdescent : baseEnd_18158 < baseStart_18158 := by decide
  rcases family_descends (prefixWord ++ tailWord_18158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18178 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_18178 : Nat := 118140960795 + 18178 * 2 ^ 59
def prefixEnd_18178 : Nat := 4983230072969 + 3 ^ 40 * 18178 * 2
def baseEnd_18178 : Nat := 9334051337535112191407

theorem tailTrace_18178 : CollatzResearch.WordTrace tailWord_18178 prefixEnd_18178 9334051337535112191407 := by
  unfold tailWord_18178
  simp only [CollatzResearch.WordTrace]
  refine ⟨165751532037921350085797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 442004085434456933562125 165751532037921350085797)
  ·
    refine ⟨31078412257110253141087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165751532037921350085797 31078412257110253141087)
    ·
      refine ⟨46617618385665379711631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31078412257110253141087 46617618385665379711631)
      ·
        refine ⟨69926427578498069567447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46617618385665379711631 69926427578498069567447)
        ·
          refine ⟨104889641367747104351171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69926427578498069567447 104889641367747104351171)
          ·
            refine ⟨157334462051620656526757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104889641367747104351171 157334462051620656526757)
            ·
              refine ⟨29500211634678873098767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157334462051620656526757 29500211634678873098767)
              ·
                refine ⟨44250317452018309648151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29500211634678873098767 44250317452018309648151)
                ·
                  refine ⟨66375476178027464472227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44250317452018309648151 66375476178027464472227)
                  ·
                    refine ⟨99563214267041196708341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66375476178027464472227 99563214267041196708341)
                    ·
                      refine ⟨9334051337535112191407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 99563214267041196708341 9334051337535112191407)
                      ·
                        rfl

theorem cell23_18178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_18178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18178 prefixEnd_18178 := by exact prefixLift 18178
  have htrace : WordTrace (prefixWord ++ tailWord_18178) baseStart_18178 baseEnd_18178 := by
    simpa [prefixWord, tailWord_18178, baseEnd_18178] using wordTrace_append hprefix tailTrace_18178
  have hstable : (prefixWord ++ tailWord_18178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18178).length < 2 ^ (prefixWord ++ tailWord_18178).sum := by decide
  have hdescent : baseEnd_18178 < baseStart_18178 := by decide
  rcases family_descends (prefixWord ++ tailWord_18178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18224 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 6, 6]
def baseStart_18224 : Nat := 118140960795 + 18224 * 2 ^ 59
def prefixEnd_18224 : Nat := 4983230072969 + 3 ^ 40 * 18224 * 2
def baseEnd_18224 : Nat := 3119223815880644072065

theorem tailTrace_18224 : CollatzResearch.WordTrace tailWord_18224 prefixEnd_18224 3119223815880644072065 := by
  unfold tailWord_18224
  simp only [CollatzResearch.WordTrace]
  refine ⟨332341942992517628258863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 443122590656690171011817 332341942992517628258863)
  ·
    refine ⟨498512914488776442388295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 332341942992517628258863 498512914488776442388295)
    ·
      refine ⟨747769371733164663582443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 498512914488776442388295 747769371733164663582443)
      ·
        refine ⟨1121654057599746995373665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 747769371733164663582443 1121654057599746995373665)
        ·
          refine ⟨841240543199810246530249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1121654057599746995373665 841240543199810246530249)
          ·
            refine ⟨630930407399857684897687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 841240543199810246530249 630930407399857684897687)
            ·
              refine ⟨946395611099786527346531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630930407399857684897687 946395611099786527346531)
              ·
                refine ⟨1419593416649679791019797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946395611099786527346531 1419593416649679791019797)
                ·
                  refine ⟨66543441405453740204053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1419593416649679791019797 66543441405453740204053)
                  ·
                    refine ⟨3119223815880644072065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66543441405453740204053 3119223815880644072065)
                    ·
                      rfl

theorem cell23_18224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_18224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18224 prefixEnd_18224 := by exact prefixLift 18224
  have htrace : WordTrace (prefixWord ++ tailWord_18224) baseStart_18224 baseEnd_18224 := by
    simpa [prefixWord, tailWord_18224, baseEnd_18224] using wordTrace_append hprefix tailTrace_18224
  have hstable : (prefixWord ++ tailWord_18224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18224).length < 2 ^ (prefixWord ++ tailWord_18224).sum := by decide
  have hdescent : baseEnd_18224 < baseStart_18224 := by decide
  rcases family_descends (prefixWord ++ tailWord_18224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18261 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_18261 : Nat := 118140960795 + 18261 * 2 ^ 59
def prefixEnd_18261 : Nat := 4983230072969 + 3 ^ 40 * 18261 * 2
def baseEnd_18261 : Nat := 9376670231858287453525

theorem tailTrace_18261 : CollatzResearch.WordTrace tailWord_18261 prefixEnd_18261 9376670231858287453525 := by
  unfold tailWord_18261
  simp only [CollatzResearch.WordTrace]
  refine ⟨666033386850990575614637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 444022257900660383743091 666033386850990575614637)
  ·
    refine ⟨249762520069121465855489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 666033386850990575614637 249762520069121465855489)
    ·
      refine ⟨187321890051841099391617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249762520069121465855489 187321890051841099391617)
      ·
        refine ⟨140491417538880824543713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187321890051841099391617 140491417538880824543713)
        ·
          refine ⟨105368563154160618407785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140491417538880824543713 105368563154160618407785)
          ·
            refine ⟨79026422365620463805839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105368563154160618407785 79026422365620463805839)
            ·
              refine ⟨118539633548430695708759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79026422365620463805839 118539633548430695708759)
              ·
                refine ⟨177809450322646043563139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118539633548430695708759 177809450322646043563139)
                ·
                  refine ⟨266714175483969065344709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177809450322646043563139 266714175483969065344709)
                  ·
                    refine ⟨50008907903244199752133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 266714175483969065344709 50008907903244199752133)
                    ·
                      refine ⟨9376670231858287453525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 50008907903244199752133 9376670231858287453525)
                      ·
                        rfl

theorem cell23_18261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_18261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18261 prefixEnd_18261 := by exact prefixLift 18261
  have htrace : WordTrace (prefixWord ++ tailWord_18261) baseStart_18261 baseEnd_18261 := by
    simpa [prefixWord, tailWord_18261, baseEnd_18261] using wordTrace_append hprefix tailTrace_18261
  have hstable : (prefixWord ++ tailWord_18261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18261).length < 2 ^ (prefixWord ++ tailWord_18261).sum := by decide
  have hdescent : baseEnd_18261 < baseStart_18261 := by decide
  rcases family_descends (prefixWord ++ tailWord_18261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18265 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 2, 2, 2]
def baseStart_18265 : Nat := 118140960795 + 18265 * 2 ^ 59
def prefixEnd_18265 : Nat := 4983230072969 + 3 ^ 40 * 18265 * 2
def baseEnd_18265 : Nat := 9378724154476271803507

theorem tailTrace_18265 : CollatzResearch.WordTrace tailWord_18265 prefixEnd_18265 9378724154476271803507 := by
  unfold tailWord_18265
  simp only [CollatzResearch.WordTrace]
  refine ⟨666179278836499258760249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 444119519224332839173499 666179278836499258760249)
  ·
    refine ⟨499634459127374444070187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 666179278836499258760249 499634459127374444070187)
    ·
      refine ⟨749451688691061666105281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499634459127374444070187 749451688691061666105281)
      ·
        refine ⟨562088766518296249578961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 749451688691061666105281 562088766518296249578961)
        ·
          refine ⟨421566574888722187184221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562088766518296249578961 421566574888722187184221)
          ·
            refine ⟨158087465583270820194083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421566574888722187184221 158087465583270820194083)
            ·
              refine ⟨237131198374906230291125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158087465583270820194083 237131198374906230291125)
              ·
                refine ⟨22231049847647459089793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 237131198374906230291125 22231049847647459089793)
                ·
                  refine ⟨16673287385735594317345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22231049847647459089793 16673287385735594317345)
                  ·
                    refine ⟨12504965539301695738009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16673287385735594317345 12504965539301695738009)
                    ·
                      refine ⟨9378724154476271803507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12504965539301695738009 9378724154476271803507)
                      ·
                        rfl

theorem cell23_18265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 2, 2].length) (baseStart_18265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18265 prefixEnd_18265 := by exact prefixLift 18265
  have htrace : WordTrace (prefixWord ++ tailWord_18265) baseStart_18265 baseEnd_18265 := by
    simpa [prefixWord, tailWord_18265, baseEnd_18265] using wordTrace_append hprefix tailTrace_18265
  have hstable : (prefixWord ++ tailWord_18265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18265).length < 2 ^ (prefixWord ++ tailWord_18265).sum := by decide
  have hdescent : baseEnd_18265 < baseStart_18265 := by decide
  rcases family_descends (prefixWord ++ tailWord_18265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18271 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 7]
def baseStart_18271 : Nat := 118140960795 + 18271 * 2 ^ 59
def prefixEnd_18271 : Nat := 4983230072969 + 3 ^ 40 * 18271 * 2
def baseEnd_18271 : Nat := 1042422782044805369831

theorem tailTrace_18271 : CollatzResearch.WordTrace tailWord_18271 prefixEnd_18271 1042422782044805369831 := by
  unfold tailWord_18271
  simp only [CollatzResearch.WordTrace]
  refine ⟨666398116814762283478667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 444265411209841522319111 666398116814762283478667)
  ·
    refine ⟨999597175222143425218001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 666398116814762283478667 999597175222143425218001)
    ·
      refine ⟨749697881416607568913501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 999597175222143425218001 749697881416607568913501)
      ·
        refine ⟨281136705531227838342563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 749697881416607568913501 281136705531227838342563)
        ·
          refine ⟨421705058296841757513845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281136705531227838342563 421705058296841757513845)
          ·
            refine ⟨39534849215328914766923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 421705058296841757513845 39534849215328914766923)
            ·
              refine ⟨59302273822993372150385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39534849215328914766923 59302273822993372150385)
              ·
                refine ⟨44476705367245029112789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59302273822993372150385 44476705367245029112789)
                ·
                  refine ⟨1042422782044805369831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 44476705367245029112789 1042422782044805369831)
                  ·
                    rfl

theorem cell23_18271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 7].length) (baseStart_18271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18271 prefixEnd_18271 := by exact prefixLift 18271
  have htrace : WordTrace (prefixWord ++ tailWord_18271) baseStart_18271 baseEnd_18271 := by
    simpa [prefixWord, tailWord_18271, baseEnd_18271] using wordTrace_append hprefix tailTrace_18271
  have hstable : (prefixWord ++ tailWord_18271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18271).length < 2 ^ (prefixWord ++ tailWord_18271).sum := by decide
  have hdescent : baseEnd_18271 < baseStart_18271 := by decide
  rcases family_descends (prefixWord ++ tailWord_18271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18301 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_18301 : Nat := 118140960795 + 18301 * 2 ^ 59
def prefixEnd_18301 : Nat := 4983230072969 + 3 ^ 40 * 18301 * 2
def baseEnd_18301 : Nat := 3132403152679376984447

theorem tailTrace_18301 : CollatzResearch.WordTrace tailWord_18301 prefixEnd_18301 3132403152679376984447 := by
  unfold tailWord_18301
  simp only [CollatzResearch.WordTrace]
  refine ⟨667492306706077407070757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 444994871137384938047171 667492306706077407070757)
  ·
    refine ⟨125154807507389513825767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 667492306706077407070757 125154807507389513825767)
    ·
      refine ⟨187732211261084270738651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125154807507389513825767 187732211261084270738651)
      ·
        refine ⟨281598316891626406107977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187732211261084270738651 281598316891626406107977)
        ·
          refine ⟨211198737668719804580983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281598316891626406107977 211198737668719804580983)
          ·
            refine ⟨316798106503079706871475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211198737668719804580983 316798106503079706871475)
            ·
              refine ⟨475197159754619560307213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316798106503079706871475 475197159754619560307213)
              ·
                refine ⟨178198934907982335115205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 475197159754619560307213 178198934907982335115205)
                ·
                  refine ⟨33412300295246687834101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178198934907982335115205 33412300295246687834101)
                  ·
                    refine ⟨3132403152679376984447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33412300295246687834101 3132403152679376984447)
                    ·
                      rfl

theorem cell23_18301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_18301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18301 prefixEnd_18301 := by exact prefixLift 18301
  have htrace : WordTrace (prefixWord ++ tailWord_18301) baseStart_18301 baseEnd_18301 := by
    simpa [prefixWord, tailWord_18301, baseEnd_18301] using wordTrace_append hprefix tailTrace_18301
  have hstable : (prefixWord ++ tailWord_18301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18301).length < 2 ^ (prefixWord ++ tailWord_18301).sum := by decide
  have hdescent : baseEnd_18301 < baseStart_18301 := by decide
  rcases family_descends (prefixWord ++ tailWord_18301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18305 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 7]
def baseStart_18305 : Nat := 118140960795 + 18305 * 2 ^ 59
def prefixEnd_18305 : Nat := 4983230072969 + 3 ^ 40 * 18305 * 2
def baseEnd_18305 : Nat := 1044362597850679478147

theorem tailTrace_18305 : CollatzResearch.WordTrace tailWord_18305 prefixEnd_18305 1044362597850679478147 := by
  unfold tailWord_18305
  simp only [CollatzResearch.WordTrace]
  refine ⟨667638198691586090216369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 445092132461057393477579 667638198691586090216369)
  ·
    refine ⟨500728649018689567662277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 667638198691586090216369 500728649018689567662277)
    ·
      refine ⟨93886621691004293936677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 500728649018689567662277 93886621691004293936677)
      ·
        refine ⟨17603741567063305113127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93886621691004293936677 17603741567063305113127)
        ·
          refine ⟨26405612350594957669691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17603741567063305113127 26405612350594957669691)
          ·
            refine ⟨39608418525892436504537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26405612350594957669691 39608418525892436504537)
            ·
              refine ⟨29706313894419327378403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39608418525892436504537 29706313894419327378403)
              ·
                refine ⟨44559470841628991067605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29706313894419327378403 44559470841628991067605)
                ·
                  refine ⟨1044362597850679478147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 44559470841628991067605 1044362597850679478147)
                  ·
                    rfl

theorem cell23_18305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 7].length) (baseStart_18305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18305 prefixEnd_18305 := by exact prefixLift 18305
  have htrace : WordTrace (prefixWord ++ tailWord_18305) baseStart_18305 baseEnd_18305 := by
    simpa [prefixWord, tailWord_18305, baseEnd_18305] using wordTrace_append hprefix tailTrace_18305
  have hstable : (prefixWord ++ tailWord_18305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18305).length < 2 ^ (prefixWord ++ tailWord_18305).sum := by decide
  have hdescent : baseEnd_18305 < baseStart_18305 := by decide
  rcases family_descends (prefixWord ++ tailWord_18305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18308 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_18308 : Nat := 118140960795 + 18308 * 2 ^ 59
def prefixEnd_18308 : Nat := 4983230072969 + 3 ^ 40 * 18308 * 2
def baseEnd_18308 : Nat := 9400803822619603565809

theorem tailTrace_18308 : CollatzResearch.WordTrace tailWord_18308 prefixEnd_18308 9400803822619603565809 := by
  unfold tailWord_18308
  simp only [CollatzResearch.WordTrace]
  refine ⟨333873808840358801287789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 445165078453811735050385 333873808840358801287789)
  ·
    refine ⟨125202678315134550482921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 333873808840358801287789 125202678315134550482921)
    ·
      refine ⟨93902008736350912862191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125202678315134550482921 93902008736350912862191)
      ·
        refine ⟨140853013104526369293287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93902008736350912862191 140853013104526369293287)
        ·
          refine ⟨211279519656789553939931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140853013104526369293287 211279519656789553939931)
          ·
            refine ⟨316919279485184330909897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211279519656789553939931 316919279485184330909897)
            ·
              refine ⟨237689459613888248182423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316919279485184330909897 237689459613888248182423)
              ·
                refine ⟨356534189420832372273635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237689459613888248182423 356534189420832372273635)
                ·
                  refine ⟨534801284131248558410453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356534189420832372273635 534801284131248558410453)
                  ·
                    refine ⟨12534405096826138087745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 534801284131248558410453 12534405096826138087745)
                    ·
                      refine ⟨9400803822619603565809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12534405096826138087745 9400803822619603565809)
                      ·
                        rfl

theorem cell23_18308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_18308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18308 prefixEnd_18308 := by exact prefixLift 18308
  have htrace : WordTrace (prefixWord ++ tailWord_18308) baseStart_18308 baseEnd_18308 := by
    simpa [prefixWord, tailWord_18308, baseEnd_18308] using wordTrace_append hprefix tailTrace_18308
  have hstable : (prefixWord ++ tailWord_18308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18308).length < 2 ^ (prefixWord ++ tailWord_18308).sum := by decide
  have hdescent : baseEnd_18308 < baseStart_18308 := by decide
  rcases family_descends (prefixWord ++ tailWord_18308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18321 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_18321 : Nat := 118140960795 + 18321 * 2 ^ 59
def prefixEnd_18321 : Nat := 4983230072969 + 3 ^ 40 * 18321 * 2
def baseEnd_18321 : Nat := 9407479071128052703249

theorem tailTrace_18321 : CollatzResearch.WordTrace tailWord_18321 prefixEnd_18321 9407479071128052703249 := by
  unfold tailWord_18321
  simp only [CollatzResearch.WordTrace]
  refine ⟨668221766633620822798817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 445481177755747215199211 668221766633620822798817)
  ·
    refine ⟨501166324975215617099113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 668221766633620822798817 501166324975215617099113)
    ·
      refine ⟨375874743731411712824335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 501166324975215617099113 375874743731411712824335)
      ·
        refine ⟨563812115597117569236503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375874743731411712824335 563812115597117569236503)
        ·
          refine ⟨845718173395676353854755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563812115597117569236503 845718173395676353854755)
          ·
            refine ⟨1268577260093514530782133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845718173395676353854755 1268577260093514530782133)
            ·
              refine ⟨118929118133766987260825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1268577260093514530782133 118929118133766987260825)
              ·
                refine ⟨89196838600325240445619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118929118133766987260825 89196838600325240445619)
                ·
                  refine ⟨133795257900487860668429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89196838600325240445619 133795257900487860668429)
                  ·
                    refine ⟨50173221712682947750661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133795257900487860668429 50173221712682947750661)
                    ·
                      refine ⟨9407479071128052703249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 50173221712682947750661 9407479071128052703249)
                      ·
                        rfl

theorem cell23_18321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_18321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18321 prefixEnd_18321 := by exact prefixLift 18321
  have htrace : WordTrace (prefixWord ++ tailWord_18321) baseStart_18321 baseEnd_18321 := by
    simpa [prefixWord, tailWord_18321, baseEnd_18321] using wordTrace_append hprefix tailTrace_18321
  have hstable : (prefixWord ++ tailWord_18321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18321).length < 2 ^ (prefixWord ++ tailWord_18321).sum := by decide
  have hdescent : baseEnd_18321 < baseStart_18321 := by decide
  rcases family_descends (prefixWord ++ tailWord_18321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18361 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 8]
def baseStart_18361 : Nat := 118140960795 + 18361 * 2 ^ 59
def prefixEnd_18361 : Nat := 4983230072969 + 3 ^ 40 * 18361 * 2
def baseEnd_18361 : Nat := 1047557588589766244785

theorem tailTrace_18361 : CollatzResearch.WordTrace tailWord_18361 prefixEnd_18361 1047557588589766244785 := by
  unfold tailWord_18361
  simp only [CollatzResearch.WordTrace]
  refine ⟨669680686488707654254937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 446453790992471769503291 669680686488707654254937)
  ·
    refine ⟨502260514866530740691203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 669680686488707654254937 502260514866530740691203)
    ·
      refine ⟨753390772299796111036805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502260514866530740691203 753390772299796111036805)
      ·
        refine ⟨141260769806211770819401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 753390772299796111036805 141260769806211770819401)
        ·
          refine ⟨105945577354658828114551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141260769806211770819401 105945577354658828114551)
          ·
            refine ⟨158918366031988242171827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105945577354658828114551 158918366031988242171827)
            ·
              refine ⟨238377549047982363257741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158918366031988242171827 238377549047982363257741)
              ·
                refine ⟨89391580892993386221653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238377549047982363257741 89391580892993386221653)
                ·
                  refine ⟨1047557588589766244785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 89391580892993386221653 1047557588589766244785)
                  ·
                    rfl

theorem cell23_18361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 8].length) (baseStart_18361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18361 prefixEnd_18361 := by exact prefixLift 18361
  have htrace : WordTrace (prefixWord ++ tailWord_18361) baseStart_18361 baseEnd_18361 := by
    simpa [prefixWord, tailWord_18361, baseEnd_18361] using wordTrace_append hprefix tailTrace_18361
  have hstable : (prefixWord ++ tailWord_18361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18361).length < 2 ^ (prefixWord ++ tailWord_18361).sum := by decide
  have hdescent : baseEnd_18361 < baseStart_18361 := by decide
  rcases family_descends (prefixWord ++ tailWord_18361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18365 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_18365 : Nat := 118140960795 + 18365 * 2 ^ 59
def prefixEnd_18365 : Nat := 4983230072969 + 3 ^ 40 * 18365 * 2
def baseEnd_18365 : Nat := 3143357406641960184349

theorem tailTrace_18365 : CollatzResearch.WordTrace tailWord_18365 prefixEnd_18365 3143357406641960184349 := by
  unfold tailWord_18365
  simp only [CollatzResearch.WordTrace]
  refine ⟨669826578474216337400549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 446551052316144224933699 669826578474216337400549)
  ·
    refine ⟨125592483463915563262603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 669826578474216337400549 125592483463915563262603)
    ·
      refine ⟨188388725195873344893905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125592483463915563262603 188388725195873344893905)
      ·
        refine ⟨141291543896905008670429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188388725195873344893905 141291543896905008670429)
        ·
          refine ⟨52984328961339378251411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141291543896905008670429 52984328961339378251411)
          ·
            refine ⟨79476493442009067377117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52984328961339378251411 79476493442009067377117)
            ·
              refine ⟨29803685040753400266419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79476493442009067377117 29803685040753400266419)
              ·
                refine ⟨44705527561130100399629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29803685040753400266419 44705527561130100399629)
                ·
                  refine ⟨16764572835423787649861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44705527561130100399629 16764572835423787649861)
                  ·
                    refine ⟨3143357406641960184349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16764572835423787649861 3143357406641960184349)
                    ·
                      rfl

theorem cell23_18365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_18365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18365 prefixEnd_18365 := by exact prefixLift 18365
  have htrace : WordTrace (prefixWord ++ tailWord_18365) baseStart_18365 baseEnd_18365 := by
    simpa [prefixWord, tailWord_18365, baseEnd_18365] using wordTrace_append hprefix tailTrace_18365
  have hstable : (prefixWord ++ tailWord_18365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18365).length < 2 ^ (prefixWord ++ tailWord_18365).sum := by decide
  have hdescent : baseEnd_18365 < baseStart_18365 := by decide
  rcases family_descends (prefixWord ++ tailWord_18365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18415 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 2, 3, 2]
def baseStart_18415 : Nat := 118140960795 + 18415 * 2 ^ 59
def prefixEnd_18415 : Nat := 4983230072969 + 3 ^ 40 * 18415 * 2
def baseEnd_18415 : Nat := 9455746252650684927817

theorem tailTrace_18415 : CollatzResearch.WordTrace tailWord_18415 prefixEnd_18415 9455746252650684927817 := by
  unfold tailWord_18415
  simp only [CollatzResearch.WordTrace]
  refine ⟨671650228293074876720699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 447766818862049917813799 671650228293074876720699)
  ·
    refine ⟨1007475342439612315081049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 671650228293074876720699 1007475342439612315081049)
    ·
      refine ⟨755606506829709236310787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1007475342439612315081049 755606506829709236310787)
      ·
        refine ⟨1133409760244563854466181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755606506829709236310787 1133409760244563854466181)
        ·
          refine ⟨212514330045855722712409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1133409760244563854466181 212514330045855722712409)
          ·
            refine ⟨159385747534391792034307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212514330045855722712409 159385747534391792034307)
            ·
              refine ⟨239078621301587688051461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159385747534391792034307 239078621301587688051461)
              ·
                refine ⟨44827241494047691509649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239078621301587688051461 44827241494047691509649)
                ·
                  refine ⟨33620431120535768632237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44827241494047691509649 33620431120535768632237)
                  ·
                    refine ⟨12607661670200913237089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33620431120535768632237 12607661670200913237089)
                    ·
                      refine ⟨9455746252650684927817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12607661670200913237089 9455746252650684927817)
                      ·
                        rfl

theorem cell23_18415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 3, 2].length) (baseStart_18415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18415 prefixEnd_18415 := by exact prefixLift 18415
  have htrace : WordTrace (prefixWord ++ tailWord_18415) baseStart_18415 baseEnd_18415 := by
    simpa [prefixWord, tailWord_18415, baseEnd_18415] using wordTrace_append hprefix tailTrace_18415
  have hstable : (prefixWord ++ tailWord_18415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18415).length < 2 ^ (prefixWord ++ tailWord_18415).sum := by decide
  have hdescent : baseEnd_18415 < baseStart_18415 := by decide
  rcases family_descends (prefixWord ++ tailWord_18415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18428 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_18428 : Nat := 118140960795 + 18428 * 2 ^ 59
def prefixEnd_18428 : Nat := 4983230072969 + 3 ^ 40 * 18428 * 2
def baseEnd_18428 : Nat := 9462421501159134065257

theorem tailTrace_18428 : CollatzResearch.WordTrace tailWord_18428 prefixEnd_18428 9462421501159134065257 := by
  unfold tailWord_18428
  simp only [CollatzResearch.WordTrace]
  refine ⟨336062188622989048471969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 448082918163985397962625 336062188622989048471969)
  ·
    refine ⟨252046641467241786353977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 336062188622989048471969 252046641467241786353977)
    ·
      refine ⟨189034981100431339765483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252046641467241786353977 189034981100431339765483)
      ·
        refine ⟨283552471650647009648225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189034981100431339765483 283552471650647009648225)
        ·
          refine ⟨212664353737985257236169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283552471650647009648225 212664353737985257236169)
          ·
            refine ⟨159498265303488942927127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212664353737985257236169 159498265303488942927127)
            ·
              refine ⟨239247397955233414390691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159498265303488942927127 239247397955233414390691)
              ·
                refine ⟨358871096932850121586037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239247397955233414390691 358871096932850121586037)
                ·
                  refine ⟨33644165337454698898691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 358871096932850121586037 33644165337454698898691)
                  ·
                    refine ⟨50466248006182048348037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33644165337454698898691 50466248006182048348037)
                    ·
                      refine ⟨9462421501159134065257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 50466248006182048348037 9462421501159134065257)
                      ·
                        rfl

theorem cell23_18428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_18428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18428 prefixEnd_18428 := by exact prefixLift 18428
  have htrace : WordTrace (prefixWord ++ tailWord_18428) baseStart_18428 baseEnd_18428 := by
    simpa [prefixWord, tailWord_18428, baseEnd_18428] using wordTrace_append hprefix tailTrace_18428
  have hstable : (prefixWord ++ tailWord_18428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18428).length < 2 ^ (prefixWord ++ tailWord_18428).sum := by decide
  have hdescent : baseEnd_18428 < baseStart_18428 := by decide
  rcases family_descends (prefixWord ++ tailWord_18428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18451 : List Nat := [1, 1, 1, 2, 1, 4, 2, 11]
def baseStart_18451 : Nat := 118140960795 + 18451 * 2 ^ 59
def prefixEnd_18451 : Nat := 4983230072969 + 3 ^ 40 * 18451 * 2
def baseEnd_18451 : Nat := 350897465044909039913

theorem tailTrace_18451 : CollatzResearch.WordTrace tailWord_18451 prefixEnd_18451 350897465044909039913 := by
  unfold tailWord_18451
  simp only [CollatzResearch.WordTrace]
  refine ⟨672963256162653025031207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 448642170775102016687471 672963256162653025031207)
  ·
    refine ⟨1009444884243979537546811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 672963256162653025031207 1009444884243979537546811)
    ·
      refine ⟨1514167326365969306320217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1009444884243979537546811 1514167326365969306320217)
      ·
        refine ⟨1135625494774476979740163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1514167326365969306320217 1135625494774476979740163)
        ·
          refine ⟨1703438242161715469610245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135625494774476979740163 1703438242161715469610245)
          ·
            refine ⟨319394670405321650551921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1703438242161715469610245 319394670405321650551921)
            ·
              refine ⟨239546002803991237913941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319394670405321650551921 239546002803991237913941)
              ·
                refine ⟨350897465044909039913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 239546002803991237913941 350897465044909039913)
                ·
                  rfl

theorem cell23_18451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 11].length) (baseStart_18451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18451 prefixEnd_18451 := by exact prefixLift 18451
  have htrace : WordTrace (prefixWord ++ tailWord_18451) baseStart_18451 baseEnd_18451 := by
    simpa [prefixWord, tailWord_18451, baseEnd_18451] using wordTrace_append hprefix tailTrace_18451
  have hstable : (prefixWord ++ tailWord_18451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18451).length < 2 ^ (prefixWord ++ tailWord_18451).sum := by decide
  have hdescent : baseEnd_18451 < baseStart_18451 := by decide
  rcases family_descends (prefixWord ++ tailWord_18451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18489 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 2, 4]
def baseStart_18489 : Nat := 118140960795 + 18489 * 2 ^ 59
def prefixEnd_18489 : Nat := 4983230072969 + 3 ^ 40 * 18489 * 2
def baseEnd_18489 : Nat := 3164581273694465134159

theorem tailTrace_18489 : CollatzResearch.WordTrace tailWord_18489 prefixEnd_18489 3164581273694465134159 := by
  unfold tailWord_18489
  simp only [CollatzResearch.WordTrace]
  refine ⟨674349230024985514914521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 449566153349990343276347 674349230024985514914521)
  ·
    refine ⟨505761922518739136185891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 674349230024985514914521 505761922518739136185891)
    ·
      refine ⟨758642883778108704278837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 505761922518739136185891 758642883778108704278837)
      ·
        refine ⟨71122770354197691026141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 758642883778108704278837 71122770354197691026141)
        ·
          refine ⟨26671038882824134134803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71122770354197691026141 26671038882824134134803)
          ·
            refine ⟨40006558324236201202205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26671038882824134134803 40006558324236201202205)
            ·
              refine ⟨15002459371588575450827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40006558324236201202205 15002459371588575450827)
              ·
                refine ⟨22503689057382863176241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15002459371588575450827 22503689057382863176241)
                ·
                  refine ⟨16877766793037147382181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22503689057382863176241 16877766793037147382181)
                  ·
                    refine ⟨3164581273694465134159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16877766793037147382181 3164581273694465134159)
                    ·
                      rfl

theorem cell23_18489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 2, 4].length) (baseStart_18489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18489 prefixEnd_18489 := by exact prefixLift 18489
  have htrace : WordTrace (prefixWord ++ tailWord_18489) baseStart_18489 baseEnd_18489 := by
    simpa [prefixWord, tailWord_18489, baseEnd_18489] using wordTrace_append hprefix tailTrace_18489
  have hstable : (prefixWord ++ tailWord_18489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18489).length < 2 ^ (prefixWord ++ tailWord_18489).sum := by decide
  have hdescent : baseEnd_18489 < baseStart_18489 := by decide
  rcases family_descends (prefixWord ++ tailWord_18489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18495 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 3]
def baseStart_18495 : Nat := 118140960795 + 18495 * 2 ^ 59
def prefixEnd_18495 : Nat := 4983230072969 + 3 ^ 40 * 18495 * 2
def baseEnd_18495 : Nat := 9496824705010371927449

theorem tailTrace_18495 : CollatzResearch.WordTrace tailWord_18495 prefixEnd_18495 9496824705010371927449 := by
  unfold tailWord_18495
  simp only [CollatzResearch.WordTrace]
  refine ⟨674568068003248539632939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 449712045335499026421959 674568068003248539632939)
  ·
    refine ⟨1011852102004872809449409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 674568068003248539632939 1011852102004872809449409)
    ·
      refine ⟨758889076503654607087057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1011852102004872809449409 758889076503654607087057)
      ·
        refine ⟨569166807377740955315293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 758889076503654607087057 569166807377740955315293)
        ·
          refine ⟨213437552766652858243235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 569166807377740955315293 213437552766652858243235)
          ·
            refine ⟨320156329149979287364853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213437552766652858243235 320156329149979287364853)
            ·
              refine ⟨30014655857810558190455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 320156329149979287364853 30014655857810558190455)
              ·
                refine ⟨45021983786715837285683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30014655857810558190455 45021983786715837285683)
                ·
                  refine ⟨67532975680073755928525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45021983786715837285683 67532975680073755928525)
                  ·
                    refine ⟨25324865880027658473197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67532975680073755928525 25324865880027658473197)
                    ·
                      refine ⟨9496824705010371927449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 25324865880027658473197 9496824705010371927449)
                      ·
                        rfl

theorem cell23_18495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_18495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18495 prefixEnd_18495 := by exact prefixLift 18495
  have htrace : WordTrace (prefixWord ++ tailWord_18495) baseStart_18495 baseEnd_18495 := by
    simpa [prefixWord, tailWord_18495, baseEnd_18495] using wordTrace_append hprefix tailTrace_18495
  have hstable : (prefixWord ++ tailWord_18495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18495).length < 2 ^ (prefixWord ++ tailWord_18495).sum := by decide
  have hdescent : baseEnd_18495 < baseStart_18495 := by decide
  rcases family_descends (prefixWord ++ tailWord_18495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18508 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_18508 : Nat := 118140960795 + 18508 * 2 ^ 59
def prefixEnd_18508 : Nat := 4983230072969 + 3 ^ 40 * 18508 * 2
def baseEnd_18508 : Nat := 9503499953518821064889

theorem tailTrace_18508 : CollatzResearch.WordTrace tailWord_18508 prefixEnd_18508 9503499953518821064889 := by
  unfold tailWord_18508
  simp only [CollatzResearch.WordTrace]
  refine ⟨337521108478075879928089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 450028144637434506570785 337521108478075879928089)
  ·
    refine ⟨253140831358556909946067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 337521108478075879928089 253140831358556909946067)
    ·
      refine ⟨379711247037835364919101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253140831358556909946067 379711247037835364919101)
      ·
        refine ⟨142391717639188261844663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 379711247037835364919101 142391717639188261844663)
        ·
          refine ⟨213587576458782392766995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142391717639188261844663 213587576458782392766995)
          ·
            refine ⟨320381364688173589150493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213587576458782392766995 320381364688173589150493)
            ·
              refine ⟨120143011758065095931435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 320381364688173589150493 120143011758065095931435)
              ·
                refine ⟨180214517637097643897153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120143011758065095931435 180214517637097643897153)
                ·
                  refine ⟨135160888227823232922865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180214517637097643897153 135160888227823232922865)
                  ·
                    refine ⟨101370666170867424692149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 135160888227823232922865 101370666170867424692149)
                    ·
                      refine ⟨9503499953518821064889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 101370666170867424692149 9503499953518821064889)
                      ·
                        rfl

theorem cell23_18508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_18508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18508 prefixEnd_18508 := by exact prefixLift 18508
  have htrace : WordTrace (prefixWord ++ tailWord_18508) baseStart_18508 baseEnd_18508 := by
    simpa [prefixWord, tailWord_18508, baseEnd_18508] using wordTrace_append hprefix tailTrace_18508
  have hstable : (prefixWord ++ tailWord_18508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18508).length < 2 ^ (prefixWord ++ tailWord_18508).sum := by decide
  have hdescent : baseEnd_18508 < baseStart_18508 := by decide
  rcases family_descends (prefixWord ++ tailWord_18508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18522 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2]
def baseStart_18522 : Nat := 118140960795 + 18522 * 2 ^ 59
def prefixEnd_18522 : Nat := 4983230072969 + 3 ^ 40 * 18522 * 2
def baseEnd_18522 : Nat := 9510688682681766289825

theorem tailTrace_18522 : CollatzResearch.WordTrace tailWord_18522 prefixEnd_18522 9510688682681766289825 := by
  unfold tailWord_18522
  simp only [CollatzResearch.WordTrace]
  refine ⟨168888209726358037716455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 450368559270288100577213 168888209726358037716455)
  ·
    refine ⟨253332314589537056574683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168888209726358037716455 253332314589537056574683)
    ·
      refine ⟨379998471884305584862025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253332314589537056574683 379998471884305584862025)
      ·
        refine ⟨284998853913229188646519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379998471884305584862025 284998853913229188646519)
        ·
          refine ⟨427498280869843782969779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284998853913229188646519 427498280869843782969779)
          ·
            refine ⟨641247421304765674454669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427498280869843782969779 641247421304765674454669)
            ·
              refine ⟨240467782989287127920501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 641247421304765674454669 240467782989287127920501)
              ·
                refine ⟨22543854655245668242547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 240467782989287127920501 22543854655245668242547)
                ·
                  refine ⟨33815781982868502363821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22543854655245668242547 33815781982868502363821)
                  ·
                    refine ⟨12680918243575688386433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33815781982868502363821 12680918243575688386433)
                    ·
                      refine ⟨9510688682681766289825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12680918243575688386433 9510688682681766289825)
                      ·
                        rfl

theorem cell23_18522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_18522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18522 prefixEnd_18522 := by exact prefixLift 18522
  have htrace : WordTrace (prefixWord ++ tailWord_18522) baseStart_18522 baseEnd_18522 := by
    simpa [prefixWord, tailWord_18522, baseEnd_18522] using wordTrace_append hprefix tailTrace_18522
  have hstable : (prefixWord ++ tailWord_18522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18522).length < 2 ^ (prefixWord ++ tailWord_18522).sum := by decide
  have hdescent : baseEnd_18522 < baseStart_18522 := by decide
  rcases family_descends (prefixWord ++ tailWord_18522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18530 : List Nat := [3, 3, 2, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_18530 : Nat := 118140960795 + 18530 * 2 ^ 59
def prefixEnd_18530 : Nat := 4983230072969 + 3 ^ 40 * 18530 * 2
def baseEnd_18530 : Nat := 9514796527917734989789

theorem tailTrace_18530 : CollatzResearch.WordTrace tailWord_18530 prefixEnd_18530 9514796527917734989789 := by
  unfold tailWord_18530
  simp only [CollatzResearch.WordTrace]
  refine ⟨168961155719112379289261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 450563081917633011438029 168961155719112379289261)
  ·
    refine ⟨63360433394667142233473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168961155719112379289261 63360433394667142233473)
    ·
      refine ⟨47520325046000356675105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63360433394667142233473 47520325046000356675105)
      ·
        refine ⟨35640243784500267506329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47520325046000356675105 35640243784500267506329)
        ·
          refine ⟨26730182838375200629747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35640243784500267506329 26730182838375200629747)
          ·
            refine ⟨40095274257562800944621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26730182838375200629747 40095274257562800944621)
            ·
              refine ⟨15035727846586050354233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40095274257562800944621 15035727846586050354233)
              ·
                refine ⟨11276795884939537765675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15035727846586050354233 11276795884939537765675)
                ·
                  refine ⟨16915193827409306648513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11276795884939537765675 16915193827409306648513)
                  ·
                    refine ⟨12686395370556979986385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16915193827409306648513 12686395370556979986385)
                    ·
                      refine ⟨9514796527917734989789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12686395370556979986385 9514796527917734989789)
                      ·
                        rfl

theorem cell23_18530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_18530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18530 prefixEnd_18530 := by exact prefixLift 18530
  have htrace : WordTrace (prefixWord ++ tailWord_18530) baseStart_18530 baseEnd_18530 := by
    simpa [prefixWord, tailWord_18530, baseEnd_18530] using wordTrace_append hprefix tailTrace_18530
  have hstable : (prefixWord ++ tailWord_18530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18530).length < 2 ^ (prefixWord ++ tailWord_18530).sum := by decide
  have hdescent : baseEnd_18530 < baseStart_18530 := by decide
  rcases family_descends (prefixWord ++ tailWord_18530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18546 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 2, 1, 3]
def baseStart_18546 : Nat := 118140960795 + 18546 * 2 ^ 59
def prefixEnd_18546 : Nat := 4983230072969 + 3 ^ 40 * 18546 * 2
def baseEnd_18546 : Nat := 9523012218389672389715

theorem tailTrace_18546 : CollatzResearch.WordTrace tailWord_18546 prefixEnd_18546 9523012218389672389715 := by
  unfold tailWord_18546
  simp only [CollatzResearch.WordTrace]
  refine ⟨169107047704621062434873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 450952127212322833159661 169107047704621062434873)
  ·
    refine ⟨126830285778465796826155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169107047704621062434873 126830285778465796826155)
    ·
      refine ⟨190245428667698695239233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126830285778465796826155 190245428667698695239233)
      ·
        refine ⟨142684071500774021429425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190245428667698695239233 142684071500774021429425)
        ·
          refine ⟨107013053625580516072069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142684071500774021429425 107013053625580516072069)
          ·
            refine ⟨20064947554796346763513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107013053625580516072069 20064947554796346763513)
            ·
              refine ⟨15048710666097260072635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20064947554796346763513 15048710666097260072635)
              ·
                refine ⟨22573065999145890108953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15048710666097260072635 22573065999145890108953)
                ·
                  refine ⟨16929799499359417581715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22573065999145890108953 16929799499359417581715)
                  ·
                    refine ⟨25394699249039126372573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16929799499359417581715 25394699249039126372573)
                    ·
                      refine ⟨9523012218389672389715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 25394699249039126372573 9523012218389672389715)
                      ·
                        rfl

theorem cell23_18546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_18546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18546 prefixEnd_18546 := by exact prefixLift 18546
  have htrace : WordTrace (prefixWord ++ tailWord_18546) baseStart_18546 baseEnd_18546 := by
    simpa [prefixWord, tailWord_18546, baseEnd_18546] using wordTrace_append hprefix tailTrace_18546
  have hstable : (prefixWord ++ tailWord_18546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18546).length < 2 ^ (prefixWord ++ tailWord_18546).sum := by decide
  have hdescent : baseEnd_18546 < baseStart_18546 := by decide
  rcases family_descends (prefixWord ++ tailWord_18546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18592 : List Nat := [2, 1, 1, 4, 2, 3, 1, 4, 5]
def baseStart_18592 : Nat := 118140960795 + 18592 * 2 ^ 59
def prefixEnd_18592 : Nat := 4983230072969 + 3 ^ 40 * 18592 * 2
def baseEnd_18592 : Nat := 1060736925388499157167

theorem tailTrace_18592 : CollatzResearch.WordTrace tailWord_18592 prefixEnd_18592 1060736925388499157167 := by
  unfold tailWord_18592
  simp only [CollatzResearch.WordTrace]
  refine ⟨339052974325917052957015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 452070632434556070609353 339052974325917052957015)
  ·
    refine ⟨508579461488875579435523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 339052974325917052957015 508579461488875579435523)
    ·
      refine ⟨762869192233313369153285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 508579461488875579435523 762869192233313369153285)
      ·
        refine ⟨143037973543746256716241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 762869192233313369153285 143037973543746256716241)
        ·
          refine ⟨107278480157809692537181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143037973543746256716241 107278480157809692537181)
          ·
            refine ⟨40229430059178634701443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107278480157809692537181 40229430059178634701443)
            ·
              refine ⟨60344145088767952052165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40229430059178634701443 60344145088767952052165)
              ·
                refine ⟨11314527204143991009781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60344145088767952052165 11314527204143991009781)
                ·
                  refine ⟨1060736925388499157167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11314527204143991009781 1060736925388499157167)
                  ·
                    rfl

theorem cell23_18592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 5].length) (baseStart_18592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18592 prefixEnd_18592 := by exact prefixLift 18592
  have htrace : WordTrace (prefixWord ++ tailWord_18592) baseStart_18592 baseEnd_18592 := by
    simpa [prefixWord, tailWord_18592, baseEnd_18592] using wordTrace_append hprefix tailTrace_18592
  have hstable : (prefixWord ++ tailWord_18592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18592).length < 2 ^ (prefixWord ++ tailWord_18592).sum := by decide
  have hdescent : baseEnd_18592 < baseStart_18592 := by decide
  rcases family_descends (prefixWord ++ tailWord_18592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18622 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_18622 : Nat := 118140960795 + 18622 * 2 ^ 59
def prefixEnd_18622 : Nat := 4983230072969 + 3 ^ 40 * 18622 * 2
def baseEnd_18622 : Nat := 3187345582710458346455

theorem tailTrace_18622 : CollatzResearch.WordTrace tailWord_18622 prefixEnd_18622 3187345582710458346455 := by
  unfold tailWord_18622
  simp only [CollatzResearch.WordTrace]
  refine ⟨84900017317893653688265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 452800092362099486337413 84900017317893653688265)
  ·
    refine ⟨63675012988420240266199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84900017317893653688265 63675012988420240266199)
    ·
      refine ⟨95512519482630360399299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63675012988420240266199 95512519482630360399299)
      ·
        refine ⟨143268779223945540598949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95512519482630360399299 143268779223945540598949)
        ·
          refine ⟨26862896104489788862303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143268779223945540598949 26862896104489788862303)
          ·
            refine ⟨40294344156734683293455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26862896104489788862303 40294344156734683293455)
            ·
              refine ⟨60441516235102024940183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40294344156734683293455 60441516235102024940183)
              ·
                refine ⟨90662274352653037410275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60441516235102024940183 90662274352653037410275)
                ·
                  refine ⟨135993411528979556115413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90662274352653037410275 135993411528979556115413)
                  ·
                    refine ⟨3187345582710458346455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 135993411528979556115413 3187345582710458346455)
                    ·
                      rfl

theorem cell23_18622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_18622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18622 prefixEnd_18622 := by exact prefixLift 18622
  have htrace : WordTrace (prefixWord ++ tailWord_18622) baseStart_18622 baseEnd_18622 := by
    simpa [prefixWord, tailWord_18622, baseEnd_18622] using wordTrace_append hprefix tailTrace_18622
  have hstable : (prefixWord ++ tailWord_18622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18622).length < 2 ^ (prefixWord ++ tailWord_18622).sum := by decide
  have hdescent : baseEnd_18622 < baseStart_18622 := by decide
  rcases family_descends (prefixWord ++ tailWord_18622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18626 : List Nat := [3, 5, 1, 1, 1, 1, 1, 5, 5]
def baseStart_18626 : Nat := 118140960795 + 18626 * 2 ^ 59
def prefixEnd_18626 : Nat := 4983230072969 + 3 ^ 40 * 18626 * 2
def baseEnd_18626 : Nat := 1062676741194373265483

theorem tailTrace_18626 : CollatzResearch.WordTrace tailWord_18626 prefixEnd_18626 1062676741194373265483 := by
  unfold tailWord_18626
  simp only [CollatzResearch.WordTrace]
  refine ⟨169836507632164478162933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 452897353685771941767821 169836507632164478162933)
  ·
    refine ⟨15922172590515419827775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169836507632164478162933 15922172590515419827775)
    ·
      refine ⟨23883258885773129741663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15922172590515419827775 23883258885773129741663)
      ·
        refine ⟨35824888328659694612495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23883258885773129741663 35824888328659694612495)
        ·
          refine ⟨53737332492989541918743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35824888328659694612495 53737332492989541918743)
          ·
            refine ⟨80605998739484312878115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53737332492989541918743 80605998739484312878115)
            ·
              refine ⟨120908998109226469317173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80605998739484312878115 120908998109226469317173)
              ·
                refine ⟨11335218572739981498485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120908998109226469317173 11335218572739981498485)
                ·
                  refine ⟨1062676741194373265483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11335218572739981498485 1062676741194373265483)
                  ·
                    rfl

theorem cell23_18626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_18626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18626 prefixEnd_18626 := by exact prefixLift 18626
  have htrace : WordTrace (prefixWord ++ tailWord_18626) baseStart_18626 baseEnd_18626 := by
    simpa [prefixWord, tailWord_18626, baseEnd_18626] using wordTrace_append hprefix tailTrace_18626
  have hstable : (prefixWord ++ tailWord_18626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18626).length < 2 ^ (prefixWord ++ tailWord_18626).sum := by decide
  have hdescent : baseEnd_18626 < baseStart_18626 := by decide
  rcases family_descends (prefixWord ++ tailWord_18626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18635 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 5, 4]
def baseStart_18635 : Nat := 118140960795 + 18635 * 2 ^ 59
def prefixEnd_18635 : Nat := 4983230072969 + 3 ^ 40 * 18635 * 2
def baseEnd_18635 : Nat := 3189570665546608058935

theorem tailTrace_18635 : CollatzResearch.WordTrace tailWord_18635 prefixEnd_18635 3189570665546608058935 := by
  unfold tailWord_18635
  simp only [CollatzResearch.WordTrace]
  refine ⟨679674287496052449729359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 453116191664034966486239 679674287496052449729359)
  ·
    refine ⟨1019511431244078674594039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 679674287496052449729359 1019511431244078674594039)
    ·
      refine ⟨1529267146866118011891059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1019511431244078674594039 1529267146866118011891059)
      ·
        refine ⟨2293900720299177017836589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1529267146866118011891059 2293900720299177017836589)
        ·
          refine ⟨860212770112191381688721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2293900720299177017836589 860212770112191381688721)
          ·
            refine ⟨645159577584143536266541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860212770112191381688721 645159577584143536266541)
            ·
              refine ⟨241934841594053826099953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 645159577584143536266541 241934841594053826099953)
              ·
                refine ⟨181451131195540369574965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241934841594053826099953 181451131195540369574965)
                ·
                  refine ⟨17011043549581909647653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 181451131195540369574965 17011043549581909647653)
                  ·
                    refine ⟨3189570665546608058935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17011043549581909647653 3189570665546608058935)
                    ·
                      rfl

theorem cell23_18635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 4].length) (baseStart_18635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18635 prefixEnd_18635 := by exact prefixLift 18635
  have htrace : WordTrace (prefixWord ++ tailWord_18635) baseStart_18635 baseEnd_18635 := by
    simpa [prefixWord, tailWord_18635, baseEnd_18635] using wordTrace_append hprefix tailTrace_18635
  have hstable : (prefixWord ++ tailWord_18635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18635).length < 2 ^ (prefixWord ++ tailWord_18635).sum := by decide
  have hdescent : baseEnd_18635 < baseStart_18635 := by decide
  rcases family_descends (prefixWord ++ tailWord_18635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18675 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 3]
def baseStart_18675 : Nat := 118140960795 + 18675 * 2 ^ 59
def prefixEnd_18675 : Nat := 4983230072969 + 3 ^ 40 * 18675 * 2
def baseEnd_18675 : Nat := 9589251222819667676621

theorem tailTrace_18675 : CollatzResearch.WordTrace tailWord_18675 prefixEnd_18675 9589251222819667676621 := by
  unfold tailWord_18675
  simp only [CollatzResearch.WordTrace]
  refine ⟨681133207351139281185479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 454088804900759520790319 681133207351139281185479)
  ·
    refine ⟨1021699811026708921778219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 681133207351139281185479 1021699811026708921778219)
    ·
      refine ⟨1532549716540063382667329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1021699811026708921778219 1532549716540063382667329)
      ·
        refine ⟨1149412287405047537000497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1532549716540063382667329 1149412287405047537000497)
        ·
          refine ⟨862059215553785652750373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1149412287405047537000497 862059215553785652750373)
          ·
            refine ⟨161636102916334809890695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 862059215553785652750373 161636102916334809890695)
            ·
              refine ⟨242454154374502214836043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161636102916334809890695 242454154374502214836043)
              ·
                refine ⟨363681231561753322254065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242454154374502214836043 363681231561753322254065)
                ·
                  refine ⟨272760923671314991690549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363681231561753322254065 272760923671314991690549)
                  ·
                    refine ⟨25571336594185780470989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 272760923671314991690549 25571336594185780470989)
                    ·
                      refine ⟨9589251222819667676621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 25571336594185780470989 9589251222819667676621)
                      ·
                        rfl

theorem cell23_18675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 3].length) (baseStart_18675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18675 prefixEnd_18675 := by exact prefixLift 18675
  have htrace : WordTrace (prefixWord ++ tailWord_18675) baseStart_18675 baseEnd_18675 := by
    simpa [prefixWord, tailWord_18675, baseEnd_18675] using wordTrace_append hprefix tailTrace_18675
  have hstable : (prefixWord ++ tailWord_18675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18675).length < 2 ^ (prefixWord ++ tailWord_18675).sum := by decide
  have hdescent : baseEnd_18675 < baseStart_18675 := by decide
  rcases family_descends (prefixWord ++ tailWord_18675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18709 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_18709 : Nat := 118140960795 + 18709 * 2 ^ 59
def prefixEnd_18709 : Nat := 4983230072969 + 3 ^ 40 * 18709 * 2
def baseEnd_18709 : Nat := 9606709565072534651465

theorem tailTrace_18709 : CollatzResearch.WordTrace tailWord_18709 prefixEnd_18709 9606709565072534651465 := by
  unfold tailWord_18709
  simp only [CollatzResearch.WordTrace]
  refine ⟨682373289227963087923181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 454915526151975391948787 682373289227963087923181)
  ·
    refine ⟨255889983460486157971193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 682373289227963087923181 255889983460486157971193)
    ·
      refine ⟨191917487595364618478395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255889983460486157971193 191917487595364618478395)
      ·
        refine ⟨287876231393046927717593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191917487595364618478395 287876231393046927717593)
        ·
          refine ⟨215907173544785195788195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287876231393046927717593 215907173544785195788195)
          ·
            refine ⟨323860760317177793682293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215907173544785195788195 323860760317177793682293)
            ·
              refine ⟨30361946279735418157715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 323860760317177793682293 30361946279735418157715)
              ·
                refine ⟨45542919419603127236573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30361946279735418157715 45542919419603127236573)
                ·
                  refine ⟨17078594782351172713715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45542919419603127236573 17078594782351172713715)
                  ·
                    refine ⟨25617892173526759070573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17078594782351172713715 25617892173526759070573)
                    ·
                      refine ⟨9606709565072534651465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 25617892173526759070573 9606709565072534651465)
                      ·
                        rfl

theorem cell23_18709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_18709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18709 prefixEnd_18709 := by exact prefixLift 18709
  have htrace : WordTrace (prefixWord ++ tailWord_18709) baseStart_18709 baseEnd_18709 := by
    simpa [prefixWord, tailWord_18709, baseEnd_18709] using wordTrace_append hprefix tailTrace_18709
  have hstable : (prefixWord ++ tailWord_18709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18709).length < 2 ^ (prefixWord ++ tailWord_18709).sum := by decide
  have hdescent : baseEnd_18709 < baseStart_18709 := by decide
  rcases family_descends (prefixWord ++ tailWord_18709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18732 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 2, 6, 2]
def baseStart_18732 : Nat := 118140960795 + 18732 * 2 ^ 59
def prefixEnd_18732 : Nat := 4983230072969 + 3 ^ 40 * 18732 * 2
def baseEnd_18732 : Nat := 9618519620125944663859

theorem tailTrace_18732 : CollatzResearch.WordTrace tailWord_18732 prefixEnd_18732 9618519620125944663859 := by
  unfold tailWord_18732
  simp only [CollatzResearch.WordTrace]
  refine ⟨341606084072319008005225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 455474778763092010673633 341606084072319008005225)
  ·
    refine ⟨256204563054239256003919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 341606084072319008005225 256204563054239256003919)
    ·
      refine ⟨384306844581358884005879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256204563054239256003919 384306844581358884005879)
      ·
        refine ⟨576460266872038326008819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384306844581358884005879 576460266872038326008819)
        ·
          refine ⟨864690400308057489013229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576460266872038326008819 864690400308057489013229)
          ·
            refine ⟨324258900115521558379961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 864690400308057489013229 324258900115521558379961)
            ·
              refine ⟨243194175086641168784971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324258900115521558379961 243194175086641168784971)
              ·
                refine ⟨364791262629961753177457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243194175086641168784971 364791262629961753177457)
                ·
                  refine ⟨273593446972471314883093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364791262629961753177457 273593446972471314883093)
                  ·
                    refine ⟨12824692826834592885145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 273593446972471314883093 12824692826834592885145)
                    ·
                      refine ⟨9618519620125944663859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 12824692826834592885145 9618519620125944663859)
                      ·
                        rfl

theorem cell23_18732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 6, 2].length) (baseStart_18732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18732 prefixEnd_18732 := by exact prefixLift 18732
  have htrace : WordTrace (prefixWord ++ tailWord_18732) baseStart_18732 baseEnd_18732 := by
    simpa [prefixWord, tailWord_18732, baseEnd_18732] using wordTrace_append hprefix tailTrace_18732
  have hstable : (prefixWord ++ tailWord_18732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18732).length < 2 ^ (prefixWord ++ tailWord_18732).sum := by decide
  have hdescent : baseEnd_18732 < baseStart_18732 := by decide
  rcases family_descends (prefixWord ++ tailWord_18732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18735 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 5]
def baseStart_18735 : Nat := 118140960795 + 18735 * 2 ^ 59
def prefixEnd_18735 : Nat := 4983230072969 + 3 ^ 40 * 18735 * 2
def baseEnd_18735 : Nat := 9620060062089432926345

theorem tailTrace_18735 : CollatzResearch.WordTrace tailWord_18735 prefixEnd_18735 9620060062089432926345 := by
  unfold tailWord_18735
  simp only [CollatzResearch.WordTrace]
  refine ⟨683321587133769528369659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 455547724755846352246439 683321587133769528369659)
  ·
    refine ⟨1024982380700654292554489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 683321587133769528369659 1024982380700654292554489)
    ·
      refine ⟨768736785525490719415867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1024982380700654292554489 768736785525490719415867)
      ·
        refine ⟨1153105178288236079123801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768736785525490719415867 1153105178288236079123801)
        ·
          refine ⟨864828883716177059342851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1153105178288236079123801 864828883716177059342851)
          ·
            refine ⟨1297243325574265589014277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864828883716177059342851 1297243325574265589014277)
            ·
              refine ⟨243233123545174797940177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1297243325574265589014277 243233123545174797940177)
              ·
                refine ⟨182424842658881098455133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243233123545174797940177 182424842658881098455133)
                ·
                  refine ⟨68409315997080411920675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182424842658881098455133 68409315997080411920675)
                  ·
                    refine ⟨102613973995620617881013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68409315997080411920675 102613973995620617881013)
                    ·
                      refine ⟨9620060062089432926345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 102613973995620617881013 9620060062089432926345)
                      ·
                        rfl

theorem cell23_18735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_18735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18735 prefixEnd_18735 := by exact prefixLift 18735
  have htrace : WordTrace (prefixWord ++ tailWord_18735) baseStart_18735 baseEnd_18735 := by
    simpa [prefixWord, tailWord_18735, baseEnd_18735] using wordTrace_append hprefix tailTrace_18735
  have hstable : (prefixWord ++ tailWord_18735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18735).length < 2 ^ (prefixWord ++ tailWord_18735).sum := by decide
  have hdescent : baseEnd_18735 < baseStart_18735 := by decide
  rcases family_descends (prefixWord ++ tailWord_18735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18759 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 2, 4]
def baseStart_18759 : Nat := 118140960795 + 18759 * 2 ^ 59
def prefixEnd_18759 : Nat := 4983230072969 + 3 ^ 40 * 18759 * 2
def baseEnd_18759 : Nat := 3210794532599113008745

theorem tailTrace_18759 : CollatzResearch.WordTrace tailWord_18759 prefixEnd_18759 3210794532599113008745 := by
  unfold tailWord_18759
  simp only [CollatzResearch.WordTrace]
  refine ⟨684196939046821627243331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 456131292697881084828887 684196939046821627243331)
  ·
    refine ⟨1026295408570232440864997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 684196939046821627243331 1026295408570232440864997)
    ·
      refine ⟨192430389106918582662187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1026295408570232440864997 192430389106918582662187)
      ·
        refine ⟨288645583660377873993281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192430389106918582662187 288645583660377873993281)
        ·
          refine ⟨216484187745283405494961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288645583660377873993281 216484187745283405494961)
          ·
            refine ⟨162363140808962554121221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216484187745283405494961 162363140808962554121221)
            ·
              refine ⟨30443088901680478897729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162363140808962554121221 30443088901680478897729)
              ·
                refine ⟨22832316676260359173297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30443088901680478897729 22832316676260359173297)
                ·
                  refine ⟨17124237507195269379973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22832316676260359173297 17124237507195269379973)
                  ·
                    refine ⟨3210794532599113008745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17124237507195269379973 3210794532599113008745)
                    ·
                      rfl

theorem cell23_18759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_18759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18759 prefixEnd_18759 := by exact prefixLift 18759
  have htrace : WordTrace (prefixWord ++ tailWord_18759) baseStart_18759 baseEnd_18759 := by
    simpa [prefixWord, tailWord_18759, baseEnd_18759] using wordTrace_append hprefix tailTrace_18759
  have hstable : (prefixWord ++ tailWord_18759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18759).length < 2 ^ (prefixWord ++ tailWord_18759).sum := by decide
  have hdescent : baseEnd_18759 < baseStart_18759 := by decide
  rcases family_descends (prefixWord ++ tailWord_18759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18772 : List Nat := [2, 4, 1, 1, 2, 2, 3, 8]
def baseStart_18772 : Nat := 118140960795 + 18772 * 2 ^ 59
def prefixEnd_18772 : Nat := 4983230072969 + 3 ^ 40 * 18772 * 2
def baseEnd_18772 : Nat := 357002179492806969025

theorem tailTrace_18772 : CollatzResearch.WordTrace tailWord_18772 prefixEnd_18772 357002179492806969025 := by
  unfold tailWord_18772
  simp only [CollatzResearch.WordTrace]
  refine ⟨342335543999862423733285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 456447391999816564977713 342335543999862423733285)
  ·
    refine ⟨64187914499974204449991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 342335543999862423733285 64187914499974204449991)
    ·
      refine ⟨96281871749961306674987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64187914499974204449991 96281871749961306674987)
      ·
        refine ⟨144422807624941960012481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96281871749961306674987 144422807624941960012481)
        ·
          refine ⟨108317105718706470009361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144422807624941960012481 108317105718706470009361)
          ·
            refine ⟨81237829289029852507021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108317105718706470009361 81237829289029852507021)
            ·
              refine ⟨30464185983386194690133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81237829289029852507021 30464185983386194690133)
              ·
                refine ⟨357002179492806969025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 30464185983386194690133 357002179492806969025)
                ·
                  rfl

theorem cell23_18772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 8].length) (baseStart_18772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18772 prefixEnd_18772 := by exact prefixLift 18772
  have htrace : WordTrace (prefixWord ++ tailWord_18772) baseStart_18772 baseEnd_18772 := by
    simpa [prefixWord, tailWord_18772, baseEnd_18772] using wordTrace_append hprefix tailTrace_18772
  have hstable : (prefixWord ++ tailWord_18772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18772).length < 2 ^ (prefixWord ++ tailWord_18772).sum := by decide
  have hdescent : baseEnd_18772 < baseStart_18772 := by decide
  rcases family_descends (prefixWord ++ tailWord_18772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18795 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 5]
def baseStart_18795 : Nat := 118140960795 + 18795 * 2 ^ 59
def prefixEnd_18795 : Nat := 4983230072969 + 3 ^ 40 * 18795 * 2
def baseEnd_18795 : Nat := 9650868901359198176069

theorem tailTrace_18795 : CollatzResearch.WordTrace tailWord_18795 prefixEnd_18795 9650868901359198176069 := by
  unfold tailWord_18795
  simp only [CollatzResearch.WordTrace]
  refine ⟨685509966916399775553839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 457006644610933183702559 685509966916399775553839)
  ·
    refine ⟨1028264950374599663330759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 685509966916399775553839 1028264950374599663330759)
    ·
      refine ⟨1542397425561899494996139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1028264950374599663330759 1542397425561899494996139)
      ·
        refine ⟨2313596138342849242494209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542397425561899494996139 2313596138342849242494209)
        ·
          refine ⟨1735197103757136931870657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2313596138342849242494209 1735197103757136931870657)
          ·
            refine ⟨1301397827817852698902993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1735197103757136931870657 1301397827817852698902993)
            ·
              refine ⟨976048370863389524177245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301397827817852698902993 976048370863389524177245)
              ·
                refine ⟨366018139073771071566467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 976048370863389524177245 366018139073771071566467)
                ·
                  refine ⟨549027208610656607349701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366018139073771071566467 549027208610656607349701)
                  ·
                    refine ⟨102942601614498113878069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 549027208610656607349701 102942601614498113878069)
                    ·
                      refine ⟨9650868901359198176069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 102942601614498113878069 9650868901359198176069)
                      ·
                        rfl

theorem cell23_18795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_18795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18795 prefixEnd_18795 := by exact prefixLift 18795
  have htrace : WordTrace (prefixWord ++ tailWord_18795) baseStart_18795 baseEnd_18795 := by
    simpa [prefixWord, tailWord_18795, baseEnd_18795] using wordTrace_append hprefix tailTrace_18795
  have hstable : (prefixWord ++ tailWord_18795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18795).length < 2 ^ (prefixWord ++ tailWord_18795).sum := by decide
  have hdescent : baseEnd_18795 < baseStart_18795 := by decide
  rcases family_descends (prefixWord ++ tailWord_18795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18815 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 3, 8]
def baseStart_18815 : Nat := 118140960795 + 18815 * 2 ^ 59
def prefixEnd_18815 : Nat := 4983230072969 + 3 ^ 40 * 18815 * 2
def baseEnd_18815 : Nat := 3220379504816373308659

theorem tailTrace_18815 : CollatzResearch.WordTrace tailWord_18815 prefixEnd_18815 3220379504816373308659 := by
  unfold tailWord_18815
  simp only [CollatzResearch.WordTrace]
  refine ⟨686239426843943191281899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 457492951229295460854599 686239426843943191281899)
  ·
    refine ⟨1029359140265914786922849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 686239426843943191281899 1029359140265914786922849)
    ·
      refine ⟨772019355199436090192137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1029359140265914786922849 772019355199436090192137)
      ·
        refine ⟨579014516399577067644103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 772019355199436090192137 579014516399577067644103)
        ·
          refine ⟨868521774599365601466155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579014516399577067644103 868521774599365601466155)
          ·
            refine ⟨1302782661899048402199233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868521774599365601466155 1302782661899048402199233)
            ·
              refine ⟨977086996424286301649425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302782661899048402199233 977086996424286301649425)
              ·
                refine ⟨732815247318214726237069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977086996424286301649425 732815247318214726237069)
                ·
                  refine ⟨274805717744330522338901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732815247318214726237069 274805717744330522338901)
                  ·
                    refine ⟨3220379504816373308659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 274805717744330522338901 3220379504816373308659)
                    ·
                      rfl

theorem cell23_18815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_18815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18815 prefixEnd_18815 := by exact prefixLift 18815
  have htrace : WordTrace (prefixWord ++ tailWord_18815) baseStart_18815 baseEnd_18815 := by
    simpa [prefixWord, tailWord_18815, baseEnd_18815] using wordTrace_append hprefix tailTrace_18815
  have hstable : (prefixWord ++ tailWord_18815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18815).length < 2 ^ (prefixWord ++ tailWord_18815).sum := by decide
  have hdescent : baseEnd_18815 < baseStart_18815 := by decide
  rcases family_descends (prefixWord ++ tailWord_18815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18835 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 10]
def baseStart_18835 : Nat := 118140960795 + 18835 * 2 ^ 59
def prefixEnd_18835 : Nat := 4983230072969 + 3 ^ 40 * 18835 * 2
def baseEnd_18835 : Nat := 9671408127539041675885

theorem tailTrace_18835 : CollatzResearch.WordTrace tailWord_18835 prefixEnd_18835 9671408127539041675885 := by
  unfold tailWord_18835
  simp only [CollatzResearch.WordTrace]
  refine ⟨686968886771486607009959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 457979257847657738006639 686968886771486607009959)
  ·
    refine ⟨1030453330157229910514939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 686968886771486607009959 1030453330157229910514939)
    ·
      refine ⟨1545679995235844865772409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1030453330157229910514939 1545679995235844865772409)
      ·
        refine ⟨1159259996426883649329307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1545679995235844865772409 1159259996426883649329307)
        ·
          refine ⟨1738889994640325473993961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159259996426883649329307 1738889994640325473993961)
          ·
            refine ⟨1304167495980244105495471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1738889994640325473993961 1304167495980244105495471)
            ·
              refine ⟨1956251243970366158243207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304167495980244105495471 1956251243970366158243207)
              ·
                refine ⟨2934376865955549237364811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1956251243970366158243207 2934376865955549237364811)
                ·
                  refine ⟨4401565298933323856047217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934376865955549237364811 4401565298933323856047217)
                  ·
                    refine ⟨3301173974199992892035413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4401565298933323856047217 3301173974199992892035413)
                    ·
                      refine ⟨9671408127539041675885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 3301173974199992892035413 9671408127539041675885)
                      ·
                        rfl

theorem cell23_18835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_18835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18835 prefixEnd_18835 := by exact prefixLift 18835
  have htrace : WordTrace (prefixWord ++ tailWord_18835) baseStart_18835 baseEnd_18835 := by
    simpa [prefixWord, tailWord_18835, baseEnd_18835] using wordTrace_append hprefix tailTrace_18835
  have hstable : (prefixWord ++ tailWord_18835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18835).length < 2 ^ (prefixWord ++ tailWord_18835).sum := by decide
  have hdescent : baseEnd_18835 < baseStart_18835 := by decide
  rcases family_descends (prefixWord ++ tailWord_18835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18852 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_18852 : Nat := 118140960795 + 18852 * 2 ^ 59
def prefixEnd_18852 : Nat := 4983230072969 + 3 ^ 40 * 18852 * 2
def baseEnd_18852 : Nat := 9680137298665475163307

theorem tailTrace_18852 : CollatzResearch.WordTrace tailWord_18852 prefixEnd_18852 9680137298665475163307 := by
  unfold tailWord_18852
  simp only [CollatzResearch.WordTrace]
  refine ⟨343794463854949255189405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 458392618473265673585873 343794463854949255189405)
  ·
    refine ⟨128922923945605970696027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 343794463854949255189405 128922923945605970696027)
    ·
      refine ⟨193384385918408956044041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128922923945605970696027 193384385918408956044041)
      ·
        refine ⟨145038289438806717033031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193384385918408956044041 145038289438806717033031)
        ·
          refine ⟨217557434158210075549547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145038289438806717033031 217557434158210075549547)
          ·
            refine ⟨326336151237315113324321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217557434158210075549547 326336151237315113324321)
            ·
              refine ⟨244752113427986334993241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326336151237315113324321 244752113427986334993241)
              ·
                refine ⟨183564085070989751244931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244752113427986334993241 183564085070989751244931)
                ·
                  refine ⟨275346127606484626867397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183564085070989751244931 275346127606484626867397)
                  ·
                    refine ⟨51627398926215867537637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 275346127606484626867397 51627398926215867537637)
                    ·
                      refine ⟨9680137298665475163307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 51627398926215867537637 9680137298665475163307)
                      ·
                        rfl

theorem cell23_18852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_18852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18852 prefixEnd_18852 := by exact prefixLift 18852
  have htrace : WordTrace (prefixWord ++ tailWord_18852) baseStart_18852 baseEnd_18852 := by
    simpa [prefixWord, tailWord_18852, baseEnd_18852] using wordTrace_append hprefix tailTrace_18852
  have hstable : (prefixWord ++ tailWord_18852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18852).length < 2 ^ (prefixWord ++ tailWord_18852).sum := by decide
  have hdescent : baseEnd_18852 < baseStart_18852 := by decide
  rcases family_descends (prefixWord ++ tailWord_18852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18929 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_18929 : Nat := 118140960795 + 18929 * 2 ^ 59
def prefixEnd_18929 : Nat := 4983230072969 + 3 ^ 40 * 18929 * 2
def baseEnd_18929 : Nat := 9719675309061673900453

theorem tailTrace_18929 : CollatzResearch.WordTrace tailWord_18929 prefixEnd_18929 9719675309061673900453 := by
  unfold tailWord_18929
  simp only [CollatzResearch.WordTrace]
  refine ⟨690397348430940660931841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 460264898953960440621227 690397348430940660931841)
  ·
    refine ⟨517798011323205495698881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 690397348430940660931841 517798011323205495698881)
    ·
      refine ⟨388348508492404121774161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 517798011323205495698881 388348508492404121774161)
      ·
        refine ⟨291261381369303091330621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388348508492404121774161 291261381369303091330621)
        ·
          refine ⟨109223018013488659248983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291261381369303091330621 109223018013488659248983)
          ·
            refine ⟨163834527020232988873475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109223018013488659248983 163834527020232988873475)
            ·
              refine ⟨245751790530349483310213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163834527020232988873475 245751790530349483310213)
              ·
                refine ⟨46078460724440528120665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245751790530349483310213 46078460724440528120665)
                ·
                  refine ⟨34558845543330396090499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46078460724440528120665 34558845543330396090499)
                  ·
                    refine ⟨51838268314995594135749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34558845543330396090499 51838268314995594135749)
                    ·
                      refine ⟨9719675309061673900453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 51838268314995594135749 9719675309061673900453)
                      ·
                        rfl

theorem cell23_18929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_18929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18929 prefixEnd_18929 := by exact prefixLift 18929
  have htrace : WordTrace (prefixWord ++ tailWord_18929) baseStart_18929 baseEnd_18929 := by
    simpa [prefixWord, tailWord_18929, baseEnd_18929] using wordTrace_append hprefix tailTrace_18929
  have hstable : (prefixWord ++ tailWord_18929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18929).length < 2 ^ (prefixWord ++ tailWord_18929).sum := by decide
  have hdescent : baseEnd_18929 < baseStart_18929 := by decide
  rcases family_descends (prefixWord ++ tailWord_18929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18930 : List Nat := [3, 2, 1, 4, 2, 2, 2, 2, 5]
def baseStart_18930 : Nat := 118140960795 + 18930 * 2 ^ 59
def prefixEnd_18930 : Nat := 4983230072969 + 3 ^ 40 * 18930 * 2
def baseEnd_18930 : Nat := 1080020976635129998661

theorem tailTrace_18930 : CollatzResearch.WordTrace tailWord_18930 prefixEnd_18930 1080020976635129998661 := by
  unfold tailWord_18930
  simp only [CollatzResearch.WordTrace]
  refine ⟨172608455356829457929561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 460289214284878554478829 172608455356829457929561)
  ·
    refine ⟨129456341517622093447171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172608455356829457929561 129456341517622093447171)
    ·
      refine ⟨194184512276433140170757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129456341517622093447171 194184512276433140170757)
      ·
        refine ⟨36409596051831213782017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194184512276433140170757 36409596051831213782017)
        ·
          refine ⟨27307197038873410336513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36409596051831213782017 27307197038873410336513)
          ·
            refine ⟨20480397779155057752385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27307197038873410336513 20480397779155057752385)
            ·
              refine ⟨15360298334366293314289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20480397779155057752385 15360298334366293314289)
              ·
                refine ⟨11520223750774719985717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15360298334366293314289 11520223750774719985717)
                ·
                  refine ⟨1080020976635129998661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11520223750774719985717 1080020976635129998661)
                  ·
                    rfl

theorem cell23_18930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_18930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18930 prefixEnd_18930 := by exact prefixLift 18930
  have htrace : WordTrace (prefixWord ++ tailWord_18930) baseStart_18930 baseEnd_18930 := by
    simpa [prefixWord, tailWord_18930, baseEnd_18930] using wordTrace_append hprefix tailTrace_18930
  have hstable : (prefixWord ++ tailWord_18930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18930).length < 2 ^ (prefixWord ++ tailWord_18930).sum := by decide
  have hdescent : baseEnd_18930 < baseStart_18930 := by decide
  rcases family_descends (prefixWord ++ tailWord_18930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18949 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 4, 2, 3]
def baseStart_18949 : Nat := 118140960795 + 18949 * 2 ^ 59
def prefixEnd_18949 : Nat := 4983230072969 + 3 ^ 40 * 18949 * 2
def baseEnd_18949 : Nat := 9729944922151595650361

theorem tailTrace_18949 : CollatzResearch.WordTrace tailWord_18949 prefixEnd_18949 9729944922151595650361 := by
  unfold tailWord_18949
  simp only [CollatzResearch.WordTrace]
  refine ⟨691126808358484076659901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 460751205572322717773267 691126808358484076659901)
  ·
    refine ⟨259172553134431528747463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 691126808358484076659901 259172553134431528747463)
    ·
      refine ⟨388758829701647293121195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259172553134431528747463 388758829701647293121195)
      ·
        refine ⟨583138244552470939681793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388758829701647293121195 583138244552470939681793)
        ·
          refine ⟨437353683414353204761345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583138244552470939681793 437353683414353204761345)
          ·
            refine ⟨328015262560764903571009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437353683414353204761345 328015262560764903571009)
            ·
              refine ⟨246011446920573677678257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328015262560764903571009 246011446920573677678257)
              ·
                refine ⟨184508585190430258258693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246011446920573677678257 184508585190430258258693)
                ·
                  refine ⟨34595359723205673423505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184508585190430258258693 34595359723205673423505)
                  ·
                    refine ⟨25946519792404255067629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34595359723205673423505 25946519792404255067629)
                    ·
                      refine ⟨9729944922151595650361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 25946519792404255067629 9729944922151595650361)
                      ·
                        rfl

theorem cell23_18949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_18949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18949 prefixEnd_18949 := by exact prefixLift 18949
  have htrace : WordTrace (prefixWord ++ tailWord_18949) baseStart_18949 baseEnd_18949 := by
    simpa [prefixWord, tailWord_18949, baseEnd_18949] using wordTrace_append hprefix tailTrace_18949
  have hstable : (prefixWord ++ tailWord_18949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18949).length < 2 ^ (prefixWord ++ tailWord_18949).sum := by decide
  have hdescent : baseEnd_18949 < baseStart_18949 := by decide
  rcases family_descends (prefixWord ++ tailWord_18949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18952 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 10]
def baseStart_18952 : Nat := 118140960795 + 18952 * 2 ^ 59
def prefixEnd_18952 : Nat := 4983230072969 + 3 ^ 40 * 18952 * 2
def baseEnd_18952 : Nat := 1081276151568342656983

theorem tailTrace_18952 : CollatzResearch.WordTrace tailWord_18952 prefixEnd_18952 1081276151568342656983 := by
  unfold tailWord_18952
  simp only [CollatzResearch.WordTrace]
  refine ⟨345618113673807794509555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 460824151565077059346073 345618113673807794509555)
  ·
    refine ⟨518427170510711691764333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 345618113673807794509555 518427170510711691764333)
    ·
      refine ⟨194410188941516884411625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 518427170510711691764333 194410188941516884411625)
      ·
        refine ⟨145807641706137663308719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194410188941516884411625 145807641706137663308719)
        ·
          refine ⟨218711462559206494963079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145807641706137663308719 218711462559206494963079)
          ·
            refine ⟨328067193838809742444619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218711462559206494963079 328067193838809742444619)
            ·
              refine ⟨492100790758214613666929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328067193838809742444619 492100790758214613666929)
              ·
                refine ⟨369075593068660960250197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492100790758214613666929 369075593068660960250197)
                ·
                  refine ⟨1081276151568342656983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 369075593068660960250197 1081276151568342656983)
                  ·
                    rfl

theorem cell23_18952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 10].length) (baseStart_18952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18952 prefixEnd_18952 := by exact prefixLift 18952
  have htrace : WordTrace (prefixWord ++ tailWord_18952) baseStart_18952 baseEnd_18952 := by
    simpa [prefixWord, tailWord_18952, baseEnd_18952] using wordTrace_append hprefix tailTrace_18952
  have hstable : (prefixWord ++ tailWord_18952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18952).length < 2 ^ (prefixWord ++ tailWord_18952).sum := by decide
  have hdescent : baseEnd_18952 < baseStart_18952 := by decide
  rcases family_descends (prefixWord ++ tailWord_18952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18956 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 3, 4]
def baseStart_18956 : Nat := 118140960795 + 18956 * 2 ^ 59
def prefixEnd_18956 : Nat := 4983230072969 + 3 ^ 40 * 18956 * 2
def baseEnd_18956 : Nat := 3244513095577689420943

theorem tailTrace_18956 : CollatzResearch.WordTrace tailWord_18956 prefixEnd_18956 3244513095577689420943 := by
  unfold tailWord_18956
  simp only [CollatzResearch.WordTrace]
  refine ⟨345691059666562136082361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 460921412888749514776481 345691059666562136082361)
  ·
    refine ⟨259268294749921602061771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 345691059666562136082361 259268294749921602061771)
    ·
      refine ⟨388902442124882403092657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259268294749921602061771 388902442124882403092657)
      ·
        refine ⟨291676831593661802319493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388902442124882403092657 291676831593661802319493)
        ·
          refine ⟨54689405923811587934905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291676831593661802319493 54689405923811587934905)
          ·
            refine ⟨41017054442858690951179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54689405923811587934905 41017054442858690951179)
            ·
              refine ⟨61525581664288036426769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41017054442858690951179 61525581664288036426769)
              ·
                refine ⟨46144186248216027320077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61525581664288036426769 46144186248216027320077)
                ·
                  refine ⟨17304069843081010245029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46144186248216027320077 17304069843081010245029)
                  ·
                    refine ⟨3244513095577689420943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17304069843081010245029 3244513095577689420943)
                    ·
                      rfl

theorem cell23_18956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_18956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18956 prefixEnd_18956 := by exact prefixLift 18956
  have htrace : WordTrace (prefixWord ++ tailWord_18956) baseStart_18956 baseEnd_18956 := by
    simpa [prefixWord, tailWord_18956, baseEnd_18956] using wordTrace_append hprefix tailTrace_18956
  have hstable : (prefixWord ++ tailWord_18956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18956).length < 2 ^ (prefixWord ++ tailWord_18956).sum := by decide
  have hdescent : baseEnd_18956 < baseStart_18956 := by decide
  rcases family_descends (prefixWord ++ tailWord_18956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18973 : List Nat := [1, 4, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_18973 : Nat := 118140960795 + 18973 * 2 ^ 59
def prefixEnd_18973 : Nat := 4983230072969 + 3 ^ 40 * 18973 * 2
def baseEnd_18973 : Nat := 3247422819286500583417

theorem tailTrace_18973 : CollatzResearch.WordTrace tailWord_18973 prefixEnd_18973 3247422819286500583417 := by
  unfold tailWord_18973
  simp only [CollatzResearch.WordTrace]
  refine ⟨692002160271536175533573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 461334773514357450355715 692002160271536175533573)
  ·
    refine ⟨129750405050913032912545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 692002160271536175533573 129750405050913032912545)
    ·
      refine ⟨97312803788184774684409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129750405050913032912545 97312803788184774684409)
      ·
        refine ⟨72984602841138581013307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97312803788184774684409 72984602841138581013307)
        ·
          refine ⟨109476904261707871519961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72984602841138581013307 109476904261707871519961)
          ·
            refine ⟨82107678196280903639971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109476904261707871519961 82107678196280903639971)
            ·
              refine ⟨123161517294421355459957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82107678196280903639971 123161517294421355459957)
              ·
                refine ⟨11546392246352002074371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123161517294421355459957 11546392246352002074371)
                ·
                  refine ⟨17319588369528003111557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11546392246352002074371 17319588369528003111557)
                  ·
                    refine ⟨3247422819286500583417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17319588369528003111557 3247422819286500583417)
                    ·
                      rfl

theorem cell23_18973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_18973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18973 prefixEnd_18973 := by exact prefixLift 18973
  have htrace : WordTrace (prefixWord ++ tailWord_18973) baseStart_18973 baseEnd_18973 := by
    simpa [prefixWord, tailWord_18973, baseEnd_18973] using wordTrace_append hprefix tailTrace_18973
  have hstable : (prefixWord ++ tailWord_18973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18973).length < 2 ^ (prefixWord ++ tailWord_18973).sum := by decide
  have hdescent : baseEnd_18973 < baseStart_18973 := by decide
  rcases family_descends (prefixWord ++ tailWord_18973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18986 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 6]
def baseStart_18986 : Nat := 118140960795 + 18986 * 2 ^ 59
def prefixEnd_18986 : Nat := 4983230072969 + 3 ^ 40 * 18986 * 2
def baseEnd_18986 : Nat := 1083215967374216765299

theorem tailTrace_18986 : CollatzResearch.WordTrace tailWord_18986 prefixEnd_18986 1083215967374216765299 := by
  unfold tailWord_18986
  simp only [CollatzResearch.WordTrace]
  refine ⟨173119077306109848939203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 461650872816292930504541 173119077306109848939203)
  ·
    refine ⟨259678615959164773408805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173119077306109848939203 259678615959164773408805)
    ·
      refine ⟨48689740492343395014151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259678615959164773408805 48689740492343395014151)
      ·
        refine ⟨73034610738515092521227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48689740492343395014151 73034610738515092521227)
        ·
          refine ⟨109551916107772638781841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73034610738515092521227 109551916107772638781841)
          ·
            refine ⟨82163937080829479086381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109551916107772638781841 82163937080829479086381)
            ·
              refine ⟨30811476405311054657393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82163937080829479086381 30811476405311054657393)
              ·
                refine ⟨23108607303983290993045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30811476405311054657393 23108607303983290993045)
                ·
                  refine ⟨1083215967374216765299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23108607303983290993045 1083215967374216765299)
                  ·
                    rfl

theorem cell23_18986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_18986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_18986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_18986 prefixEnd_18986 := by exact prefixLift 18986
  have htrace : WordTrace (prefixWord ++ tailWord_18986) baseStart_18986 baseEnd_18986 := by
    simpa [prefixWord, tailWord_18986, baseEnd_18986] using wordTrace_append hprefix tailTrace_18986
  have hstable : (prefixWord ++ tailWord_18986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18986).length < 2 ^ (prefixWord ++ tailWord_18986).sum := by decide
  have hdescent : baseEnd_18986 < baseStart_18986 := by decide
  rcases family_descends (prefixWord ++ tailWord_18986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19019 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 4]
def baseStart_19019 : Nat := 118140960795 + 19019 * 2 ^ 59
def prefixEnd_19019 : Nat := 4983230072969 + 3 ^ 40 * 19019 * 2
def baseEnd_19019 : Nat := 9765888567966321775039

theorem tailTrace_19019 : CollatzResearch.WordTrace tailWord_19019 prefixEnd_19019 9765888567966321775039 := by
  unfold tailWord_19019
  simp only [CollatzResearch.WordTrace]
  refine ⟨693679918104886031708111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 462453278736590687805407 693679918104886031708111)
  ·
    refine ⟨1040519877157329047562167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 693679918104886031708111 1040519877157329047562167)
    ·
      refine ⟨1560779815735993571343251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1040519877157329047562167 1560779815735993571343251)
      ·
        refine ⟨2341169723603990357014877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1560779815735993571343251 2341169723603990357014877)
        ·
          refine ⟨877938646351496383880579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2341169723603990357014877 877938646351496383880579)
          ·
            refine ⟨1316907969527244575820869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877938646351496383880579 1316907969527244575820869)
            ·
              refine ⟨246920244286358357966413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1316907969527244575820869 246920244286358357966413)
              ·
                refine ⟨92595091607384384237405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246920244286358357966413 92595091607384384237405)
                ·
                  refine ⟨34723159352769144089027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92595091607384384237405 34723159352769144089027)
                  ·
                    refine ⟨52084739029153716133541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34723159352769144089027 52084739029153716133541)
                    ·
                      refine ⟨9765888567966321775039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 52084739029153716133541 9765888567966321775039)
                      ·
                        rfl

theorem cell23_19019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 4].length) (baseStart_19019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19019 prefixEnd_19019 := by exact prefixLift 19019
  have htrace : WordTrace (prefixWord ++ tailWord_19019) baseStart_19019 baseEnd_19019 := by
    simpa [prefixWord, tailWord_19019, baseEnd_19019] using wordTrace_append hprefix tailTrace_19019
  have hstable : (prefixWord ++ tailWord_19019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19019).length < 2 ^ (prefixWord ++ tailWord_19019).sum := by decide
  have hdescent : baseEnd_19019 < baseStart_19019 := by decide
  rcases family_descends (prefixWord ++ tailWord_19019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19029 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_19029 : Nat := 118140960795 + 19029 * 2 ^ 59
def prefixEnd_19029 : Nat := 4983230072969 + 3 ^ 40 * 19029 * 2
def baseEnd_19029 : Nat := 3257007791503760883331

theorem tailTrace_19029 : CollatzResearch.WordTrace tailWord_19029 prefixEnd_19029 3257007791503760883331 := by
  unfold tailWord_19029
  simp only [CollatzResearch.WordTrace]
  refine ⟨694044648068657739572141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 462696432045771826381427 694044648068657739572141)
  ·
    refine ⟨260266743025746652339553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 694044648068657739572141 260266743025746652339553)
    ·
      refine ⟨195200057269309989254665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260266743025746652339553 195200057269309989254665)
      ·
        refine ⟨146400042951982491940999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195200057269309989254665 146400042951982491940999)
        ·
          refine ⟨219600064427973737911499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146400042951982491940999 219600064427973737911499)
          ·
            refine ⟨329400096641960606867249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219600064427973737911499 329400096641960606867249)
            ·
              refine ⟨247050072481470455150437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329400096641960606867249 247050072481470455150437)
              ·
                refine ⟨46321888590275710340707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247050072481470455150437 46321888590275710340707)
                ·
                  refine ⟨69482832885413565511061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46321888590275710340707 69482832885413565511061)
                  ·
                    refine ⟨3257007791503760883331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69482832885413565511061 3257007791503760883331)
                    ·
                      rfl

theorem cell23_19029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_19029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19029 prefixEnd_19029 := by exact prefixLift 19029
  have htrace : WordTrace (prefixWord ++ tailWord_19029) baseStart_19029 baseEnd_19029 := by
    simpa [prefixWord, tailWord_19029, baseEnd_19029] using wordTrace_append hprefix tailTrace_19029
  have hstable : (prefixWord ++ tailWord_19029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19029).length < 2 ^ (prefixWord ++ tailWord_19029).sum := by decide
  have hdescent : baseEnd_19029 < baseStart_19029 := by decide
  rcases family_descends (prefixWord ++ tailWord_19029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19063 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 2, 4]
def baseStart_19063 : Nat := 118140960795 + 19063 * 2 ^ 59
def prefixEnd_19063 : Nat := 4983230072969 + 3 ^ 40 * 19063 * 2
def baseEnd_19063 : Nat := 3262827238921383208279

theorem tailTrace_19063 : CollatzResearch.WordTrace tailWord_19063 prefixEnd_19063 3262827238921383208279 := by
  unfold tailWord_19063
  simp only [CollatzResearch.WordTrace]
  refine ⟨695284729945481546309843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 463523153296987697539895 695284729945481546309843)
  ·
    refine ⟨1042927094918222319464765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 695284729945481546309843 1042927094918222319464765)
    ·
      refine ⟨391097660594333369799287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1042927094918222319464765 391097660594333369799287)
      ·
        refine ⟨586646490891500054698931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391097660594333369799287 586646490891500054698931)
        ·
          refine ⟨879969736337250082048397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586646490891500054698931 879969736337250082048397)
          ·
            refine ⟨329988651126468780768149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 879969736337250082048397 329988651126468780768149)
            ·
              refine ⟨15468218021553224098507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 329988651126468780768149 15468218021553224098507)
              ·
                refine ⟨23202327032329836147761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15468218021553224098507 23202327032329836147761)
                ·
                  refine ⟨17401745274247377110821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23202327032329836147761 17401745274247377110821)
                  ·
                    refine ⟨3262827238921383208279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17401745274247377110821 3262827238921383208279)
                    ·
                      rfl

theorem cell23_19063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_19063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19063 prefixEnd_19063 := by exact prefixLift 19063
  have htrace : WordTrace (prefixWord ++ tailWord_19063) baseStart_19063 baseEnd_19063 := by
    simpa [prefixWord, tailWord_19063, baseEnd_19063] using wordTrace_append hprefix tailTrace_19063
  have hstable : (prefixWord ++ tailWord_19063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19063).length < 2 ^ (prefixWord ++ tailWord_19063).sum := by decide
  have hdescent : baseEnd_19063 < baseStart_19063 := by decide
  rcases family_descends (prefixWord ++ tailWord_19063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19119 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 1, 8]
def baseStart_19119 : Nat := 118140960795 + 19119 * 2 ^ 59
def prefixEnd_19119 : Nat := 4983230072969 + 3 ^ 40 * 19119 * 2
def baseEnd_19119 : Nat := 3272412211138643508193

theorem tailTrace_19119 : CollatzResearch.WordTrace tailWord_19119 prefixEnd_19119 3272412211138643508193 := by
  unfold tailWord_19119
  simp only [CollatzResearch.WordTrace]
  refine ⟨697327217742603110348411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 464884811828402073565607 697327217742603110348411)
  ·
    refine ⟨1045990826613904665522617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 697327217742603110348411 1045990826613904665522617)
    ·
      refine ⟨784493119960428499141963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1045990826613904665522617 784493119960428499141963)
      ·
        refine ⟨1176739679940642748712945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784493119960428499141963 1176739679940642748712945)
        ·
          refine ⟨882554759955482061534709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1176739679940642748712945 882554759955482061534709)
          ·
            refine ⟨82739508745826443268879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 882554759955482061534709 82739508745826443268879)
            ·
              refine ⟨124109263118739664903319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82739508745826443268879 124109263118739664903319)
              ·
                refine ⟨186163894678109497354979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124109263118739664903319 186163894678109497354979)
                ·
                  refine ⟨279245842017164246032469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186163894678109497354979 279245842017164246032469)
                  ·
                    refine ⟨3272412211138643508193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 279245842017164246032469 3272412211138643508193)
                    ·
                      rfl

theorem cell23_19119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_19119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19119 prefixEnd_19119 := by exact prefixLift 19119
  have htrace : WordTrace (prefixWord ++ tailWord_19119) baseStart_19119 baseEnd_19119 := by
    simpa [prefixWord, tailWord_19119, baseEnd_19119] using wordTrace_append hprefix tailTrace_19119
  have hstable : (prefixWord ++ tailWord_19119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19119).length < 2 ^ (prefixWord ++ tailWord_19119).sum := by decide
  have hdescent : baseEnd_19119 < baseStart_19119 := by decide
  rcases family_descends (prefixWord ++ tailWord_19119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19154 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_19154 : Nat := 118140960795 + 19154 * 2 ^ 59
def prefixEnd_19154 : Nat := 4983230072969 + 3 ^ 40 * 19154 * 2
def baseEnd_19154 : Nat := 9835208456323293586919

theorem tailTrace_19154 : CollatzResearch.WordTrace tailWord_19154 prefixEnd_19154 9835208456323293586919 := by
  unfold tailWord_19154
  simp only [CollatzResearch.WordTrace]
  refine ⟨174650943153951021968129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 465735848410536058581677 174650943153951021968129)
  ·
    refine ⟨130988207365463266476097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174650943153951021968129 130988207365463266476097)
    ·
      refine ⟨98241155524097449857073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130988207365463266476097 98241155524097449857073)
      ·
        refine ⟨73680866643073087392805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98241155524097449857073 73680866643073087392805)
        ·
          refine ⟨13815162495576203886151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73680866643073087392805 13815162495576203886151)
          ·
            refine ⟨20722743743364305829227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13815162495576203886151 20722743743364305829227)
            ·
              refine ⟨31084115615046458743841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20722743743364305829227 31084115615046458743841)
              ·
                refine ⟨23313086711284844057881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31084115615046458743841 23313086711284844057881)
                ·
                  refine ⟨17484815033463633043411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23313086711284844057881 17484815033463633043411)
                  ·
                    refine ⟨26227222550195449565117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17484815033463633043411 26227222550195449565117)
                    ·
                      refine ⟨9835208456323293586919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 26227222550195449565117 9835208456323293586919)
                      ·
                        rfl

theorem cell23_19154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_19154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19154 prefixEnd_19154 := by exact prefixLift 19154
  have htrace : WordTrace (prefixWord ++ tailWord_19154) baseStart_19154 baseEnd_19154 := by
    simpa [prefixWord, tailWord_19154, baseEnd_19154] using wordTrace_append hprefix tailTrace_19154
  have hstable : (prefixWord ++ tailWord_19154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19154).length < 2 ^ (prefixWord ++ tailWord_19154).sum := by decide
  have hdescent : baseEnd_19154 < baseStart_19154 := by decide
  rcases family_descends (prefixWord ++ tailWord_19154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19160 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 4, 2, 2]
def baseStart_19160 : Nat := 118140960795 + 19160 * 2 ^ 59
def prefixEnd_19160 : Nat := 4983230072969 + 3 ^ 40 * 19160 * 2
def baseEnd_19160 : Nat := 9838289340250270111891

theorem tailTrace_19160 : CollatzResearch.WordTrace tailWord_19160 prefixEnd_19160 9838289340250270111891 := by
  unfold tailWord_19160
  simp only [CollatzResearch.WordTrace]
  refine ⟨349411305297033556295467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 465881740396044741727289 349411305297033556295467)
  ·
    refine ⟨524116957945550334443201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 349411305297033556295467 524116957945550334443201)
    ·
      refine ⟨393087718459162750832401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 524116957945550334443201 393087718459162750832401)
      ·
        refine ⟨294815788844372063124301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393087718459162750832401 294815788844372063124301)
        ·
          refine ⟨110555920816639523671613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294815788844372063124301 110555920816639523671613)
          ·
            refine ⟨41458470306239821376855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110555920816639523671613 41458470306239821376855)
            ·
              refine ⟨62187705459359732065283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41458470306239821376855 62187705459359732065283)
              ·
                refine ⟨93281558189039598097925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62187705459359732065283 93281558189039598097925)
                ·
                  refine ⟨17490292160444924643361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93281558189039598097925 17490292160444924643361)
                  ·
                    refine ⟨13117719120333693482521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17490292160444924643361 13117719120333693482521)
                    ·
                      refine ⟨9838289340250270111891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13117719120333693482521 9838289340250270111891)
                      ·
                        rfl

theorem cell23_19160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_19160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19160 prefixEnd_19160 := by exact prefixLift 19160
  have htrace : WordTrace (prefixWord ++ tailWord_19160) baseStart_19160 baseEnd_19160 := by
    simpa [prefixWord, tailWord_19160, baseEnd_19160] using wordTrace_append hprefix tailTrace_19160
  have hstable : (prefixWord ++ tailWord_19160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19160).length < 2 ^ (prefixWord ++ tailWord_19160).sum := by decide
  have hdescent : baseEnd_19160 < baseStart_19160 := by decide
  rcases family_descends (prefixWord ++ tailWord_19160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19196 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_19196 : Nat := 118140960795 + 19196 * 2 ^ 59
def prefixEnd_19196 : Nat := 4983230072969 + 3 ^ 40 * 19196 * 2
def baseEnd_19196 : Nat := 3285591547937376420575

theorem tailTrace_19196 : CollatzResearch.WordTrace tailWord_19196 prefixEnd_19196 3285591547937376420575 := by
  unfold tailWord_19196
  simp only [CollatzResearch.WordTrace]
  refine ⟨350067819231822630450721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 466757092309096840600961 350067819231822630450721)
  ·
    refine ⟨262550864423866972838041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 350067819231822630450721 262550864423866972838041)
    ·
      refine ⟨196913148317900229628531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262550864423866972838041 196913148317900229628531)
      ·
        refine ⟨295369722476850344442797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196913148317900229628531 295369722476850344442797)
        ·
          refine ⟨110763645928818879166049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295369722476850344442797 110763645928818879166049)
          ·
            refine ⟨83072734446614159374537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110763645928818879166049 83072734446614159374537)
            ·
              refine ⟨62304550834960619530903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83072734446614159374537 62304550834960619530903)
              ·
                refine ⟨93456826252440929296355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62304550834960619530903 93456826252440929296355)
                ·
                  refine ⟨140185239378661393944533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93456826252440929296355 140185239378661393944533)
                  ·
                    refine ⟨3285591547937376420575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 140185239378661393944533 3285591547937376420575)
                    ·
                      rfl

theorem cell23_19196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_19196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19196 prefixEnd_19196 := by exact prefixLift 19196
  have htrace : WordTrace (prefixWord ++ tailWord_19196) baseStart_19196 baseEnd_19196 := by
    simpa [prefixWord, tailWord_19196, baseEnd_19196] using wordTrace_append hprefix tailTrace_19196
  have hstable : (prefixWord ++ tailWord_19196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19196).length < 2 ^ (prefixWord ++ tailWord_19196).sum := by decide
  have hdescent : baseEnd_19196 < baseStart_19196 := by decide
  rcases family_descends (prefixWord ++ tailWord_19196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19223 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 5]
def baseStart_19223 : Nat := 118140960795 + 19223 * 2 ^ 59
def prefixEnd_19223 : Nat := 4983230072969 + 3 ^ 40 * 19223 * 2
def baseEnd_19223 : Nat := 9870638621483523624101

theorem tailTrace_19223 : CollatzResearch.WordTrace tailWord_19223 prefixEnd_19223 9870638621483523624101 := by
  unfold tailWord_19223
  simp only [CollatzResearch.WordTrace]
  refine ⟨701120409365828872134323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 467413606243885914756215 701120409365828872134323)
  ·
    refine ⟨1051680614048743308201485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 701120409365828872134323 1051680614048743308201485)
    ·
      refine ⟨394380230268278740575557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1051680614048743308201485 394380230268278740575557)
      ·
        refine ⟨73946293175302263857917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 394380230268278740575557 73946293175302263857917)
        ·
          refine ⟨27729859940738348946719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73946293175302263857917 27729859940738348946719)
          ·
            refine ⟨41594789911107523420079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27729859940738348946719 41594789911107523420079)
            ·
              refine ⟨62392184866661285130119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41594789911107523420079 62392184866661285130119)
              ·
                refine ⟨93588277299991927695179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62392184866661285130119 93588277299991927695179)
                ·
                  refine ⟨140382415949987891542769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93588277299991927695179 140382415949987891542769)
                  ·
                    refine ⟨105286811962490918657077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 140382415949987891542769 105286811962490918657077)
                    ·
                      refine ⟨9870638621483523624101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 105286811962490918657077 9870638621483523624101)
                      ·
                        rfl

theorem cell23_19223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_19223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19223 prefixEnd_19223 := by exact prefixLift 19223
  have htrace : WordTrace (prefixWord ++ tailWord_19223) baseStart_19223 baseEnd_19223 := by
    simpa [prefixWord, tailWord_19223, baseEnd_19223] using wordTrace_append hprefix tailTrace_19223
  have hstable : (prefixWord ++ tailWord_19223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19223).length < 2 ^ (prefixWord ++ tailWord_19223).sum := by decide
  have hdescent : baseEnd_19223 < baseStart_19223 := by decide
  rcases family_descends (prefixWord ++ tailWord_19223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19233 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 1, 6, 2]
def baseStart_19233 : Nat := 118140960795 + 19233 * 2 ^ 59
def prefixEnd_19233 : Nat := 4983230072969 + 3 ^ 40 * 19233 * 2
def baseEnd_19233 : Nat := 9875773428028484499055

theorem tailTrace_19233 : CollatzResearch.WordTrace tailWord_19233 prefixEnd_19233 9875773428028484499055 := by
  unfold tailWord_19233
  simp only [CollatzResearch.WordTrace]
  refine ⟨701485139329600579998353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 467656759553067053332235 701485139329600579998353)
  ·
    refine ⟨526113854497200434998765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 701485139329600579998353 526113854497200434998765)
    ·
      refine ⟨197292695436450163124537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 526113854497200434998765 197292695436450163124537)
      ·
        refine ⟨147969521577337622343403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197292695436450163124537 147969521577337622343403)
        ·
          refine ⟨221954282366006433515105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147969521577337622343403 221954282366006433515105)
          ·
            refine ⟨166465711774504825136329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221954282366006433515105 166465711774504825136329)
            ·
              refine ⟨124849283830878618852247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166465711774504825136329 124849283830878618852247)
              ·
                refine ⟨187273925746317928278371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124849283830878618852247 187273925746317928278371)
                ·
                  refine ⟨280910888619476892417557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187273925746317928278371 280910888619476892417557)
                  ·
                    refine ⟨13167697904037979332073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 280910888619476892417557 13167697904037979332073)
                    ·
                      refine ⟨9875773428028484499055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13167697904037979332073 9875773428028484499055)
                      ·
                        rfl

theorem cell23_19233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_19233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19233 prefixEnd_19233 := by exact prefixLift 19233
  have htrace : WordTrace (prefixWord ++ tailWord_19233) baseStart_19233 baseEnd_19233 := by
    simpa [prefixWord, tailWord_19233, baseEnd_19233] using wordTrace_append hprefix tailTrace_19233
  have hstable : (prefixWord ++ tailWord_19233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19233).length < 2 ^ (prefixWord ++ tailWord_19233).sum := by decide
  have hdescent : baseEnd_19233 < baseStart_19233 := by decide
  rcases family_descends (prefixWord ++ tailWord_19233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19260 : List Nat := [2, 2, 2, 2, 1, 1, 1, 7, 1, 4]
def baseStart_19260 : Nat := 118140960795 + 19260 * 2 ^ 59
def prefixEnd_19260 : Nat := 4983230072969 + 3 ^ 40 * 19260 * 2
def baseEnd_19260 : Nat := 3296545801899959620477

theorem tailTrace_19260 : CollatzResearch.WordTrace tailWord_19260 prefixEnd_19260 3296545801899959620477 := by
  unfold tailWord_19260
  simp only [CollatzResearch.WordTrace]
  refine ⟨351234955115892095615617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 468313273487856127487489 351234955115892095615617)
  ·
    refine ⟨263426216336919071711713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 351234955115892095615617 263426216336919071711713)
    ·
      refine ⟨197569662252689303783785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263426216336919071711713 197569662252689303783785)
      ·
        refine ⟨148177246689516977837839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197569662252689303783785 148177246689516977837839)
        ·
          refine ⟨222265870034275466756759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148177246689516977837839 222265870034275466756759)
          ·
            refine ⟨333398805051413200135139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222265870034275466756759 333398805051413200135139)
            ·
              refine ⟨500098207577119800202709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333398805051413200135139 500098207577119800202709)
              ·
                refine ⟨11721051740088745317251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 500098207577119800202709 11721051740088745317251)
                ·
                  refine ⟨17581577610133117975877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11721051740088745317251 17581577610133117975877)
                  ·
                    refine ⟨3296545801899959620477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17581577610133117975877 3296545801899959620477)
                    ·
                      rfl

theorem cell23_19260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_19260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19260 prefixEnd_19260 := by exact prefixLift 19260
  have htrace : WordTrace (prefixWord ++ tailWord_19260) baseStart_19260 baseEnd_19260 := by
    simpa [prefixWord, tailWord_19260, baseEnd_19260] using wordTrace_append hprefix tailTrace_19260
  have hstable : (prefixWord ++ tailWord_19260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19260).length < 2 ^ (prefixWord ++ tailWord_19260).sum := by decide
  have hdescent : baseEnd_19260 < baseStart_19260 := by decide
  rcases family_descends (prefixWord ++ tailWord_19260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19273 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 6]
def baseStart_19273 : Nat := 118140960795 + 19273 * 2 ^ 59
def prefixEnd_19273 : Nat := 4983230072969 + 3 ^ 40 * 19273 * 2
def baseEnd_19273 : Nat := 1099590294912036444319

theorem tailTrace_19273 : CollatzResearch.WordTrace tailWord_19273 prefixEnd_19273 1099590294912036444319 := by
  unfold tailWord_19273
  simp only [CollatzResearch.WordTrace]
  refine ⟨702944059184687411454473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 468629372789791607636315 702944059184687411454473)
  ·
    refine ⟨527208044388515558590855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 702944059184687411454473 527208044388515558590855)
    ·
      refine ⟨790812066582773337886283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527208044388515558590855 790812066582773337886283)
      ·
        refine ⟨1186218099874160006829425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790812066582773337886283 1186218099874160006829425)
        ·
          refine ⟨889663574905620005122069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1186218099874160006829425 889663574905620005122069)
          ·
            refine ⟨41702980073700937740097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 889663574905620005122069 41702980073700937740097)
            ·
              refine ⟨31277235055275703305073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41702980073700937740097 31277235055275703305073)
              ·
                refine ⟨23457926291456777478805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31277235055275703305073 23457926291456777478805)
                ·
                  refine ⟨1099590294912036444319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23457926291456777478805 1099590294912036444319)
                  ·
                    rfl

theorem cell23_19273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 6].length) (baseStart_19273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19273 prefixEnd_19273 := by exact prefixLift 19273
  have htrace : WordTrace (prefixWord ++ tailWord_19273) baseStart_19273 baseEnd_19273 := by
    simpa [prefixWord, tailWord_19273, baseEnd_19273] using wordTrace_append hprefix tailTrace_19273
  have hstable : (prefixWord ++ tailWord_19273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19273).length < 2 ^ (prefixWord ++ tailWord_19273).sum := by decide
  have hdescent : baseEnd_19273 < baseStart_19273 := by decide
  rcases family_descends (prefixWord ++ tailWord_19273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19283 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 7, 1, 3]
def baseStart_19283 : Nat := 118140960795 + 19283 * 2 ^ 59
def prefixEnd_19283 : Nat := 4983230072969 + 3 ^ 40 * 19283 * 2
def baseEnd_19283 : Nat := 9901447460753288873825

theorem tailTrace_19283 : CollatzResearch.WordTrace tailWord_19283 prefixEnd_19283 9901447460753288873825 := by
  unfold tailWord_19283
  simp only [CollatzResearch.WordTrace]
  refine ⟨703308789148459119318503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 468872526098972746212335 703308789148459119318503)
  ·
    refine ⟨1054963183722688678977755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 703308789148459119318503 1054963183722688678977755)
    ·
      refine ⟨1582444775584033018466633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054963183722688678977755 1582444775584033018466633)
      ·
        refine ⟨1186833581688024763849975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1582444775584033018466633 1186833581688024763849975)
        ·
          refine ⟨1780250372532037145774963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186833581688024763849975 1780250372532037145774963)
          ·
            refine ⟨2670375558798055718662445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780250372532037145774963 2670375558798055718662445)
            ·
              refine ⟨1001390834549270894498417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2670375558798055718662445 1001390834549270894498417)
              ·
                refine ⟨751043125911953170873813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001390834549270894498417 751043125911953170873813)
                ·
                  refine ⟨17602573263561402442355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 751043125911953170873813 17602573263561402442355)
                  ·
                    refine ⟨26403859895342103663533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17602573263561402442355 26403859895342103663533)
                    ·
                      refine ⟨9901447460753288873825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 26403859895342103663533 9901447460753288873825)
                      ·
                        rfl

theorem cell23_19283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 1, 3].length) (baseStart_19283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19283 prefixEnd_19283 := by exact prefixLift 19283
  have htrace : WordTrace (prefixWord ++ tailWord_19283) baseStart_19283 baseEnd_19283 := by
    simpa [prefixWord, tailWord_19283, baseEnd_19283] using wordTrace_append hprefix tailTrace_19283
  have hstable : (prefixWord ++ tailWord_19283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19283).length < 2 ^ (prefixWord ++ tailWord_19283).sum := by decide
  have hdescent : baseEnd_19283 < baseStart_19283 := by decide
  rcases family_descends (prefixWord ++ tailWord_19283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19296 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_19296 : Nat := 118140960795 + 19296 * 2 ^ 59
def prefixEnd_19296 : Nat := 4983230072969 + 3 ^ 40 * 19296 * 2
def baseEnd_19296 : Nat := 9908122709261738011265

theorem tailTrace_19296 : CollatzResearch.WordTrace tailWord_19296 prefixEnd_19296 9908122709261738011265 := by
  unfold tailWord_19296
  simp only [CollatzResearch.WordTrace]
  refine ⟨351891469050681169770871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 469188625400908226361161 351891469050681169770871)
  ·
    refine ⟨527837203576021754656307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 351891469050681169770871 527837203576021754656307)
    ·
      refine ⟨791755805364032631984461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527837203576021754656307 791755805364032631984461)
      ·
        refine ⟨296908427011512236994173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 791755805364032631984461 296908427011512236994173)
        ·
          refine ⟨111340660129317088872815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296908427011512236994173 111340660129317088872815)
          ·
            refine ⟨167010990193975633309223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111340660129317088872815 167010990193975633309223)
            ·
              refine ⟨250516485290963449963835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167010990193975633309223 250516485290963449963835)
              ·
                refine ⟨375774727936445174945753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250516485290963449963835 375774727936445174945753)
                ·
                  refine ⟨281831045952333881209315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375774727936445174945753 281831045952333881209315)
                  ·
                    refine ⟨422746568928500821813973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 281831045952333881209315 422746568928500821813973)
                    ·
                      refine ⟨9908122709261738011265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 422746568928500821813973 9908122709261738011265)
                      ·
                        rfl

theorem cell23_19296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_19296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19296 prefixEnd_19296 := by exact prefixLift 19296
  have htrace : WordTrace (prefixWord ++ tailWord_19296) baseStart_19296 baseEnd_19296 := by
    simpa [prefixWord, tailWord_19296, baseEnd_19296] using wordTrace_append hprefix tailTrace_19296
  have hstable : (prefixWord ++ tailWord_19296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19296).length < 2 ^ (prefixWord ++ tailWord_19296).sum := by decide
  have hdescent : baseEnd_19296 < baseStart_19296 := by decide
  rcases family_descends (prefixWord ++ tailWord_19296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19300 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_19300 : Nat := 118140960795 + 19300 * 2 ^ 59
def prefixEnd_19300 : Nat := 4983230072969 + 3 ^ 40 * 19300 * 2
def baseEnd_19300 : Nat := 9910176631879722361247

theorem tailTrace_19300 : CollatzResearch.WordTrace tailWord_19300 prefixEnd_19300 9910176631879722361247 := by
  unfold tailWord_19300
  simp only [CollatzResearch.WordTrace]
  refine ⟨351964415043435511343677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 469285886724580681791569 351964415043435511343677)
  ·
    refine ⟨131986655641288316753879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 351964415043435511343677 131986655641288316753879)
    ·
      refine ⟨197979983461932475130819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131986655641288316753879 197979983461932475130819)
      ·
        refine ⟨296969975192898712696229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197979983461932475130819 296969975192898712696229)
        ·
          refine ⟨55681870348668508630543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296969975192898712696229 55681870348668508630543)
          ·
            refine ⟨83522805523002762945815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55681870348668508630543 83522805523002762945815)
            ·
              refine ⟨125284208284504144418723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83522805523002762945815 125284208284504144418723)
              ·
                refine ⟨187926312426756216628085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125284208284504144418723 187926312426756216628085)
                ·
                  refine ⟨17618091790008395308883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187926312426756216628085 17618091790008395308883)
                  ·
                    refine ⟨26427137685012592963325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17618091790008395308883 26427137685012592963325)
                    ·
                      refine ⟨9910176631879722361247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 26427137685012592963325 9910176631879722361247)
                      ·
                        rfl

theorem cell23_19300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_19300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19300 prefixEnd_19300 := by exact prefixLift 19300
  have htrace : WordTrace (prefixWord ++ tailWord_19300) baseStart_19300 baseEnd_19300 := by
    simpa [prefixWord, tailWord_19300, baseEnd_19300] using wordTrace_append hprefix tailTrace_19300
  have hstable : (prefixWord ++ tailWord_19300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19300).length < 2 ^ (prefixWord ++ tailWord_19300).sum := by decide
  have hdescent : baseEnd_19300 < baseStart_19300 := by decide
  rcases family_descends (prefixWord ++ tailWord_19300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19303 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 3, 5]
def baseStart_19303 : Nat := 118140960795 + 19303 * 2 ^ 59
def prefixEnd_19303 : Nat := 4983230072969 + 3 ^ 40 * 19303 * 2
def baseEnd_19303 : Nat := 3303905691281070207911

theorem tailTrace_19303 : CollatzResearch.WordTrace tailWord_19303 prefixEnd_19303 3303905691281070207911 := by
  unfold tailWord_19303
  simp only [CollatzResearch.WordTrace]
  refine ⟨704038249076002535046563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 469358832717335023364375 704038249076002535046563)
  ·
    refine ⟨1056057373614003802569845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 704038249076002535046563 1056057373614003802569845)
    ·
      refine ⟨99005378776312856490923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1056057373614003802569845 99005378776312856490923)
      ·
        refine ⟨148508068164469284736385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99005378776312856490923 148508068164469284736385)
        ·
          refine ⟨111381051123351963552289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148508068164469284736385 111381051123351963552289)
          ·
            refine ⟨83535788342513972664217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111381051123351963552289 83535788342513972664217)
            ·
              refine ⟨62651841256885479498163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83535788342513972664217 62651841256885479498163)
              ·
                refine ⟨93977761885328219247245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62651841256885479498163 93977761885328219247245)
                ·
                  refine ⟨35241660706998082217717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93977761885328219247245 35241660706998082217717)
                  ·
                    refine ⟨3303905691281070207911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35241660706998082217717 3303905691281070207911)
                    ·
                      rfl

theorem cell23_19303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_19303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19303 prefixEnd_19303 := by exact prefixLift 19303
  have htrace : WordTrace (prefixWord ++ tailWord_19303) baseStart_19303 baseEnd_19303 := by
    simpa [prefixWord, tailWord_19303, baseEnd_19303] using wordTrace_append hprefix tailTrace_19303
  have hstable : (prefixWord ++ tailWord_19303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19303).length < 2 ^ (prefixWord ++ tailWord_19303).sum := by decide
  have hdescent : baseEnd_19303 < baseStart_19303 := by decide
  rcases family_descends (prefixWord ++ tailWord_19303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19357 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_19357 : Nat := 118140960795 + 19357 * 2 ^ 59
def prefixEnd_19357 : Nat := 4983230072969 + 3 ^ 40 * 19357 * 2
def baseEnd_19357 : Nat := 9939445029185999348485

theorem tailTrace_19357 : CollatzResearch.WordTrace tailWord_19357 prefixEnd_19357 9939445029185999348485 := by
  unfold tailWord_19357
  simp only [CollatzResearch.WordTrace]
  refine ⟨706007790880369757512325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 470671860586913171674883 706007790880369757512325)
  ·
    refine ⟨132376460790069329533561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 706007790880369757512325 132376460790069329533561)
    ·
      refine ⟨99282345592551997150171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132376460790069329533561 99282345592551997150171)
      ·
        refine ⟨148923518388827995725257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99282345592551997150171 148923518388827995725257)
        ·
          refine ⟨111692638791620996793943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148923518388827995725257 111692638791620996793943)
          ·
            refine ⟨167538958187431495190915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111692638791620996793943 167538958187431495190915)
            ·
              refine ⟨251308437281147242786373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167538958187431495190915 251308437281147242786373)
              ·
                refine ⟨47120331990215108022445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251308437281147242786373 47120331990215108022445)
                ·
                  refine ⟨17670124496330665508417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47120331990215108022445 17670124496330665508417)
                  ·
                    refine ⟨13252593372247999131313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17670124496330665508417 13252593372247999131313)
                    ·
                      refine ⟨9939445029185999348485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13252593372247999131313 9939445029185999348485)
                      ·
                        rfl

theorem cell23_19357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_19357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19357 prefixEnd_19357 := by exact prefixLift 19357
  have htrace : WordTrace (prefixWord ++ tailWord_19357) baseStart_19357 baseEnd_19357 := by
    simpa [prefixWord, tailWord_19357, baseEnd_19357] using wordTrace_append hprefix tailTrace_19357
  have hstable : (prefixWord ++ tailWord_19357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19357).length < 2 ^ (prefixWord ++ tailWord_19357).sum := by decide
  have hdescent : baseEnd_19357 < baseStart_19357 := by decide
  rcases family_descends (prefixWord ++ tailWord_19357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19360 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 3]
def baseStart_19360 : Nat := 118140960795 + 19360 * 2 ^ 59
def prefixEnd_19360 : Nat := 4983230072969 + 3 ^ 40 * 19360 * 2
def baseEnd_19360 : Nat := 9940985471149487610971

theorem tailTrace_19360 : CollatzResearch.WordTrace tailWord_19360 prefixEnd_19360 9940985471149487610971 := by
  unfold tailWord_19360
  simp only [CollatzResearch.WordTrace]
  refine ⟨353058604934750634935767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 470744806579667513247689 353058604934750634935767)
  ·
    refine ⟨529587907402125952403651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 353058604934750634935767 529587907402125952403651)
    ·
      refine ⟨794381861103188928605477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 529587907402125952403651 794381861103188928605477)
      ·
        refine ⟨148946598956847924113527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 794381861103188928605477 148946598956847924113527)
        ·
          refine ⟨223419898435271886170291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148946598956847924113527 223419898435271886170291)
          ·
            refine ⟨335129847652907829255437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223419898435271886170291 335129847652907829255437)
            ·
              refine ⟨125673692869840435970789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 335129847652907829255437 125673692869840435970789)
              ·
                refine ⟨23563817413095081744523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125673692869840435970789 23563817413095081744523)
                ·
                  refine ⟨35345726119642622616785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23563817413095081744523 35345726119642622616785)
                  ·
                    refine ⟨26509294589731966962589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35345726119642622616785 26509294589731966962589)
                    ·
                      refine ⟨9940985471149487610971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 26509294589731966962589 9940985471149487610971)
                      ·
                        rfl

theorem cell23_19360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_19360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19360 prefixEnd_19360 := by exact prefixLift 19360
  have htrace : WordTrace (prefixWord ++ tailWord_19360) baseStart_19360 baseEnd_19360 := by
    simpa [prefixWord, tailWord_19360, baseEnd_19360] using wordTrace_append hprefix tailTrace_19360
  have hstable : (prefixWord ++ tailWord_19360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19360).length < 2 ^ (prefixWord ++ tailWord_19360).sum := by decide
  have hdescent : baseEnd_19360 < baseStart_19360 := by decide
  rcases family_descends (prefixWord ++ tailWord_19360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19363 : List Nat := [1, 1, 1, 4, 1, 2, 6, 7]
def baseStart_19363 : Nat := 118140960795 + 19363 * 2 ^ 59
def prefixEnd_19363 : Nat := 4983230072969 + 3 ^ 40 * 19363 * 2
def baseEnd_19363 : Nat := 368241700485665773091

theorem tailTrace_19363 : CollatzResearch.WordTrace tailWord_19363 prefixEnd_19363 368241700485665773091 := by
  unfold tailWord_19363
  simp only [CollatzResearch.WordTrace]
  refine ⟨706226628858632782230743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 470817752572421854820495 706226628858632782230743)
  ·
    refine ⟨1059339943287949173346115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 706226628858632782230743 1059339943287949173346115)
    ·
      refine ⟨1589009914931923760019173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1059339943287949173346115 1589009914931923760019173)
      ·
        refine ⟨297939359049735705003595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1589009914931923760019173 297939359049735705003595)
        ·
          refine ⟨446909038574603557505393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297939359049735705003595 446909038574603557505393)
          ·
            refine ⟨335181778930952668129045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446909038574603557505393 335181778930952668129045)
            ·
              refine ⟨15711645887388406318549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 335181778930952668129045 15711645887388406318549)
              ·
                refine ⟨368241700485665773091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15711645887388406318549 368241700485665773091)
                ·
                  rfl

theorem cell23_19363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 7].length) (baseStart_19363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19363 prefixEnd_19363 := by exact prefixLift 19363
  have htrace : WordTrace (prefixWord ++ tailWord_19363) baseStart_19363 baseEnd_19363 := by
    simpa [prefixWord, tailWord_19363, baseEnd_19363] using wordTrace_append hprefix tailTrace_19363
  have hstable : (prefixWord ++ tailWord_19363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19363).length < 2 ^ (prefixWord ++ tailWord_19363).sum := by decide
  have hdescent : baseEnd_19363 < baseStart_19363 := by decide
  rcases family_descends (prefixWord ++ tailWord_19363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19380 : List Nat := [2, 5, 2, 1, 1, 1, 11]
def baseStart_19380 : Nat := 118140960795 + 19380 * 2 ^ 59
def prefixEnd_19380 : Nat := 4983230072969 + 3 ^ 40 * 19380 * 2
def baseEnd_19380 : Nat := 122855001039992708159

theorem tailTrace_19380 : CollatzResearch.WordTrace tailWord_19380 prefixEnd_19380 122855001039992708159 := by
  unfold tailWord_19380
  simp only [CollatzResearch.WordTrace]
  refine ⟨353423334898522342799797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 471231113198029790399729 353423334898522342799797)
  ·
    refine ⟨33133437646736469637481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 353423334898522342799797 33133437646736469637481)
    ·
      refine ⟨24850078235052352228111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33133437646736469637481 24850078235052352228111)
      ·
        refine ⟨37275117352578528342167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24850078235052352228111 37275117352578528342167)
        ·
          refine ⟨55912676028867792513251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37275117352578528342167 55912676028867792513251)
          ·
            refine ⟨83869014043301688769877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55912676028867792513251 83869014043301688769877)
            ·
              refine ⟨122855001039992708159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 83869014043301688769877 122855001039992708159)
              ·
                rfl

theorem cell23_19380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 11].length) (baseStart_19380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19380 prefixEnd_19380 := by exact prefixLift 19380
  have htrace : WordTrace (prefixWord ++ tailWord_19380) baseStart_19380 baseEnd_19380 := by
    simpa [prefixWord, tailWord_19380, baseEnd_19380] using wordTrace_append hprefix tailTrace_19380
  have hstable : (prefixWord ++ tailWord_19380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19380).length < 2 ^ (prefixWord ++ tailWord_19380).sum := by decide
  have hdescent : baseEnd_19380 < baseStart_19380 := by decide
  rcases family_descends (prefixWord ++ tailWord_19380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19407 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 2, 1, 3]
def baseStart_19407 : Nat := 118140960795 + 19407 * 2 ^ 59
def prefixEnd_19407 : Nat := 4983230072969 + 3 ^ 40 * 19407 * 2
def baseEnd_19407 : Nat := 9965119061910803723255

theorem tailTrace_19407 : CollatzResearch.WordTrace tailWord_19407 prefixEnd_19407 9965119061910803723255 := by
  unfold tailWord_19407
  simp only [CollatzResearch.WordTrace]
  refine ⟨707831440699228296832475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 471887627132818864554983 707831440699228296832475)
  ·
    refine ⟨1061747161048842445248713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 707831440699228296832475 1061747161048842445248713)
    ·
      refine ⟨796310370786631833936535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1061747161048842445248713 796310370786631833936535)
      ·
        refine ⟨1194465556179947750904803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 796310370786631833936535 1194465556179947750904803)
        ·
          refine ⟨1791698334269921626357205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194465556179947750904803 1791698334269921626357205)
          ·
            refine ⟨41992929709451288117747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1791698334269921626357205 41992929709451288117747)
            ·
              refine ⟨62989394564176932176621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41992929709451288117747 62989394564176932176621)
              ·
                refine ⟨23621022961566349566233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62989394564176932176621 23621022961566349566233)
                ·
                  refine ⟨17715767221174762174675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23621022961566349566233 17715767221174762174675)
                  ·
                    refine ⟨26573650831762143262013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17715767221174762174675 26573650831762143262013)
                    ·
                      refine ⟨9965119061910803723255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 26573650831762143262013 9965119061910803723255)
                      ·
                        rfl

theorem cell23_19407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 1, 3].length) (baseStart_19407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19407 prefixEnd_19407 := by exact prefixLift 19407
  have htrace : WordTrace (prefixWord ++ tailWord_19407) baseStart_19407 baseEnd_19407 := by
    simpa [prefixWord, tailWord_19407, baseEnd_19407] using wordTrace_append hprefix tailTrace_19407
  have hstable : (prefixWord ++ tailWord_19407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19407).length < 2 ^ (prefixWord ++ tailWord_19407).sum := by decide
  have hdescent : baseEnd_19407 < baseStart_19407 := by decide
  rcases family_descends (prefixWord ++ tailWord_19407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19417 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 3, 3, 2]
def baseStart_19417 : Nat := 118140960795 + 19417 * 2 ^ 59
def prefixEnd_19417 : Nat := 4983230072969 + 3 ^ 40 * 19417 * 2
def baseEnd_19417 : Nat := 9970253868455764598209

theorem tailTrace_19417 : CollatzResearch.WordTrace tailWord_19417 prefixEnd_19417 9970253868455764598209 := by
  unfold tailWord_19417
  simp only [CollatzResearch.WordTrace]
  refine ⟨708196170663000004696505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 472130780442000003131003 708196170663000004696505)
  ·
    refine ⟨531147127997250003522379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 708196170663000004696505 531147127997250003522379)
    ·
      refine ⟨796720691995875005283569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 531147127997250003522379 796720691995875005283569)
      ·
        refine ⟨597540518996906253962677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 796720691995875005283569 597540518996906253962677)
        ·
          refine ⟨56019423655959961309001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 597540518996906253962677 56019423655959961309001)
          ·
            refine ⟨42014567741969970981751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56019423655959961309001 42014567741969970981751)
            ·
              refine ⟨63021851612954956472627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42014567741969970981751 63021851612954956472627)
              ·
                refine ⟨94532777419432434708941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63021851612954956472627 94532777419432434708941)
                ·
                  refine ⟨35449791532287163015853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94532777419432434708941 35449791532287163015853)
                  ·
                    refine ⟨13293671824607686130945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35449791532287163015853 13293671824607686130945)
                    ·
                      refine ⟨9970253868455764598209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13293671824607686130945 9970253868455764598209)
                      ·
                        rfl

theorem cell23_19417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 3, 2].length) (baseStart_19417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19417 prefixEnd_19417 := by exact prefixLift 19417
  have htrace : WordTrace (prefixWord ++ tailWord_19417) baseStart_19417 baseEnd_19417 := by
    simpa [prefixWord, tailWord_19417, baseEnd_19417] using wordTrace_append hprefix tailTrace_19417
  have hstable : (prefixWord ++ tailWord_19417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19417).length < 2 ^ (prefixWord ++ tailWord_19417).sum := by decide
  have hdescent : baseEnd_19417 < baseStart_19417 := by decide
  rcases family_descends (prefixWord ++ tailWord_19417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19433 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 6, 4, 3]
def baseStart_19433 : Nat := 118140960795 + 19433 * 2 ^ 59
def prefixEnd_19433 : Nat := 4983230072969 + 3 ^ 40 * 19433 * 2
def baseEnd_19433 : Nat := 9978469558927701998135

theorem tailTrace_19433 : CollatzResearch.WordTrace tailWord_19433 prefixEnd_19433 9978469558927701998135 := by
  unfold tailWord_19433
  simp only [CollatzResearch.WordTrace]
  refine ⟨708779738605034737278953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 472519825736689824852635 708779738605034737278953)
  ·
    refine ⟨531584803953776052959215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 708779738605034737278953 531584803953776052959215)
    ·
      refine ⟨797377205930664079438823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 531584803953776052959215 797377205930664079438823)
      ·
        refine ⟨1196065808895996119158235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797377205930664079438823 1196065808895996119158235)
        ·
          refine ⟨1794098713343994178737353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1196065808895996119158235 1794098713343994178737353)
          ·
            refine ⟨1345574035007995634053015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1794098713343994178737353 1345574035007995634053015)
            ·
              refine ⟨2018361052511993451079523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345574035007995634053015 2018361052511993451079523)
              ·
                refine ⟨3027541578767990176619285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018361052511993451079523 3027541578767990176619285)
                ·
                  refine ⟨141916011504749539529029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3027541578767990176619285 141916011504749539529029)
                  ·
                    refine ⟨26609252157140538661693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141916011504749539529029 26609252157140538661693)
                    ·
                      refine ⟨9978469558927701998135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 26609252157140538661693 9978469558927701998135)
                      ·
                        rfl

theorem cell23_19433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4, 3].length) (baseStart_19433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19433 prefixEnd_19433 := by exact prefixLift 19433
  have htrace : WordTrace (prefixWord ++ tailWord_19433) baseStart_19433 baseEnd_19433 := by
    simpa [prefixWord, tailWord_19433, baseEnd_19433] using wordTrace_append hprefix tailTrace_19433
  have hstable : (prefixWord ++ tailWord_19433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19433).length < 2 ^ (prefixWord ++ tailWord_19433).sum := by decide
  have hdescent : baseEnd_19433 < baseStart_19433 := by decide
  rcases family_descends (prefixWord ++ tailWord_19433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19442 : List Nat := [3, 2, 1, 5, 2, 1, 2, 2, 1, 2, 2]
def baseStart_19442 : Nat := 118140960795 + 19442 * 2 ^ 59
def prefixEnd_19442 : Nat := 4983230072969 + 3 ^ 40 * 19442 * 2
def baseEnd_19442 : Nat := 9983090884818166785595

theorem tailTrace_19442 : CollatzResearch.WordTrace tailWord_19442 prefixEnd_19442 9983090884818166785595 := by
  unfold tailWord_19442
  simp only [CollatzResearch.WordTrace]
  refine ⟨177276998893107318589145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 472738663714952849571053 177276998893107318589145)
  ·
    refine ⟨132957749169830488941859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177276998893107318589145 132957749169830488941859)
    ·
      refine ⟨199436623754745733412789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132957749169830488941859 199436623754745733412789)
      ·
        refine ⟨18697183477007412507449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199436623754745733412789 18697183477007412507449)
        ·
          refine ⟨14022887607755559380587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18697183477007412507449 14022887607755559380587)
          ·
            refine ⟨21034331411633339070881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14022887607755559380587 21034331411633339070881)
            ·
              refine ⟨15775748558725004303161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21034331411633339070881 15775748558725004303161)
              ·
                refine ⟨11831811419043753227371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15775748558725004303161 11831811419043753227371)
                ·
                  refine ⟨17747717128565629841057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11831811419043753227371 17747717128565629841057)
                  ·
                    refine ⟨13310787846424222380793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17747717128565629841057 13310787846424222380793)
                    ·
                      refine ⟨9983090884818166785595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13310787846424222380793 9983090884818166785595)
                      ·
                        rfl

theorem cell23_19442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_19442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19442 prefixEnd_19442 := by exact prefixLift 19442
  have htrace : WordTrace (prefixWord ++ tailWord_19442) baseStart_19442 baseEnd_19442 := by
    simpa [prefixWord, tailWord_19442, baseEnd_19442] using wordTrace_append hprefix tailTrace_19442
  have hstable : (prefixWord ++ tailWord_19442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19442).length < 2 ^ (prefixWord ++ tailWord_19442).sum := by decide
  have hdescent : baseEnd_19442 < baseStart_19442 := by decide
  rcases family_descends (prefixWord ++ tailWord_19442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19453 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 7]
def baseStart_19453 : Nat := 118140960795 + 19453 * 2 ^ 59
def prefixEnd_19453 : Nat := 4983230072969 + 3 ^ 40 * 19453 * 2
def baseEnd_19453 : Nat := 1109859908001958194227

theorem tailTrace_19453 : CollatzResearch.WordTrace tailWord_19453 prefixEnd_19453 1109859908001958194227 := by
  unfold tailWord_19453
  simp only [CollatzResearch.WordTrace]
  refine ⟨709509198532578153007013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 473006132355052102004675 709509198532578153007013)
  ·
    refine ⟨133032974724858403688815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 709509198532578153007013 133032974724858403688815)
    ·
      refine ⟨199549462087287605533223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133032974724858403688815 199549462087287605533223)
      ·
        refine ⟨299324193130931408299835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199549462087287605533223 299324193130931408299835)
        ·
          refine ⟨448986289696397112449753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299324193130931408299835 448986289696397112449753)
          ·
            refine ⟨336739717272297834337315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448986289696397112449753 336739717272297834337315)
            ·
              refine ⟨505109575908446751505973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336739717272297834337315 505109575908446751505973)
              ·
                refine ⟨47354022741416882953685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 505109575908446751505973 47354022741416882953685)
                ·
                  refine ⟨1109859908001958194227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47354022741416882953685 1109859908001958194227)
                  ·
                    rfl

theorem cell23_19453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_19453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19453 prefixEnd_19453 := by exact prefixLift 19453
  have htrace : WordTrace (prefixWord ++ tailWord_19453) baseStart_19453 baseEnd_19453 := by
    simpa [prefixWord, tailWord_19453, baseEnd_19453] using wordTrace_append hprefix tailTrace_19453
  have hstable : (prefixWord ++ tailWord_19453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19453).length < 2 ^ (prefixWord ++ tailWord_19453).sum := by decide
  have hdescent : baseEnd_19453 < baseStart_19453 := by decide
  rcases family_descends (prefixWord ++ tailWord_19453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19464 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 2, 2, 2]
def baseStart_19464 : Nat := 118140960795 + 19464 * 2 ^ 59
def prefixEnd_19464 : Nat := 4983230072969 + 3 ^ 40 * 19464 * 2
def baseEnd_19464 : Nat := 9994387459217080710493

theorem tailTrace_19464 : CollatzResearch.WordTrace tailWord_19464 prefixEnd_19464 9994387459217080710493 := by
  unfold tailWord_19464
  simp only [CollatzResearch.WordTrace]
  refine ⟨354955200746363515828723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 473273600995151354438297 354955200746363515828723)
  ·
    refine ⟨532432801119545273743085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 354955200746363515828723 532432801119545273743085)
    ·
      refine ⟨199662300419829477653657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 532432801119545273743085 199662300419829477653657)
      ·
        refine ⟨149746725314872108240243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199662300419829477653657 149746725314872108240243)
        ·
          refine ⟨224620087972308162360365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149746725314872108240243 224620087972308162360365)
          ·
            refine ⟨84232532989615560885137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224620087972308162360365 84232532989615560885137)
            ·
              refine ⟨63174399742211670663853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84232532989615560885137 63174399742211670663853)
              ·
                refine ⟨23690399903329376498945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63174399742211670663853 23690399903329376498945)
                ·
                  refine ⟨17767799927497032374209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23690399903329376498945 17767799927497032374209)
                  ·
                    refine ⟨13325849945622774280657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17767799927497032374209 13325849945622774280657)
                    ·
                      refine ⟨9994387459217080710493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13325849945622774280657 9994387459217080710493)
                      ·
                        rfl

theorem cell23_19464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_19464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19464 prefixEnd_19464 := by exact prefixLift 19464
  have htrace : WordTrace (prefixWord ++ tailWord_19464) baseStart_19464 baseEnd_19464 := by
    simpa [prefixWord, tailWord_19464, baseEnd_19464] using wordTrace_append hprefix tailTrace_19464
  have hstable : (prefixWord ++ tailWord_19464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19464).length < 2 ^ (prefixWord ++ tailWord_19464).sum := by decide
  have hdescent : baseEnd_19464 < baseStart_19464 := by decide
  rcases family_descends (prefixWord ++ tailWord_19464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19470 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_19470 : Nat := 118140960795 + 19470 * 2 ^ 59
def prefixEnd_19470 : Nat := 4983230072969 + 3 ^ 40 * 19470 * 2
def baseEnd_19470 : Nat := 1110829815904895248385

theorem tailTrace_19470 : CollatzResearch.WordTrace tailWord_19470 prefixEnd_19470 1110829815904895248385 := by
  unfold tailWord_19470
  simp only [CollatzResearch.WordTrace]
  refine ⟨88766154933873757046983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 473419492980660037583909 88766154933873757046983)
  ·
    refine ⟨133149232400810635570475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88766154933873757046983 133149232400810635570475)
    ·
      refine ⟨199723848601215953355713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133149232400810635570475 199723848601215953355713)
      ·
        refine ⟨149792886450911965016785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199723848601215953355713 149792886450911965016785)
        ·
          refine ⟨112344664838183973762589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149792886450911965016785 112344664838183973762589)
          ·
            refine ⟨42129249314318990160971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112344664838183973762589 42129249314318990160971)
            ·
              refine ⟨63193873971478485241457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42129249314318990160971 63193873971478485241457)
              ·
                refine ⟨47395405478608863931093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63193873971478485241457 47395405478608863931093)
                ·
                  refine ⟨1110829815904895248385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47395405478608863931093 1110829815904895248385)
                  ·
                    rfl

theorem cell23_19470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_19470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19470 prefixEnd_19470 := by exact prefixLift 19470
  have htrace : WordTrace (prefixWord ++ tailWord_19470) baseStart_19470 baseEnd_19470 := by
    simpa [prefixWord, tailWord_19470, baseEnd_19470] using wordTrace_append hprefix tailTrace_19470
  have hstable : (prefixWord ++ tailWord_19470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19470).length < 2 ^ (prefixWord ++ tailWord_19470).sum := by decide
  have hdescent : baseEnd_19470 < baseStart_19470 := by decide
  rcases family_descends (prefixWord ++ tailWord_19470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19487 : List Nat := [1, 1, 2, 4, 1, 4, 2, 3, 5]
def baseStart_19487 : Nat := 118140960795 + 19487 * 2 ^ 59
def prefixEnd_19487 : Nat := 4983230072969 + 3 ^ 40 * 19487 * 2
def baseEnd_19487 : Nat := 1111799723807832302543

theorem tailTrace_19487 : CollatzResearch.WordTrace tailWord_19487 prefixEnd_19487 1111799723807832302543 := by
  unfold tailWord_19487
  simp only [CollatzResearch.WordTrace]
  refine ⟨710749280409401959744715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 473832853606267973163143 710749280409401959744715)
  ·
    refine ⟨1066123920614102939617073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 710749280409401959744715 1066123920614102939617073)
    ·
      refine ⟨799592940460577204712805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1066123920614102939617073 799592940460577204712805)
      ·
        refine ⟨149923676336358225883651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 799592940460577204712805 149923676336358225883651)
        ·
          refine ⟨224885514504537338825477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149923676336358225883651 224885514504537338825477)
          ·
            refine ⟨42166033969600751029777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224885514504537338825477 42166033969600751029777)
            ·
              refine ⟨31624525477200563272333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42166033969600751029777 31624525477200563272333)
              ·
                refine ⟨11859197053950211227125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31624525477200563272333 11859197053950211227125)
                ·
                  refine ⟨1111799723807832302543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11859197053950211227125 1111799723807832302543)
                  ·
                    rfl

theorem cell23_19487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 5].length) (baseStart_19487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19487 prefixEnd_19487 := by exact prefixLift 19487
  have htrace : WordTrace (prefixWord ++ tailWord_19487) baseStart_19487 baseEnd_19487 := by
    simpa [prefixWord, tailWord_19487, baseEnd_19487] using wordTrace_append hprefix tailTrace_19487
  have hstable : (prefixWord ++ tailWord_19487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19487).length < 2 ^ (prefixWord ++ tailWord_19487).sum := by decide
  have hdescent : baseEnd_19487 < baseStart_19487 := by decide
  rcases family_descends (prefixWord ++ tailWord_19487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19498 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_19498 : Nat := 118140960795 + 19498 * 2 ^ 59
def prefixEnd_19498 : Nat := 4983230072969 + 3 ^ 40 * 19498 * 2
def baseEnd_19498 : Nat := 10011845801469947685337

theorem tailTrace_19498 : CollatzResearch.WordTrace tailWord_19498 prefixEnd_19498 10011845801469947685337 := by
  unfold tailWord_19498
  simp only [CollatzResearch.WordTrace]
  refine ⟨177787620842387709598787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 474100322246367225596765 177787620842387709598787)
  ·
    refine ⟨266681431263581564398181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177787620842387709598787 266681431263581564398181)
    ·
      refine ⟨50002768361921543324659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266681431263581564398181 50002768361921543324659)
      ·
        refine ⟨75004152542882314986989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50002768361921543324659 75004152542882314986989)
        ·
          refine ⟨28126557203580868120121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75004152542882314986989 28126557203580868120121)
          ·
            refine ⟨21094917902685651090091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28126557203580868120121 21094917902685651090091)
            ·
              refine ⟨31642376854028476635137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21094917902685651090091 31642376854028476635137)
              ·
                refine ⟨23731782640521357476353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31642376854028476635137 23731782640521357476353)
                ·
                  refine ⟨17798836980391018107265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23731782640521357476353 17798836980391018107265)
                  ·
                    refine ⟨13349127735293263580449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17798836980391018107265 13349127735293263580449)
                    ·
                      refine ⟨10011845801469947685337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13349127735293263580449 10011845801469947685337)
                      ·
                        rfl

theorem cell23_19498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_19498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19498 prefixEnd_19498 := by exact prefixLift 19498
  have htrace : WordTrace (prefixWord ++ tailWord_19498) baseStart_19498 baseEnd_19498 := by
    simpa [prefixWord, tailWord_19498, baseEnd_19498] using wordTrace_append hprefix tailTrace_19498
  have hstable : (prefixWord ++ tailWord_19498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19498).length < 2 ^ (prefixWord ++ tailWord_19498).sum := by decide
  have hdescent : baseEnd_19498 < baseStart_19498 := by decide
  rcases family_descends (prefixWord ++ tailWord_19498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19554 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_19554 : Nat := 118140960795 + 19554 * 2 ^ 59
def prefixEnd_19554 : Nat := 4983230072969 + 3 ^ 40 * 19554 * 2
def baseEnd_19554 : Nat := 10040600718121728585079

theorem tailTrace_19554 : CollatzResearch.WordTrace tailWord_19554 prefixEnd_19554 10040600718121728585079 := by
  unfold tailWord_19554
  simp only [CollatzResearch.WordTrace]
  refine ⟨178298242791668100608429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 475461980777781601622477 178298242791668100608429)
  ·
    refine ⟨66861841046875537728161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178298242791668100608429 66861841046875537728161)
    ·
      refine ⟨50146380785156653296121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66861841046875537728161 50146380785156653296121)
      ·
        refine ⟨37609785588867489972091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50146380785156653296121 37609785588867489972091)
        ·
          refine ⟨56414678383301234958137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37609785588867489972091 56414678383301234958137)
          ·
            refine ⟨42311008787475926218603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56414678383301234958137 42311008787475926218603)
            ·
              refine ⟨63466513181213889327905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42311008787475926218603 63466513181213889327905)
              ·
                refine ⟨47599884885910416995929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63466513181213889327905 47599884885910416995929)
                ·
                  refine ⟨35699913664432812746947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47599884885910416995929 35699913664432812746947)
                  ·
                    refine ⟨53549870496649219120421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35699913664432812746947 53549870496649219120421)
                    ·
                      refine ⟨10040600718121728585079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 53549870496649219120421 10040600718121728585079)
                      ·
                        rfl

theorem cell23_19554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_19554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19554 prefixEnd_19554 := by exact prefixLift 19554
  have htrace : WordTrace (prefixWord ++ tailWord_19554) baseStart_19554 baseEnd_19554 := by
    simpa [prefixWord, tailWord_19554, baseEnd_19554] using wordTrace_append hprefix tailTrace_19554
  have hstable : (prefixWord ++ tailWord_19554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19554).length < 2 ^ (prefixWord ++ tailWord_19554).sum := by decide
  have hdescent : baseEnd_19554 < baseStart_19554 := by decide
  rcases family_descends (prefixWord ++ tailWord_19554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19557 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 2, 2, 3]
def baseStart_19557 : Nat := 118140960795 + 19557 * 2 ^ 59
def prefixEnd_19557 : Nat := 4983230072969 + 3 ^ 40 * 19557 * 2
def baseEnd_19557 : Nat := 10042141160085216847565

theorem tailTrace_19557 : CollatzResearch.WordTrace tailWord_19557 prefixEnd_19557 10042141160085216847565 := by
  unfold tailWord_19557
  simp only [CollatzResearch.WordTrace]
  refine ⟨713302390155803914792925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 475534926770535943195283 713302390155803914792925)
  ·
    refine ⟨267488396308426468047347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 713302390155803914792925 267488396308426468047347)
    ·
      refine ⟨401232594462639702071021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267488396308426468047347 401232594462639702071021)
      ·
        refine ⟨150462222923489888276633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 401232594462639702071021 150462222923489888276633)
        ·
          refine ⟨112846667192617416207475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150462222923489888276633 112846667192617416207475)
          ·
            refine ⟨169270000788926124311213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112846667192617416207475 169270000788926124311213)
            ·
              refine ⟨63476250295847296616705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169270000788926124311213 63476250295847296616705)
              ·
                refine ⟨47607187721885472462529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63476250295847296616705 47607187721885472462529)
                ·
                  refine ⟨35705390791414104346897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47607187721885472462529 35705390791414104346897)
                  ·
                    refine ⟨26779043093560578260173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35705390791414104346897 26779043093560578260173)
                    ·
                      refine ⟨10042141160085216847565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 26779043093560578260173 10042141160085216847565)
                      ·
                        rfl

theorem cell23_19557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_19557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19557 prefixEnd_19557 := by exact prefixLift 19557
  have htrace : WordTrace (prefixWord ++ tailWord_19557) baseStart_19557 baseEnd_19557 := by
    simpa [prefixWord, tailWord_19557, baseEnd_19557] using wordTrace_append hprefix tailTrace_19557
  have hstable : (prefixWord ++ tailWord_19557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19557).length < 2 ^ (prefixWord ++ tailWord_19557).sum := by decide
  have hdescent : baseEnd_19557 < baseStart_19557 := by decide
  rcases family_descends (prefixWord ++ tailWord_19557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19577 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 6]
def baseStart_19577 : Nat := 118140960795 + 19577 * 2 ^ 59
def prefixEnd_19577 : Nat := 4983230072969 + 3 ^ 40 * 19577 * 2
def baseEnd_19577 : Nat := 1116934530352793177497

theorem tailTrace_19577 : CollatzResearch.WordTrace tailWord_19577 prefixEnd_19577 1116934530352793177497 := by
  unfold tailWord_19577
  simp only [CollatzResearch.WordTrace]
  refine ⟨714031850083347330520985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 476021233388898220347323 714031850083347330520985)
  ·
    refine ⟨535523887562510497890739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 714031850083347330520985 535523887562510497890739)
    ·
      refine ⟨803285831343765746836109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535523887562510497890739 803285831343765746836109)
      ·
        refine ⟨301232186753912155063541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 803285831343765746836109 301232186753912155063541)
        ·
          refine ⟨28240517508179264537207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 301232186753912155063541 28240517508179264537207)
          ·
            refine ⟨42360776262268896805811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28240517508179264537207 42360776262268896805811)
            ·
              refine ⟨63541164393403345208717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42360776262268896805811 63541164393403345208717)
              ·
                refine ⟨23827936647526254453269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63541164393403345208717 23827936647526254453269)
                ·
                  refine ⟨1116934530352793177497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23827936647526254453269 1116934530352793177497)
                  ·
                    rfl

theorem cell23_19577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 6].length) (baseStart_19577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19577 prefixEnd_19577 := by exact prefixLift 19577
  have htrace : WordTrace (prefixWord ++ tailWord_19577) baseStart_19577 baseEnd_19577 := by
    simpa [prefixWord, tailWord_19577, baseEnd_19577] using wordTrace_append hprefix tailTrace_19577
  have hstable : (prefixWord ++ tailWord_19577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19577).length < 2 ^ (prefixWord ++ tailWord_19577).sum := by decide
  have hdescent : baseEnd_19577 < baseStart_19577 := by decide
  rcases family_descends (prefixWord ++ tailWord_19577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19587 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 5, 1, 3]
def baseStart_19587 : Nat := 118140960795 + 19587 * 2 ^ 59
def prefixEnd_19587 : Nat := 4983230072969 + 3 ^ 40 * 19587 * 2
def baseEnd_19587 : Nat := 10057545579720099472427

theorem tailTrace_19587 : CollatzResearch.WordTrace tailWord_19587 prefixEnd_19587 10057545579720099472427 := by
  unfold tailWord_19587
  simp only [CollatzResearch.WordTrace]
  refine ⟨714396580047119038385015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 476264386698079358923343 714396580047119038385015)
  ·
    refine ⟨1071594870070678557577523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 714396580047119038385015 1071594870070678557577523)
    ·
      refine ⟨1607392305106017836366285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1071594870070678557577523 1607392305106017836366285)
      ·
        refine ⟨602772114414756688637357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1607392305106017836366285 602772114414756688637357)
        ·
          refine ⟨226039542905533758239009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 602772114414756688637357 226039542905533758239009)
          ·
            refine ⟨169529657179150318679257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226039542905533758239009 169529657179150318679257)
            ·
              refine ⟨127147242884362739009443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169529657179150318679257 127147242884362739009443)
              ·
                refine ⟨190720864326544108514165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127147242884362739009443 190720864326544108514165)
                ·
                  refine ⟨17880081030613510173203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190720864326544108514165 17880081030613510173203)
                  ·
                    refine ⟨26820121545920265259805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17880081030613510173203 26820121545920265259805)
                    ·
                      refine ⟨10057545579720099472427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 26820121545920265259805 10057545579720099472427)
                      ·
                        rfl

theorem cell23_19587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_19587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19587 prefixEnd_19587 := by exact prefixLift 19587
  have htrace : WordTrace (prefixWord ++ tailWord_19587) baseStart_19587 baseEnd_19587 := by
    simpa [prefixWord, tailWord_19587, baseEnd_19587] using wordTrace_append hprefix tailTrace_19587
  have hstable : (prefixWord ++ tailWord_19587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19587).length < 2 ^ (prefixWord ++ tailWord_19587).sum := by decide
  have hdescent : baseEnd_19587 < baseStart_19587 := by decide
  rcases family_descends (prefixWord ++ tailWord_19587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19615 : List Nat := [1, 1, 2, 6, 3, 1, 2, 2, 1, 4]
def baseStart_19615 : Nat := 118140960795 + 19615 * 2 ^ 59
def prefixEnd_19615 : Nat := 4983230072969 + 3 ^ 40 * 19615 * 2
def baseEnd_19615 : Nat := 3357307679348663307433

theorem tailTrace_19615 : CollatzResearch.WordTrace tailWord_19615 prefixEnd_19615 3357307679348663307433 := by
  unfold tailWord_19615
  simp only [CollatzResearch.WordTrace]
  refine ⟨715417823945679820404299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 476945215963786546936199 715417823945679820404299)
  ·
    refine ⟨1073126735918519730606449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 715417823945679820404299 1073126735918519730606449)
    ·
      refine ⟨804845051938889797954837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1073126735918519730606449 804845051938889797954837)
      ·
        refine ⟨37727111809635459279133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 804845051938889797954837 37727111809635459279133)
        ·
          refine ⟨14147666928613297229675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37727111809635459279133 14147666928613297229675)
          ·
            refine ⟨21221500392919945844513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14147666928613297229675 21221500392919945844513)
            ·
              refine ⟨15916125294689959383385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21221500392919945844513 15916125294689959383385)
              ·
                refine ⟨11937093971017469537539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15916125294689959383385 11937093971017469537539)
                ·
                  refine ⟨17905640956526204306309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11937093971017469537539 17905640956526204306309)
                  ·
                    refine ⟨3357307679348663307433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17905640956526204306309 3357307679348663307433)
                    ·
                      rfl

theorem cell23_19615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 1, 4].length) (baseStart_19615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19615 prefixEnd_19615 := by exact prefixLift 19615
  have htrace : WordTrace (prefixWord ++ tailWord_19615) baseStart_19615 baseEnd_19615 := by
    simpa [prefixWord, tailWord_19615, baseEnd_19615] using wordTrace_append hprefix tailTrace_19615
  have hstable : (prefixWord ++ tailWord_19615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19615).length < 2 ^ (prefixWord ++ tailWord_19615).sum := by decide
  have hdescent : baseEnd_19615 < baseStart_19615 := by decide
  rcases family_descends (prefixWord ++ tailWord_19615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19621 : List Nat := [1, 3, 1, 2, 1, 5, 1, 4, 1, 1, 3]
def baseStart_19621 : Nat := 118140960795 + 19621 * 2 ^ 59
def prefixEnd_19621 : Nat := 4983230072969 + 3 ^ 40 * 19621 * 2
def baseEnd_19621 : Nat := 10075003921972966447271

theorem tailTrace_19621 : CollatzResearch.WordTrace tailWord_19621 prefixEnd_19621 10075003921972966447271 := by
  unfold tailWord_19621
  simp only [CollatzResearch.WordTrace]
  refine ⟨715636661923942845122717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 477091107949295230081811 715636661923942845122717)
  ·
    refine ⟨268363748221478566921019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 715636661923942845122717 268363748221478566921019)
    ·
      refine ⟨402545622332217850381529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268363748221478566921019 402545622332217850381529)
      ·
        refine ⟨301909216749163387786147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402545622332217850381529 301909216749163387786147)
        ·
          refine ⟨452863825123745081679221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301909216749163387786147 452863825123745081679221)
          ·
            refine ⟨42455983605351101407427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 452863825123745081679221 42455983605351101407427)
            ·
              refine ⟨63683975408026652111141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42455983605351101407427 63683975408026652111141)
              ·
                refine ⟨11940745389004997270839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63683975408026652111141 11940745389004997270839)
                ·
                  refine ⟨17911118083507495906259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11940745389004997270839 17911118083507495906259)
                  ·
                    refine ⟨26866677125261243859389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17911118083507495906259 26866677125261243859389)
                    ·
                      refine ⟨10075003921972966447271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 26866677125261243859389 10075003921972966447271)
                      ·
                        rfl

theorem cell23_19621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_19621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19621 prefixEnd_19621 := by exact prefixLift 19621
  have htrace : WordTrace (prefixWord ++ tailWord_19621) baseStart_19621 baseEnd_19621 := by
    simpa [prefixWord, tailWord_19621, baseEnd_19621] using wordTrace_append hprefix tailTrace_19621
  have hstable : (prefixWord ++ tailWord_19621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19621).length < 2 ^ (prefixWord ++ tailWord_19621).sum := by decide
  have hdescent : baseEnd_19621 < baseStart_19621 := by decide
  rcases family_descends (prefixWord ++ tailWord_19621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19647 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 3]
def baseStart_19647 : Nat := 118140960795 + 19647 * 2 ^ 59
def prefixEnd_19647 : Nat := 4983230072969 + 3 ^ 40 * 19647 * 2
def baseEnd_19647 : Nat := 10088354418989864722151

theorem tailTrace_19647 : CollatzResearch.WordTrace tailWord_19647 prefixEnd_19647 10088354418989864722151 := by
  unfold tailWord_19647
  simp only [CollatzResearch.WordTrace]
  refine ⟨716584959829749285569195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 477723306553166190379463 716584959829749285569195)
  ·
    refine ⟨1074877439744623928353793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 716584959829749285569195 1074877439744623928353793)
    ·
      refine ⟨806158079808467946265345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1074877439744623928353793 806158079808467946265345)
      ·
        refine ⟨604618559856350959699009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 806158079808467946265345 604618559856350959699009)
        ·
          refine ⟨453463919892263219774257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 604618559856350959699009 453463919892263219774257)
          ·
            refine ⟨340097939919197414830693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453463919892263219774257 340097939919197414830693)
            ·
              refine ⟨63768363734849515280755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 340097939919197414830693 63768363734849515280755)
              ·
                refine ⟨95652545602274272921133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63768363734849515280755 95652545602274272921133)
                ·
                  refine ⟨35869704600852852345425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95652545602274272921133 35869704600852852345425)
                  ·
                    refine ⟨26902278450639639259069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35869704600852852345425 26902278450639639259069)
                    ·
                      refine ⟨10088354418989864722151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 26902278450639639259069 10088354418989864722151)
                      ·
                        rfl

theorem cell23_19647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_19647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19647 prefixEnd_19647 := by exact prefixLift 19647
  have htrace : WordTrace (prefixWord ++ tailWord_19647) baseStart_19647 baseEnd_19647 := by
    simpa [prefixWord, tailWord_19647, baseEnd_19647] using wordTrace_append hprefix tailTrace_19647
  have hstable : (prefixWord ++ tailWord_19647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19647).length < 2 ^ (prefixWord ++ tailWord_19647).sum := by decide
  have hdescent : baseEnd_19647 < baseStart_19647 := by decide
  rcases family_descends (prefixWord ++ tailWord_19647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19648 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 2, 3, 2]
def baseStart_19648 : Nat := 118140960795 + 19648 * 2 ^ 59
def prefixEnd_19648 : Nat := 4983230072969 + 3 ^ 40 * 19648 * 2
def baseEnd_19648 : Nat := 10088867899644360809647

theorem tailTrace_19648 : CollatzResearch.WordTrace tailWord_19648 prefixEnd_19648 10088867899644360809647 := by
  unfold tailWord_19648
  simp only [CollatzResearch.WordTrace]
  refine ⟨358310716413063228177799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 477747621884084304237065 358310716413063228177799)
  ·
    refine ⟨537466074619594842266699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 358310716413063228177799 537466074619594842266699)
    ·
      refine ⟨806199111929392263400049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 537466074619594842266699 806199111929392263400049)
      ·
        refine ⟨604649333947044197550037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 806199111929392263400049 604649333947044197550037)
        ·
          refine ⟨14171468764383848380079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 604649333947044197550037 14171468764383848380079)
          ·
            refine ⟨21257203146575772570119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14171468764383848380079 21257203146575772570119)
            ·
              refine ⟨31885804719863658855179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21257203146575772570119 31885804719863658855179)
              ·
                refine ⟨47828707079795488282769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31885804719863658855179 47828707079795488282769)
                ·
                  refine ⟨35871530309846616212077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47828707079795488282769 35871530309846616212077)
                  ·
                    refine ⟨13451823866192481079529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35871530309846616212077 13451823866192481079529)
                    ·
                      refine ⟨10088867899644360809647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13451823866192481079529 10088867899644360809647)
                      ·
                        rfl

theorem cell23_19648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 3, 2].length) (baseStart_19648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19648 prefixEnd_19648 := by exact prefixLift 19648
  have htrace : WordTrace (prefixWord ++ tailWord_19648) baseStart_19648 baseEnd_19648 := by
    simpa [prefixWord, tailWord_19648, baseEnd_19648] using wordTrace_append hprefix tailTrace_19648
  have hstable : (prefixWord ++ tailWord_19648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19648).length < 2 ^ (prefixWord ++ tailWord_19648).sum := by decide
  have hdescent : baseEnd_19648 < baseStart_19648 := by decide
  rcases family_descends (prefixWord ++ tailWord_19648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19694 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_19694 : Nat := 118140960795 + 19694 * 2 ^ 59
def prefixEnd_19694 : Nat := 4983230072969 + 3 ^ 40 * 19694 * 2
def baseEnd_19694 : Nat := 10112488009751180834435

theorem tailTrace_19694 : CollatzResearch.WordTrace tailWord_19694 prefixEnd_19694 10112488009751180834435 := by
  unfold tailWord_19694
  simp only [CollatzResearch.WordTrace]
  refine ⟨89787398832434539066267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 478866127106317541686757 89787398832434539066267)
  ·
    refine ⟨134681098248651808599401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89787398832434539066267 134681098248651808599401)
    ·
      refine ⟨101010823686488856449551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134681098248651808599401 101010823686488856449551)
      ·
        refine ⟨151516235529733284674327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101010823686488856449551 151516235529733284674327)
        ·
          refine ⟨227274353294599927011491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151516235529733284674327 227274353294599927011491)
          ·
            refine ⟨340911529941899890517237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227274353294599927011491 340911529941899890517237)
            ·
              refine ⟨31960455932053114735991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 340911529941899890517237 31960455932053114735991)
              ·
                refine ⟨47940683898079672103987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31960455932053114735991 47940683898079672103987)
                ·
                  refine ⟨71911025847119508155981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47940683898079672103987 71911025847119508155981)
                  ·
                    refine ⟨26966634692669815558493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71911025847119508155981 26966634692669815558493)
                    ·
                      refine ⟨10112488009751180834435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 26966634692669815558493 10112488009751180834435)
                      ·
                        rfl

theorem cell23_19694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_19694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19694 prefixEnd_19694 := by exact prefixLift 19694
  have htrace : WordTrace (prefixWord ++ tailWord_19694) baseStart_19694 baseEnd_19694 := by
    simpa [prefixWord, tailWord_19694, baseEnd_19694] using wordTrace_append hprefix tailTrace_19694
  have hstable : (prefixWord ++ tailWord_19694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19694).length < 2 ^ (prefixWord ++ tailWord_19694).sum := by decide
  have hdescent : baseEnd_19694 < baseStart_19694 := by decide
  rcases family_descends (prefixWord ++ tailWord_19694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19754 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_19754 : Nat := 118140960795 + 19754 * 2 ^ 59
def prefixEnd_19754 : Nat := 4983230072969 + 3 ^ 40 * 19754 * 2
def baseEnd_19754 : Nat := 10143296849020946084159

theorem tailTrace_19754 : CollatzResearch.WordTrace tailWord_19754 prefixEnd_19754 10143296849020946084159 := by
  unfold tailWord_19754
  simp only [CollatzResearch.WordTrace]
  refine ⟨180121892610526639928579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 480325046961404373142877 180121892610526639928579)
  ·
    refine ⟨270182838915789959892869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180121892610526639928579 270182838915789959892869)
    ·
      refine ⟨50659282296710617479913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270182838915789959892869 50659282296710617479913)
      ·
        refine ⟨37994461722532963109935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50659282296710617479913 37994461722532963109935)
        ·
          refine ⟨56991692583799444664903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37994461722532963109935 56991692583799444664903)
          ·
            refine ⟨85487538875699166997355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56991692583799444664903 85487538875699166997355)
            ·
              refine ⟨128231308313548750496033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85487538875699166997355 128231308313548750496033)
              ·
                refine ⟨96173481235161562872025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128231308313548750496033 96173481235161562872025)
                ·
                  refine ⟨72130110926371172154019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96173481235161562872025 72130110926371172154019)
                  ·
                    refine ⟨108195166389556758231029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72130110926371172154019 108195166389556758231029)
                    ·
                      refine ⟨10143296849020946084159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 108195166389556758231029 10143296849020946084159)
                      ·
                        rfl

theorem cell23_19754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_19754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19754 prefixEnd_19754 := by exact prefixLift 19754
  have htrace : WordTrace (prefixWord ++ tailWord_19754) baseStart_19754 baseEnd_19754 := by
    simpa [prefixWord, tailWord_19754, baseEnd_19754] using wordTrace_append hprefix tailTrace_19754
  have hstable : (prefixWord ++ tailWord_19754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19754).length < 2 ^ (prefixWord ++ tailWord_19754).sum := by decide
  have hdescent : baseEnd_19754 < baseStart_19754 := by decide
  rcases family_descends (prefixWord ++ tailWord_19754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19767 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 3]
def baseStart_19767 : Nat := 118140960795 + 19767 * 2 ^ 59
def prefixEnd_19767 : Nat := 4983230072969 + 3 ^ 40 * 19767 * 2
def baseEnd_19767 : Nat := 10149972097529395221599

theorem tailTrace_19767 : CollatzResearch.WordTrace tailWord_19767 prefixEnd_19767 10149972097529395221599 := by
  unfold tailWord_19767
  simp only [CollatzResearch.WordTrace]
  refine ⟨720961719395009779937555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 480641146263339853291703 720961719395009779937555)
  ·
    refine ⟨1081442579092514669906333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 720961719395009779937555 1081442579092514669906333)
    ·
      refine ⟨405540967159693001214875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1081442579092514669906333 405540967159693001214875)
      ·
        refine ⟨608311450739539501822313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405540967159693001214875 608311450739539501822313)
        ·
          refine ⟨456233588054654626366735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608311450739539501822313 456233588054654626366735)
          ·
            refine ⟨684350382081981939550103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456233588054654626366735 684350382081981939550103)
            ·
              refine ⟨1026525573122972909325155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684350382081981939550103 1026525573122972909325155)
              ·
                refine ⟨1539788359684459363987733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026525573122972909325155 1539788359684459363987733)
                ·
                  refine ⟨72177579360209032686925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1539788359684459363987733 72177579360209032686925)
                  ·
                    refine ⟨27066592260078387257597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72177579360209032686925 27066592260078387257597)
                    ·
                      refine ⟨10149972097529395221599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 27066592260078387257597 10149972097529395221599)
                      ·
                        rfl

theorem cell23_19767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_19767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19767 prefixEnd_19767 := by exact prefixLift 19767
  have htrace : WordTrace (prefixWord ++ tailWord_19767) baseStart_19767 baseEnd_19767 := by
    simpa [prefixWord, tailWord_19767, baseEnd_19767] using wordTrace_append hprefix tailTrace_19767
  have hstable : (prefixWord ++ tailWord_19767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19767).length < 2 ^ (prefixWord ++ tailWord_19767).sum := by decide
  have hdescent : baseEnd_19767 < baseStart_19767 := by decide
  rcases family_descends (prefixWord ++ tailWord_19767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19807 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 4]
def baseStart_19807 : Nat := 118140960795 + 19807 * 2 ^ 59
def prefixEnd_19807 : Nat := 4983230072969 + 3 ^ 40 * 19807 * 2
def baseEnd_19807 : Nat := 10170511323709238721415

theorem tailTrace_19807 : CollatzResearch.WordTrace tailWord_19807 prefixEnd_19807 10170511323709238721415 := by
  unfold tailWord_19807
  simp only [CollatzResearch.WordTrace]
  refine ⟨722420639250096611393675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 481613759500064407595783 722420639250096611393675)
  ·
    refine ⟨1083630958875144917090513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 722420639250096611393675 1083630958875144917090513)
    ·
      refine ⟨812723219156358687817885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1083630958875144917090513 812723219156358687817885)
      ·
        refine ⟨304771207183634507931707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 812723219156358687817885 304771207183634507931707)
        ·
          refine ⟨457156810775451761897561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304771207183634507931707 457156810775451761897561)
          ·
            refine ⟨342867608081588821423171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 457156810775451761897561 342867608081588821423171)
            ·
              refine ⟨514301412122383232134757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342867608081588821423171 514301412122383232134757)
              ·
                refine ⟨96431514772946856025267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514301412122383232134757 96431514772946856025267)
                ·
                  refine ⟨144647272159420284037901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96431514772946856025267 144647272159420284037901)
                  ·
                    refine ⟨54242727059782606514213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144647272159420284037901 54242727059782606514213)
                    ·
                      refine ⟨10170511323709238721415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 54242727059782606514213 10170511323709238721415)
                      ·
                        rfl

theorem cell23_19807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_19807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19807 prefixEnd_19807 := by exact prefixLift 19807
  have htrace : WordTrace (prefixWord ++ tailWord_19807) baseStart_19807 baseEnd_19807 := by
    simpa [prefixWord, tailWord_19807, baseEnd_19807] using wordTrace_append hprefix tailTrace_19807
  have hstable : (prefixWord ++ tailWord_19807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19807).length < 2 ^ (prefixWord ++ tailWord_19807).sum := by decide
  have hdescent : baseEnd_19807 < baseStart_19807 := by decide
  rcases family_descends (prefixWord ++ tailWord_19807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19821 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_19821 : Nat := 118140960795 + 19821 * 2 ^ 59
def prefixEnd_19821 : Nat := 4983230072969 + 3 ^ 40 * 19821 * 2
def baseEnd_19821 : Nat := 3392566684290727982117

theorem tailTrace_19821 : CollatzResearch.WordTrace tailWord_19821 prefixEnd_19821 3392566684290727982117 := by
  unfold tailWord_19821
  simp only [CollatzResearch.WordTrace]
  refine ⟨722931261199377002403317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 481954174132918001602211 722931261199377002403317)
  ·
    refine ⟨67774805737441593975311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 722931261199377002403317 67774805737441593975311)
    ·
      refine ⟨101662208606162390962967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67774805737441593975311 101662208606162390962967)
      ·
        refine ⟨152493312909243586444451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101662208606162390962967 152493312909243586444451)
        ·
          refine ⟨228739969363865379666677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152493312909243586444451 228739969363865379666677)
          ·
            refine ⟨21444372127862379343751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 228739969363865379666677 21444372127862379343751)
            ·
              refine ⟨32166558191793569015627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21444372127862379343751 32166558191793569015627)
              ·
                refine ⟨48249837287690353523441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32166558191793569015627 48249837287690353523441)
                ·
                  refine ⟨36187377965767765142581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48249837287690353523441 36187377965767765142581)
                  ·
                    refine ⟨3392566684290727982117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36187377965767765142581 3392566684290727982117)
                    ·
                      rfl

theorem cell23_19821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_19821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19821 prefixEnd_19821 := by exact prefixLift 19821
  have htrace : WordTrace (prefixWord ++ tailWord_19821) baseStart_19821 baseEnd_19821 := by
    simpa [prefixWord, tailWord_19821, baseEnd_19821] using wordTrace_append hprefix tailTrace_19821
  have hstable : (prefixWord ++ tailWord_19821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19821).length < 2 ^ (prefixWord ++ tailWord_19821).sum := by decide
  have hdescent : baseEnd_19821 < baseStart_19821 := by decide
  rcases family_descends (prefixWord ++ tailWord_19821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19824 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 1, 6, 2]
def baseStart_19824 : Nat := 118140960795 + 19824 * 2 ^ 59
def prefixEnd_19824 : Nat := 4983230072969 + 3 ^ 40 * 19824 * 2
def baseEnd_19824 : Nat := 10179240494835672208837

theorem tailTrace_19824 : CollatzResearch.WordTrace tailWord_19824 prefixEnd_19824 10179240494835672208837 := by
  unfold tailWord_19824
  simp only [CollatzResearch.WordTrace]
  refine ⟨361520340094254257381263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 482027120125672343175017 361520340094254257381263)
  ·
    refine ⟨542280510141381386071895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 361520340094254257381263 542280510141381386071895)
    ·
      refine ⟨813420765212072079107843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 542280510141381386071895 813420765212072079107843)
      ·
        refine ⟨1220131147818108118661765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813420765212072079107843 1220131147818108118661765)
        ·
          refine ⟨228774590215895272249081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1220131147818108118661765 228774590215895272249081)
          ·
            refine ⟨171580942661921454186811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228774590215895272249081 171580942661921454186811)
            ·
              refine ⟨257371413992882181280217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171580942661921454186811 257371413992882181280217)
              ·
                refine ⟨193028560494661635960163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257371413992882181280217 193028560494661635960163)
                ·
                  refine ⟨289542840741992453940245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193028560494661635960163 289542840741992453940245)
                  ·
                    refine ⟨13572320659780896278449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 289542840741992453940245 13572320659780896278449)
                    ·
                      refine ⟨10179240494835672208837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13572320659780896278449 10179240494835672208837)
                      ·
                        rfl

theorem cell23_19824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 6, 2].length) (baseStart_19824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19824 prefixEnd_19824 := by exact prefixLift 19824
  have htrace : WordTrace (prefixWord ++ tailWord_19824) baseStart_19824 baseEnd_19824 := by
    simpa [prefixWord, tailWord_19824, baseEnd_19824] using wordTrace_append hprefix tailTrace_19824
  have hstable : (prefixWord ++ tailWord_19824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19824).length < 2 ^ (prefixWord ++ tailWord_19824).sum := by decide
  have hdescent : baseEnd_19824 < baseStart_19824 := by decide
  rcases family_descends (prefixWord ++ tailWord_19824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19837 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_19837 : Nat := 118140960795 + 19837 * 2 ^ 59
def prefixEnd_19837 : Nat := 4983230072969 + 3 ^ 40 * 19837 * 2
def baseEnd_19837 : Nat := 10185915743344121346277

theorem tailTrace_19837 : CollatzResearch.WordTrace tailWord_19837 prefixEnd_19837 10185915743344121346277 := by
  unfold tailWord_19837
  simp only [CollatzResearch.WordTrace]
  refine ⟨723514829141411734985765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 482343219427607823323843 723514829141411734985765)
  ·
    refine ⟨135659030464014700309831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 723514829141411734985765 135659030464014700309831)
    ·
      refine ⟨203488545696022050464747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135659030464014700309831 203488545696022050464747)
      ·
        refine ⟨305232818544033075697121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203488545696022050464747 305232818544033075697121)
        ·
          refine ⟨228924613908024806772841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305232818544033075697121 228924613908024806772841)
          ·
            refine ⟨171693460431018605079631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228924613908024806772841 171693460431018605079631)
            ·
              refine ⟨257540190646527907619447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171693460431018605079631 257540190646527907619447)
              ·
                refine ⟨386310285969791861429171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257540190646527907619447 386310285969791861429171)
                ·
                  refine ⟨579465428954687792143757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386310285969791861429171 579465428954687792143757)
                  ·
                    refine ⟨217299535858007922053909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 579465428954687792143757 217299535858007922053909)
                    ·
                      refine ⟨10185915743344121346277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 217299535858007922053909 10185915743344121346277)
                      ·
                        rfl

theorem cell23_19837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_19837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19837 prefixEnd_19837 := by exact prefixLift 19837
  have htrace : WordTrace (prefixWord ++ tailWord_19837) baseStart_19837 baseEnd_19837 := by
    simpa [prefixWord, tailWord_19837, baseEnd_19837] using wordTrace_append hprefix tailTrace_19837
  have hstable : (prefixWord ++ tailWord_19837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19837).length < 2 ^ (prefixWord ++ tailWord_19837).sum := by decide
  have hdescent : baseEnd_19837 < baseStart_19837 := by decide
  rcases family_descends (prefixWord ++ tailWord_19837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19851 : List Nat := [1, 1, 1, 1, 4, 3, 1, 6, 1, 4]
def baseStart_19851 : Nat := 118140960795 + 19851 * 2 ^ 59
def prefixEnd_19851 : Nat := 4983230072969 + 3 ^ 40 * 19851 * 2
def baseEnd_19851 : Nat := 3397701490835688857071

theorem tailTrace_19851 : CollatzResearch.WordTrace tailWord_19851 prefixEnd_19851 3397701490835688857071 := by
  unfold tailWord_19851
  simp only [CollatzResearch.WordTrace]
  refine ⟨724025451090692125995407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 482683634060461417330271 724025451090692125995407)
  ·
    refine ⟨1086038176636038188993111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 724025451090692125995407 1086038176636038188993111)
    ·
      refine ⟨1629057264954057283489667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086038176636038188993111 1629057264954057283489667)
      ·
        refine ⟨2443585897431085925234501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629057264954057283489667 2443585897431085925234501)
        ·
          refine ⟨458172355768328610981469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2443585897431085925234501 458172355768328610981469)
          ·
            refine ⟨171814633413123229118051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 458172355768328610981469 171814633413123229118051)
            ·
              refine ⟨257721950119684843677077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171814633413123229118051 257721950119684843677077)
              ·
                refine ⟨12080716411860227047363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 257721950119684843677077 12080716411860227047363)
                ·
                  refine ⟨18121074617790340571045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12080716411860227047363 18121074617790340571045)
                  ·
                    refine ⟨3397701490835688857071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18121074617790340571045 3397701490835688857071)
                    ·
                      rfl

theorem cell23_19851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 1, 4].length) (baseStart_19851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19851 prefixEnd_19851 := by exact prefixLift 19851
  have htrace : WordTrace (prefixWord ++ tailWord_19851) baseStart_19851 baseEnd_19851 := by
    simpa [prefixWord, tailWord_19851, baseEnd_19851] using wordTrace_append hprefix tailTrace_19851
  have hstable : (prefixWord ++ tailWord_19851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19851).length < 2 ^ (prefixWord ++ tailWord_19851).sum := by decide
  have hdescent : baseEnd_19851 < baseStart_19851 := by decide
  rcases family_descends (prefixWord ++ tailWord_19851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19885 : List Nat := [1, 5, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_19885 : Nat := 118140960795 + 19885 * 2 ^ 59
def prefixEnd_19885 : Nat := 4983230072969 + 3 ^ 40 * 19885 * 2
def baseEnd_19885 : Nat := 3403520938253311182019

theorem tailTrace_19885 : CollatzResearch.WordTrace tailWord_19885 prefixEnd_19885 3403520938253311182019 := by
  unfold tailWord_19885
  simp only [CollatzResearch.WordTrace]
  refine ⟨725265532967515932733109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 483510355311677288488739 725265532967515932733109)
  ·
    refine ⟨67993643715704618693729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 725265532967515932733109 67993643715704618693729)
    ·
      refine ⟨50995232786778464020297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67993643715704618693729 50995232786778464020297)
      ·
        refine ⟨38246424590083848015223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50995232786778464020297 38246424590083848015223)
        ·
          refine ⟨57369636885125772022835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38246424590083848015223 57369636885125772022835)
          ·
            refine ⟨86054455327688658034253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57369636885125772022835 86054455327688658034253)
            ·
              refine ⟨32270420747883246762845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86054455327688658034253 32270420747883246762845)
              ·
                refine ⟨12101407780456217536067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32270420747883246762845 12101407780456217536067)
                ·
                  refine ⟨18152111670684326304101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12101407780456217536067 18152111670684326304101)
                  ·
                    refine ⟨3403520938253311182019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18152111670684326304101 3403520938253311182019)
                    ·
                      rfl

theorem cell23_19885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_19885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19885 prefixEnd_19885 := by exact prefixLift 19885
  have htrace : WordTrace (prefixWord ++ tailWord_19885) baseStart_19885 baseEnd_19885 := by
    simpa [prefixWord, tailWord_19885, baseEnd_19885] using wordTrace_append hprefix tailTrace_19885
  have hstable : (prefixWord ++ tailWord_19885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19885).length < 2 ^ (prefixWord ++ tailWord_19885).sum := by decide
  have hdescent : baseEnd_19885 < baseStart_19885 := by decide
  rcases family_descends (prefixWord ++ tailWord_19885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19941 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_19941 : Nat := 118140960795 + 19941 * 2 ^ 59
def prefixEnd_19941 : Nat := 4983230072969 + 3 ^ 40 * 19941 * 2
def baseEnd_19941 : Nat := 3413105910470571481933

theorem tailTrace_19941 : CollatzResearch.WordTrace tailWord_19941 prefixEnd_19941 3413105910470571481933 := by
  unfold tailWord_19941
  simp only [CollatzResearch.WordTrace]
  refine ⟨727308020764637496771677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 484872013843091664514451 727308020764637496771677)
  ·
    refine ⟨272740507786739061289379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 727308020764637496771677 272740507786739061289379)
    ·
      refine ⟨409110761680108591934069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272740507786739061289379 409110761680108591934069)
      ·
        refine ⟨38354133907510180493819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 409110761680108591934069 38354133907510180493819)
        ·
          refine ⟨57531200861265270740729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38354133907510180493819 57531200861265270740729)
          ·
            refine ⟨43148400645948953055547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57531200861265270740729 43148400645948953055547)
            ·
              refine ⟨64722600968923429583321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43148400645948953055547 64722600968923429583321)
              ·
                refine ⟨48541950726692572187491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64722600968923429583321 48541950726692572187491)
                ·
                  refine ⟨72812926090038858281237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48541950726692572187491 72812926090038858281237)
                  ·
                    refine ⟨3413105910470571481933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72812926090038858281237 3413105910470571481933)
                    ·
                      rfl

theorem cell23_19941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_19941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19941 prefixEnd_19941 := by exact prefixLift 19941
  have htrace : WordTrace (prefixWord ++ tailWord_19941) baseStart_19941 baseEnd_19941 := by
    simpa [prefixWord, tailWord_19941, baseEnd_19941] using wordTrace_append hprefix tailTrace_19941
  have hstable : (prefixWord ++ tailWord_19941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19941).length < 2 ^ (prefixWord ++ tailWord_19941).sum := by decide
  have hdescent : baseEnd_19941 < baseStart_19941 := by decide
  rcases family_descends (prefixWord ++ tailWord_19941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19951 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 1, 2, 3]
def baseStart_19951 : Nat := 118140960795 + 19951 * 2 ^ 59
def prefixEnd_19951 : Nat := 4983230072969 + 3 ^ 40 * 19951 * 2
def baseEnd_19951 : Nat := 10244452537956675320753

theorem tailTrace_19951 : CollatzResearch.WordTrace tailWord_19951 prefixEnd_19951 10244452537956675320753 := by
  unfold tailWord_19951
  simp only [CollatzResearch.WordTrace]
  refine ⟨727672750728409204635707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 485115167152272803090471 727672750728409204635707)
  ·
    refine ⟨1091509126092613806953561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 727672750728409204635707 1091509126092613806953561)
    ·
      refine ⟨818631844569460355215171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1091509126092613806953561 818631844569460355215171)
      ·
        refine ⟨1227947766854190532822757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818631844569460355215171 1227947766854190532822757)
        ·
          refine ⟨230240206285160724904267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1227947766854190532822757 230240206285160724904267)
          ·
            refine ⟨345360309427741087356401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230240206285160724904267 345360309427741087356401)
            ·
              refine ⟨259020232070805815517301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345360309427741087356401 259020232070805815517301)
              ·
                refine ⟨24283146756638045204747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259020232070805815517301 24283146756638045204747)
                ·
                  refine ⟨36424720134957067807121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24283146756638045204747 36424720134957067807121)
                  ·
                    refine ⟨27318540101217800855341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36424720134957067807121 27318540101217800855341)
                    ·
                      refine ⟨10244452537956675320753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 27318540101217800855341 10244452537956675320753)
                      ·
                        rfl

theorem cell23_19951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 2, 3].length) (baseStart_19951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19951 prefixEnd_19951 := by exact prefixLift 19951
  have htrace : WordTrace (prefixWord ++ tailWord_19951) baseStart_19951 baseEnd_19951 := by
    simpa [prefixWord, tailWord_19951, baseEnd_19951] using wordTrace_append hprefix tailTrace_19951
  have hstable : (prefixWord ++ tailWord_19951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19951).length < 2 ^ (prefixWord ++ tailWord_19951).sum := by decide
  have hdescent : baseEnd_19951 < baseStart_19951 := by decide
  rcases family_descends (prefixWord ++ tailWord_19951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19954 : List Nat := [3, 2, 1, 4, 1, 12]
def baseStart_19954 : Nat := 118140960795 + 19954 * 2 ^ 59
def prefixEnd_19954 : Nat := 4983230072969 + 3 ^ 40 * 19954 * 2
def baseEnd_19954 : Nat := 42164580164280508573

theorem tailTrace_19954 : CollatzResearch.WordTrace tailWord_19954 prefixEnd_19954 42164580164280508573 := by
  unfold tailWord_19954
  simp only [CollatzResearch.WordTrace]
  refine ⟨181945542429385179248729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 485188113145027144663277 181945542429385179248729)
  ·
    refine ⟨136459156822038884436547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181945542429385179248729 136459156822038884436547)
    ·
      refine ⟨204688735233058326654821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136459156822038884436547 204688735233058326654821)
      ·
        refine ⟨38379137856198436247779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204688735233058326654821 38379137856198436247779)
        ·
          refine ⟨57568706784297654371669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38379137856198436247779 57568706784297654371669)
          ·
            refine ⟨42164580164280508573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 57568706784297654371669 42164580164280508573)
            ·
              rfl

theorem cell23_19954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 12].length) (baseStart_19954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19954 prefixEnd_19954 := by exact prefixLift 19954
  have htrace : WordTrace (prefixWord ++ tailWord_19954) baseStart_19954 baseEnd_19954 := by
    simpa [prefixWord, tailWord_19954, baseEnd_19954] using wordTrace_append hprefix tailTrace_19954
  have hstable : (prefixWord ++ tailWord_19954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19954).length < 2 ^ (prefixWord ++ tailWord_19954).sum := by decide
  have hdescent : baseEnd_19954 < baseStart_19954 := by decide
  rcases family_descends (prefixWord ++ tailWord_19954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19958 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_19958 : Nat := 118140960795 + 19958 * 2 ^ 59
def prefixEnd_19958 : Nat := 4983230072969 + 3 ^ 40 * 19958 * 2
def baseEnd_19958 : Nat := 3416015634179382644407

theorem tailTrace_19958 : CollatzResearch.WordTrace tailWord_19958 prefixEnd_19958 3416015634179382644407 := by
  unfold tailWord_19958
  simp only [CollatzResearch.WordTrace]
  refine ⟨45495503856440587508783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 485285374468699600093685 45495503856440587508783)
  ·
    refine ⟨68243255784660881263175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45495503856440587508783 68243255784660881263175)
    ·
      refine ⟨102364883676991321894763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68243255784660881263175 102364883676991321894763)
      ·
        refine ⟨153547325515486982842145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102364883676991321894763 153547325515486982842145)
        ·
          refine ⟨115160494136615237131609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153547325515486982842145 115160494136615237131609)
          ·
            refine ⟨86370370602461427848707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115160494136615237131609 86370370602461427848707)
            ·
              refine ⟨129555555903692141773061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86370370602461427848707 129555555903692141773061)
              ·
                refine ⟨24291666731942276582449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129555555903692141773061 24291666731942276582449)
                ·
                  refine ⟨18218750048956707436837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24291666731942276582449 18218750048956707436837)
                  ·
                    refine ⟨3416015634179382644407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18218750048956707436837 3416015634179382644407)
                    ·
                      rfl

theorem cell23_19958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_19958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19958 prefixEnd_19958 := by exact prefixLift 19958
  have htrace : WordTrace (prefixWord ++ tailWord_19958) baseStart_19958 baseEnd_19958 := by
    simpa [prefixWord, tailWord_19958, baseEnd_19958] using wordTrace_append hprefix tailTrace_19958
  have hstable : (prefixWord ++ tailWord_19958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19958).length < 2 ^ (prefixWord ++ tailWord_19958).sum := by decide
  have hdescent : baseEnd_19958 < baseStart_19958 := by decide
  rcases family_descends (prefixWord ++ tailWord_19958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19994 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_19994 : Nat := 118140960795 + 19994 * 2 ^ 59
def prefixEnd_19994 : Nat := 4983230072969 + 3 ^ 40 * 19994 * 2
def baseEnd_19994 : Nat := 10266532206100007083055

theorem tailTrace_19994 : CollatzResearch.WordTrace tailWord_19994 prefixEnd_19994 10266532206100007083055 := by
  unfold tailWord_19994
  simp only [CollatzResearch.WordTrace]
  refine ⟨182310272393156887112759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 486160726381751698967357 182310272393156887112759)
  ·
    refine ⟨273465408589735330669139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182310272393156887112759 273465408589735330669139)
    ·
      refine ⟨410198112884602996003709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273465408589735330669139 410198112884602996003709)
      ·
        refine ⟨153824292331726123501391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410198112884602996003709 153824292331726123501391)
        ·
          refine ⟨230736438497589185252087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153824292331726123501391 230736438497589185252087)
          ·
            refine ⟨346104657746383777878131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230736438497589185252087 346104657746383777878131)
            ·
              refine ⟨519156986619575666817197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346104657746383777878131 519156986619575666817197)
              ·
                refine ⟨194683869982340875056449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 519156986619575666817197 194683869982340875056449)
                ·
                  refine ⟨146012902486755656292337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194683869982340875056449 146012902486755656292337)
                  ·
                    refine ⟨109509676865066742219253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146012902486755656292337 109509676865066742219253)
                    ·
                      refine ⟨10266532206100007083055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 109509676865066742219253 10266532206100007083055)
                      ·
                        rfl

theorem cell23_19994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_19994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_19994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_19994 prefixEnd_19994 := by exact prefixLift 19994
  have htrace : WordTrace (prefixWord ++ tailWord_19994) baseStart_19994 baseEnd_19994 := by
    simpa [prefixWord, tailWord_19994, baseEnd_19994] using wordTrace_append hprefix tailTrace_19994
  have hstable : (prefixWord ++ tailWord_19994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19994).length < 2 ^ (prefixWord ++ tailWord_19994).sum := by decide
  have hdescent : baseEnd_19994 < baseStart_19994 := by decide
  rcases family_descends (prefixWord ++ tailWord_19994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20071 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_20071 : Nat := 118140960795 + 20071 * 2 ^ 59
def prefixEnd_20071 : Nat := 4983230072969 + 3 ^ 40 * 20071 * 2
def baseEnd_20071 : Nat := 10306070216496205820201

theorem tailTrace_20071 : CollatzResearch.WordTrace tailWord_20071 prefixEnd_20071 10306070216496205820201 := by
  unfold tailWord_20071
  simp only [CollatzResearch.WordTrace]
  refine ⟨732049510293669699004067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 488033006862446466002711 732049510293669699004067)
  ·
    refine ⟨1098074265440504548506101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 732049510293669699004067 1098074265440504548506101)
    ·
      refine ⟨102944462385047301422447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1098074265440504548506101 102944462385047301422447)
      ·
        refine ⟨154416693577570952133671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102944462385047301422447 154416693577570952133671)
        ·
          refine ⟨231625040366356428200507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154416693577570952133671 231625040366356428200507)
          ·
            refine ⟨347437560549534642300761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231625040366356428200507 347437560549534642300761)
            ·
              refine ⟨260578170412150981725571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347437560549534642300761 260578170412150981725571)
              ·
                refine ⟨390867255618226472588357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260578170412150981725571 390867255618226472588357)
                ·
                  refine ⟨73287610428417463610317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390867255618226472588357 73287610428417463610317)
                  ·
                    refine ⟨27482853910656548853869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73287610428417463610317 27482853910656548853869)
                    ·
                      refine ⟨10306070216496205820201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 27482853910656548853869 10306070216496205820201)
                      ·
                        rfl

theorem cell23_20071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_20071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20071 prefixEnd_20071 := by exact prefixLift 20071
  have htrace : WordTrace (prefixWord ++ tailWord_20071) baseStart_20071 baseEnd_20071 := by
    simpa [prefixWord, tailWord_20071, baseEnd_20071] using wordTrace_append hprefix tailTrace_20071
  have hstable : (prefixWord ++ tailWord_20071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20071).length < 2 ^ (prefixWord ++ tailWord_20071).sum := by decide
  have hdescent : baseEnd_20071 < baseStart_20071 := by decide
  rcases family_descends (prefixWord ++ tailWord_20071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20121 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 7, 4]
def baseStart_20121 : Nat := 118140960795 + 20121 * 2 ^ 59
def prefixEnd_20121 : Nat := 4983230072969 + 3 ^ 40 * 20121 * 2
def baseEnd_20121 : Nat := 3443914749740336731657

theorem tailTrace_20121 : CollatzResearch.WordTrace tailWord_20121 prefixEnd_20121 3443914749740336731657 := by
  unfold tailWord_20121
  simp only [CollatzResearch.WordTrace]
  refine ⟨733873160112528238324217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 489248773408352158882811 733873160112528238324217)
  ·
    refine ⟨550404870084396178743163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 733873160112528238324217 550404870084396178743163)
    ·
      refine ⟨825607305126594268114745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 550404870084396178743163 825607305126594268114745)
      ·
        refine ⟨619205478844945701086059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 825607305126594268114745 619205478844945701086059)
        ·
          refine ⟨928808218267418551629089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619205478844945701086059 928808218267418551629089)
          ·
            refine ⟨696606163700563913721817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928808218267418551629089 696606163700563913721817)
            ·
              refine ⟨522454622775422935291363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696606163700563913721817 522454622775422935291363)
              ·
                refine ⟨783681934163134402937045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522454622775422935291363 783681934163134402937045)
                ·
                  refine ⟨18367545331948462568837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 783681934163134402937045 18367545331948462568837)
                  ·
                    refine ⟨3443914749740336731657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18367545331948462568837 3443914749740336731657)
                    ·
                      rfl

theorem cell23_20121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 4].length) (baseStart_20121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20121 prefixEnd_20121 := by exact prefixLift 20121
  have htrace : WordTrace (prefixWord ++ tailWord_20121) baseStart_20121 baseEnd_20121 := by
    simpa [prefixWord, tailWord_20121, baseEnd_20121] using wordTrace_append hprefix tailTrace_20121
  have hstable : (prefixWord ++ tailWord_20121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20121).length < 2 ^ (prefixWord ++ tailWord_20121).sum := by decide
  have hdescent : baseEnd_20121 < baseStart_20121 := by decide
  rcases family_descends (prefixWord ++ tailWord_20121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20128 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 4]
def baseStart_20128 : Nat := 118140960795 + 20128 * 2 ^ 59
def prefixEnd_20128 : Nat := 4983230072969 + 3 ^ 40 * 20128 * 2
def baseEnd_20128 : Nat := 10335338613802482807439

theorem tailTrace_20128 : CollatzResearch.WordTrace tailWord_20128 prefixEnd_20128 10335338613802482807439 := by
  unfold tailWord_20128
  simp only [CollatzResearch.WordTrace]
  refine ⟨367064235543584216914519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 489418980724778955886025 367064235543584216914519)
  ·
    refine ⟨550596353315376325371779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 367064235543584216914519 550596353315376325371779)
    ·
      refine ⟨825894529973064488057669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 550596353315376325371779 825894529973064488057669)
      ·
        refine ⟨154855224369949591510813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 825894529973064488057669 154855224369949591510813)
        ·
          refine ⟨58070709138731096816555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154855224369949591510813 58070709138731096816555)
          ·
            refine ⟨87106063708096645224833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58070709138731096816555 87106063708096645224833)
            ·
              refine ⟨65329547781072483918625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87106063708096645224833 65329547781072483918625)
              ·
                refine ⟨48997160835804362938969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65329547781072483918625 48997160835804362938969)
                ·
                  refine ⟨36747870626853272204227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48997160835804362938969 36747870626853272204227)
                  ·
                    refine ⟨55121805940279908306341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36747870626853272204227 55121805940279908306341)
                    ·
                      refine ⟨10335338613802482807439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 55121805940279908306341 10335338613802482807439)
                      ·
                        rfl

theorem cell23_20128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_20128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20128 prefixEnd_20128 := by exact prefixLift 20128
  have htrace : WordTrace (prefixWord ++ tailWord_20128) baseStart_20128 baseEnd_20128 := by
    simpa [prefixWord, tailWord_20128, baseEnd_20128] using wordTrace_append hprefix tailTrace_20128
  have hstable : (prefixWord ++ tailWord_20128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20128).length < 2 ^ (prefixWord ++ tailWord_20128).sum := by decide
  have hdescent : baseEnd_20128 < baseStart_20128 := by decide
  rcases family_descends (prefixWord ++ tailWord_20128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20205 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_20205 : Nat := 118140960795 + 20205 * 2 ^ 59
def prefixEnd_20205 : Nat := 4983230072969 + 3 ^ 40 * 20205 * 2
def baseEnd_20205 : Nat := 10374876624198681544585

theorem tailTrace_20205 : CollatzResearch.WordTrace tailWord_20205 prefixEnd_20205 10374876624198681544585 := by
  unfold tailWord_20205
  simp only [CollatzResearch.WordTrace]
  refine ⟨736936891808210584382069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 491291261205473722921379 736936891808210584382069)
  ·
    refine ⟨69087833607019742285819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 736936891808210584382069 69087833607019742285819)
    ·
      refine ⟨103631750410529613428729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69087833607019742285819 103631750410529613428729)
      ·
        refine ⟨77723812807897210071547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103631750410529613428729 77723812807897210071547)
        ·
          refine ⟨116585719211845815107321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77723812807897210071547 116585719211845815107321)
          ·
            refine ⟨87439289408884361330491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116585719211845815107321 87439289408884361330491)
            ·
              refine ⟨131158934113326541995737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87439289408884361330491 131158934113326541995737)
              ·
                refine ⟨98369200584994906496803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131158934113326541995737 98369200584994906496803)
                ·
                  refine ⟨147553800877492359745205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98369200584994906496803 147553800877492359745205)
                  ·
                    refine ⟨13833168832264908726113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 147553800877492359745205 13833168832264908726113)
                    ·
                      refine ⟨10374876624198681544585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13833168832264908726113 10374876624198681544585)
                      ·
                        rfl

theorem cell23_20205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_20205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20205 prefixEnd_20205 := by exact prefixLift 20205
  have htrace : WordTrace (prefixWord ++ tailWord_20205) baseStart_20205 baseEnd_20205 := by
    simpa [prefixWord, tailWord_20205, baseEnd_20205] using wordTrace_append hprefix tailTrace_20205
  have hstable : (prefixWord ++ tailWord_20205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20205).length < 2 ^ (prefixWord ++ tailWord_20205).sum := by decide
  have hdescent : baseEnd_20205 < baseStart_20205 := by decide
  rcases family_descends (prefixWord ++ tailWord_20205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20218 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2]
def baseStart_20218 : Nat := 118140960795 + 20218 * 2 ^ 59
def prefixEnd_20218 : Nat := 4983230072969 + 3 ^ 40 * 20218 * 2
def baseEnd_20218 : Nat := 10381551872707130682025

theorem tailTrace_20218 : CollatzResearch.WordTrace tailWord_20218 prefixEnd_20218 10381551872707130682025 := by
  unfold tailWord_20218
  simp only [CollatzResearch.WordTrace]
  refine ⟨184352760190278451151327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 491607360507409203070205 184352760190278451151327)
  ·
    refine ⟨276529140285417676726991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184352760190278451151327 276529140285417676726991)
    ·
      refine ⟨414793710428126515090487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276529140285417676726991 414793710428126515090487)
      ·
        refine ⟨622190565642189772635731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414793710428126515090487 622190565642189772635731)
        ·
          refine ⟨933285848463284658953597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622190565642189772635731 933285848463284658953597)
          ·
            refine ⟨349982193173731747107599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 933285848463284658953597 349982193173731747107599)
            ·
              refine ⟨524973289760597620661399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349982193173731747107599 524973289760597620661399)
              ·
                refine ⟨787459934640896430992099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524973289760597620661399 787459934640896430992099)
                ·
                  refine ⟨1181189901961344646488149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787459934640896430992099 1181189901961344646488149)
                  ·
                    refine ⟨13842069163609507576033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1181189901961344646488149 13842069163609507576033)
                    ·
                      refine ⟨10381551872707130682025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13842069163609507576033 10381551872707130682025)
                      ·
                        rfl

theorem cell23_20218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2].length) (baseStart_20218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20218 prefixEnd_20218 := by exact prefixLift 20218
  have htrace : WordTrace (prefixWord ++ tailWord_20218) baseStart_20218 baseEnd_20218 := by
    simpa [prefixWord, tailWord_20218, baseEnd_20218] using wordTrace_append hprefix tailTrace_20218
  have hstable : (prefixWord ++ tailWord_20218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20218).length < 2 ^ (prefixWord ++ tailWord_20218).sum := by decide
  have hdescent : baseEnd_20218 < baseStart_20218 := by decide
  rcases family_descends (prefixWord ++ tailWord_20218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20235 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 5, 2, 2]
def baseStart_20235 : Nat := 118140960795 + 20235 * 2 ^ 59
def prefixEnd_20235 : Nat := 4983230072969 + 3 ^ 40 * 20235 * 2
def baseEnd_20235 : Nat := 10390281043833564169447

theorem tailTrace_20235 : CollatzResearch.WordTrace tailWord_20235 prefixEnd_20235 10390281043833564169447 := by
  unfold tailWord_20235
  simp only [CollatzResearch.WordTrace]
  refine ⟨738031081699525707974159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 492020721133017138649439 738031081699525707974159)
  ·
    refine ⟨1107046622549288561961239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 738031081699525707974159 1107046622549288561961239)
    ·
      refine ⟨1660569933823932842941859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1107046622549288561961239 1660569933823932842941859)
      ·
        refine ⟨2490854900735899264412789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660569933823932842941859 2490854900735899264412789)
        ·
          refine ⟨233517646943990556038699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2490854900735899264412789 233517646943990556038699)
          ·
            refine ⟨350276470415985834058049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233517646943990556038699 350276470415985834058049)
            ·
              refine ⟨262707352811989375543537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350276470415985834058049 262707352811989375543537)
              ·
                refine ⟨197030514608992031657653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262707352811989375543537 197030514608992031657653)
                ·
                  refine ⟨18471610744593002967905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197030514608992031657653 18471610744593002967905)
                  ·
                    refine ⟨13853708058444752225929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18471610744593002967905 13853708058444752225929)
                    ·
                      refine ⟨10390281043833564169447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13853708058444752225929 10390281043833564169447)
                      ·
                        rfl

theorem cell23_20235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 2, 2].length) (baseStart_20235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20235 prefixEnd_20235 := by exact prefixLift 20235
  have htrace : WordTrace (prefixWord ++ tailWord_20235) baseStart_20235 baseEnd_20235 := by
    simpa [prefixWord, tailWord_20235, baseEnd_20235] using wordTrace_append hprefix tailTrace_20235
  have hstable : (prefixWord ++ tailWord_20235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20235).length < 2 ^ (prefixWord ++ tailWord_20235).sum := by decide
  have hdescent : baseEnd_20235 < baseStart_20235 := by decide
  rcases family_descends (prefixWord ++ tailWord_20235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20238 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_20238 : Nat := 118140960795 + 20238 * 2 ^ 59
def prefixEnd_20238 : Nat := 4983230072969 + 3 ^ 40 * 20238 * 2
def baseEnd_20238 : Nat := 10391821485797052431933

theorem tailTrace_20238 : CollatzResearch.WordTrace tailWord_20238 prefixEnd_20238 10391821485797052431933 := by
  unfold tailWord_20238
  simp only [CollatzResearch.WordTrace]
  refine ⟨92267562586082152541671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 492093667125771480222245 92267562586082152541671)
  ·
    refine ⟨138401343879123228812507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92267562586082152541671 138401343879123228812507)
    ·
      refine ⟨207602015818684843218761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138401343879123228812507 207602015818684843218761)
      ·
        refine ⟨155701511864013632414071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207602015818684843218761 155701511864013632414071)
        ·
          refine ⟨233552267796020448621107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155701511864013632414071 233552267796020448621107)
          ·
            refine ⟨350328401694030672931661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233552267796020448621107 350328401694030672931661)
            ·
              refine ⟨131373150635261502349373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350328401694030672931661 131373150635261502349373)
              ·
                refine ⟨49264931488223063381015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131373150635261502349373 49264931488223063381015)
                ·
                  refine ⟨73897397232334595071523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49264931488223063381015 73897397232334595071523)
                  ·
                    refine ⟨110846095848501892607285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73897397232334595071523 110846095848501892607285)
                    ·
                      refine ⟨10391821485797052431933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 110846095848501892607285 10391821485797052431933)
                      ·
                        rfl

theorem cell23_20238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_20238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20238 prefixEnd_20238 := by exact prefixLift 20238
  have htrace : WordTrace (prefixWord ++ tailWord_20238) baseStart_20238 baseEnd_20238 := by
    simpa [prefixWord, tailWord_20238, baseEnd_20238] using wordTrace_append hprefix tailTrace_20238
  have hstable : (prefixWord ++ tailWord_20238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20238).length < 2 ^ (prefixWord ++ tailWord_20238).sum := by decide
  have hdescent : baseEnd_20238 < baseStart_20238 := by decide
  rcases family_descends (prefixWord ++ tailWord_20238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20258 : List Nat := [3, 3, 1, 1, 2, 1, 4, 8]
def baseStart_20258 : Nat := 118140960795 + 20258 * 2 ^ 59
def prefixEnd_20258 : Nat := 4983230072969 + 3 ^ 40 * 20258 * 2
def baseEnd_20258 : Nat := 385262633292110154883

theorem tailTrace_20258 : CollatzResearch.WordTrace tailWord_20258 prefixEnd_20258 385262633292110154883 := by
  unfold tailWord_20258
  simp only [CollatzResearch.WordTrace]
  refine ⟨184717490154050159015357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 492579973744133757374285 184717490154050159015357)
  ·
    refine ⟨69269058807768809630759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184717490154050159015357 69269058807768809630759)
    ·
      refine ⟨103903588211653214446139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69269058807768809630759 103903588211653214446139)
      ·
        refine ⟨155855382317479821669209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103903588211653214446139 155855382317479821669209)
        ·
          refine ⟨116891536738109866251907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155855382317479821669209 116891536738109866251907)
          ·
            refine ⟨175337305107164799377861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116891536738109866251907 175337305107164799377861)
            ·
              refine ⟨32875744707593399883349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175337305107164799377861 32875744707593399883349)
              ·
                refine ⟨385262633292110154883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 32875744707593399883349 385262633292110154883)
                ·
                  rfl

theorem cell23_20258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 8].length) (baseStart_20258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20258 prefixEnd_20258 := by exact prefixLift 20258
  have htrace : WordTrace (prefixWord ++ tailWord_20258) baseStart_20258 baseEnd_20258 := by
    simpa [prefixWord, tailWord_20258, baseEnd_20258] using wordTrace_append hprefix tailTrace_20258
  have hstable : (prefixWord ++ tailWord_20258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20258).length < 2 ^ (prefixWord ++ tailWord_20258).sum := by decide
  have hdescent : baseEnd_20258 < baseStart_20258 := by decide
  rcases family_descends (prefixWord ++ tailWord_20258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20271 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 2, 7]
def baseStart_20271 : Nat := 118140960795 + 20271 * 2 ^ 59
def prefixEnd_20271 : Nat := 4983230072969 + 3 ^ 40 * 20271 * 2
def baseEnd_20271 : Nat := 3469588782465141106427

theorem tailTrace_20271 : CollatzResearch.WordTrace tailWord_20271 prefixEnd_20271 3469588782465141106427 := by
  unfold tailWord_20271
  simp only [CollatzResearch.WordTrace]
  refine ⟨739344109569103856284667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 492896073046069237523111 739344109569103856284667)
  ·
    refine ⟨1109016164353655784427001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 739344109569103856284667 1109016164353655784427001)
    ·
      refine ⟨831762123265241838320251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1109016164353655784427001 831762123265241838320251)
      ·
        refine ⟨1247643184897862757480377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831762123265241838320251 1247643184897862757480377)
        ·
          refine ⟨935732388673397068110283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1247643184897862757480377 935732388673397068110283)
          ·
            refine ⟨1403598583010095602165425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935732388673397068110283 1403598583010095602165425)
            ·
              refine ⟨1052698937257571701624069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403598583010095602165425 1052698937257571701624069)
              ·
                refine ⟨197381050735794694054513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1052698937257571701624069 197381050735794694054513)
                ·
                  refine ⟨148035788051846020540885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197381050735794694054513 148035788051846020540885)
                  ·
                    refine ⟨3469588782465141106427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 148035788051846020540885 3469588782465141106427)
                    ·
                      rfl

theorem cell23_20271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_20271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20271 prefixEnd_20271 := by exact prefixLift 20271
  have htrace : WordTrace (prefixWord ++ tailWord_20271) baseStart_20271 baseEnd_20271 := by
    simpa [prefixWord, tailWord_20271, baseEnd_20271] using wordTrace_append hprefix tailTrace_20271
  have hstable : (prefixWord ++ tailWord_20271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20271).length < 2 ^ (prefixWord ++ tailWord_20271).sum := by decide
  have hdescent : baseEnd_20271 < baseStart_20271 := by decide
  rcases family_descends (prefixWord ++ tailWord_20271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20285 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_20285 : Nat := 118140960795 + 20285 * 2 ^ 59
def prefixEnd_20285 : Nat := 4983230072969 + 3 ^ 40 * 20285 * 2
def baseEnd_20285 : Nat := 10415955076558368544217

theorem tailTrace_20285 : CollatzResearch.WordTrace tailWord_20285 prefixEnd_20285 10415955076558368544217 := by
  unfold tailWord_20285
  simp only [CollatzResearch.WordTrace]
  refine ⟨739854731518384247294309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 493236487678922831529539 739854731518384247294309)
  ·
    refine ⟨138722762159697046367683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 739854731518384247294309 138722762159697046367683)
    ·
      refine ⟨208084143239545569551525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138722762159697046367683 208084143239545569551525)
      ·
        refine ⟨39015776857414794290911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208084143239545569551525 39015776857414794290911)
        ·
          refine ⟨58523665286122191436367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39015776857414794290911 58523665286122191436367)
          ·
            refine ⟨87785497929183287154551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58523665286122191436367 87785497929183287154551)
            ·
              refine ⟨131678246893774930731827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87785497929183287154551 131678246893774930731827)
              ·
                refine ⟨197517370340662396097741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131678246893774930731827 197517370340662396097741)
                ·
                  refine ⟨74069013877748398536653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197517370340662396097741 74069013877748398536653)
                  ·
                    refine ⟨27775880204155649451245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74069013877748398536653 27775880204155649451245)
                    ·
                      refine ⟨10415955076558368544217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 27775880204155649451245 10415955076558368544217)
                      ·
                        rfl

theorem cell23_20285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_20285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20285 prefixEnd_20285 := by exact prefixLift 20285
  have htrace : WordTrace (prefixWord ++ tailWord_20285) baseStart_20285 baseEnd_20285 := by
    simpa [prefixWord, tailWord_20285, baseEnd_20285] using wordTrace_append hprefix tailTrace_20285
  have hstable : (prefixWord ++ tailWord_20285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20285).length < 2 ^ (prefixWord ++ tailWord_20285).sum := by decide
  have hdescent : baseEnd_20285 < baseStart_20285 := by decide
  rcases family_descends (prefixWord ++ tailWord_20285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20338 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_20338 : Nat := 118140960795 + 20338 * 2 ^ 59
def prefixEnd_20338 : Nat := 4983230072969 + 3 ^ 40 * 20338 * 2
def baseEnd_20338 : Nat := 10443169551246661181473

theorem tailTrace_20338 : CollatzResearch.WordTrace tailWord_20338 prefixEnd_20338 10443169551246661181473 := by
  unfold tailWord_20338
  simp only [CollatzResearch.WordTrace]
  refine ⟨185446950081593574743417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 494525200217582865982445 185446950081593574743417)
  ·
    refine ⟨139085212561195181057563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185446950081593574743417 139085212561195181057563)
    ·
      refine ⟨208627818841792771586345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139085212561195181057563 208627818841792771586345)
      ·
        refine ⟨156470864131344578689759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208627818841792771586345 156470864131344578689759)
        ·
          refine ⟨234706296197016868034639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156470864131344578689759 234706296197016868034639)
          ·
            refine ⟨352059444295525302051959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234706296197016868034639 352059444295525302051959)
            ·
              refine ⟨528089166443287953077939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352059444295525302051959 528089166443287953077939)
              ·
                refine ⟨792133749664931929616909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528089166443287953077939 792133749664931929616909)
                ·
                  refine ⟨297050156124349473606341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792133749664931929616909 297050156124349473606341)
                  ·
                    refine ⟨55696904273315526301189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 297050156124349473606341 55696904273315526301189)
                    ·
                      refine ⟨10443169551246661181473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 55696904273315526301189 10443169551246661181473)
                      ·
                        rfl

theorem cell23_20338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_20338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20338 prefixEnd_20338 := by exact prefixLift 20338
  have htrace : WordTrace (prefixWord ++ tailWord_20338) baseStart_20338 baseEnd_20338 := by
    simpa [prefixWord, tailWord_20338, baseEnd_20338] using wordTrace_append hprefix tailTrace_20338
  have hstable : (prefixWord ++ tailWord_20338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20338).length < 2 ^ (prefixWord ++ tailWord_20338).sum := by decide
  have hdescent : baseEnd_20338 < baseStart_20338 := by decide
  rcases family_descends (prefixWord ++ tailWord_20338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20353 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_20353 : Nat := 118140960795 + 20353 * 2 ^ 59
def prefixEnd_20353 : Nat := 4983230072969 + 3 ^ 40 * 20353 * 2
def baseEnd_20353 : Nat := 10450871761064102493905

theorem tailTrace_20353 : CollatzResearch.WordTrace tailWord_20353 prefixEnd_20353 10450871761064102493905 := by
  unfold tailWord_20353
  simp only [CollatzResearch.WordTrace]
  refine ⟨742334895272031860769713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 494889930181354573846475 742334895272031860769713)
  ·
    refine ⟨556751171454023895577285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 742334895272031860769713 556751171454023895577285)
    ·
      refine ⟨104390844647629480420741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 556751171454023895577285 104390844647629480420741)
      ·
        refine ⟨19573283371430527578889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104390844647629480420741 19573283371430527578889)
        ·
          refine ⟨14679962528572895684167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19573283371430527578889 14679962528572895684167)
          ·
            refine ⟨22019943792859343526251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14679962528572895684167 22019943792859343526251)
            ·
              refine ⟨33029915689289015289377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22019943792859343526251 33029915689289015289377)
              ·
                refine ⟨24772436766966761467033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33029915689289015289377 24772436766966761467033)
                ·
                  refine ⟨18579327575225071100275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24772436766966761467033 18579327575225071100275)
                  ·
                    refine ⟨27868991362837606650413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18579327575225071100275 27868991362837606650413)
                    ·
                      refine ⟨10450871761064102493905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 27868991362837606650413 10450871761064102493905)
                      ·
                        rfl

theorem cell23_20353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_20353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20353 prefixEnd_20353 := by exact prefixLift 20353
  have htrace : WordTrace (prefixWord ++ tailWord_20353) baseStart_20353 baseEnd_20353 := by
    simpa [prefixWord, tailWord_20353, baseEnd_20353] using wordTrace_append hprefix tailTrace_20353
  have hstable : (prefixWord ++ tailWord_20353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20353).length < 2 ^ (prefixWord ++ tailWord_20353).sum := by decide
  have hdescent : baseEnd_20353 < baseStart_20353 := by decide
  rcases family_descends (prefixWord ++ tailWord_20353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20359 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 4, 2, 2]
def baseStart_20359 : Nat := 118140960795 + 20359 * 2 ^ 59
def prefixEnd_20359 : Nat := 4983230072969 + 3 ^ 40 * 20359 * 2
def baseEnd_20359 : Nat := 10453952644991079018877

theorem tailTrace_20359 : CollatzResearch.WordTrace tailWord_20359 prefixEnd_20359 10453952644991079018877 := by
  unfold tailWord_20359
  simp only [CollatzResearch.WordTrace]
  refine ⟨742553733250294885488131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 495035822166863256992087 742553733250294885488131)
  ·
    refine ⟨1113830599875442328232197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 742553733250294885488131 1113830599875442328232197)
    ·
      refine ⟨208843237476645436543537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1113830599875442328232197 208843237476645436543537)
      ·
        refine ⟨156632428107484077407653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208843237476645436543537 156632428107484077407653)
        ·
          refine ⟨29368580270153264513935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156632428107484077407653 29368580270153264513935)
          ·
            refine ⟨44052870405229896770903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29368580270153264513935 44052870405229896770903)
            ·
              refine ⟨66079305607844845156355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44052870405229896770903 66079305607844845156355)
              ·
                refine ⟨99118958411767267734533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66079305607844845156355 99118958411767267734533)
                ·
                  refine ⟨18584804702206362700225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99118958411767267734533 18584804702206362700225)
                  ·
                    refine ⟨13938603526654772025169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18584804702206362700225 13938603526654772025169)
                    ·
                      refine ⟨10453952644991079018877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13938603526654772025169 10453952644991079018877)
                      ·
                        rfl

theorem cell23_20359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_20359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20359 prefixEnd_20359 := by exact prefixLift 20359
  have htrace : WordTrace (prefixWord ++ tailWord_20359) baseStart_20359 baseEnd_20359 := by
    simpa [prefixWord, tailWord_20359, baseEnd_20359] using wordTrace_append hprefix tailTrace_20359
  have hstable : (prefixWord ++ tailWord_20359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20359).length < 2 ^ (prefixWord ++ tailWord_20359).sum := by decide
  have hdescent : baseEnd_20359 < baseStart_20359 := by decide
  rcases family_descends (prefixWord ++ tailWord_20359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20375 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 3]
def baseStart_20375 : Nat := 118140960795 + 20375 * 2 ^ 59
def prefixEnd_20375 : Nat := 4983230072969 + 3 ^ 40 * 20375 * 2
def baseEnd_20375 : Nat := 10462168335463016418803

theorem tailTrace_20375 : CollatzResearch.WordTrace tailWord_20375 prefixEnd_20375 10462168335463016418803 := by
  unfold tailWord_20375
  simp only [CollatzResearch.WordTrace]
  refine ⟨743137301192329618070579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 495424867461553078713719 743137301192329618070579)
  ·
    refine ⟨1114705951788494427105869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 743137301192329618070579 1114705951788494427105869)
    ·
      refine ⟨418014731920685410164701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1114705951788494427105869 418014731920685410164701)
      ·
        refine ⟨156755524470257028811763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 418014731920685410164701 156755524470257028811763)
        ·
          refine ⟨235133286705385543217645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156755524470257028811763 235133286705385543217645)
          ·
            refine ⟨88174982514519578706617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235133286705385543217645 88174982514519578706617)
            ·
              refine ⟨66131236885889684029963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88174982514519578706617 66131236885889684029963)
              ·
                refine ⟨99196855328834526044945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66131236885889684029963 99196855328834526044945)
                ·
                  refine ⟨74397641496625894533709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99196855328834526044945 74397641496625894533709)
                  ·
                    refine ⟨27899115561234710450141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74397641496625894533709 27899115561234710450141)
                    ·
                      refine ⟨10462168335463016418803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 27899115561234710450141 10462168335463016418803)
                      ·
                        rfl

theorem cell23_20375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_20375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20375 prefixEnd_20375 := by exact prefixLift 20375
  have htrace : WordTrace (prefixWord ++ tailWord_20375) baseStart_20375 baseEnd_20375 := by
    simpa [prefixWord, tailWord_20375, baseEnd_20375] using wordTrace_append hprefix tailTrace_20375
  have hstable : (prefixWord ++ tailWord_20375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20375).length < 2 ^ (prefixWord ++ tailWord_20375).sum := by decide
  have hdescent : baseEnd_20375 < baseStart_20375 := by decide
  rcases family_descends (prefixWord ++ tailWord_20375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20376 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 1, 4, 2]
def baseStart_20376 : Nat := 118140960795 + 20376 * 2 ^ 59
def prefixEnd_20376 : Nat := 4983230072969 + 3 ^ 40 * 20376 * 2
def baseEnd_20376 : Nat := 10462681816117512506299

theorem tailTrace_20376 : CollatzResearch.WordTrace tailWord_20376 prefixEnd_20376 10462681816117512506299 := by
  unfold tailWord_20376
  simp only [CollatzResearch.WordTrace]
  refine ⟨371586887094353394428491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 495449182792471192571321 371586887094353394428491)
  ·
    refine ⟨557380330641530091642737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 371586887094353394428491 557380330641530091642737)
    ·
      refine ⟨418035247981147568732053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 557380330641530091642737 418035247981147568732053)
      ·
        refine ⟨19595402249116292284315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 418035247981147568732053 19595402249116292284315)
        ·
          refine ⟨29393103373674438426473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19595402249116292284315 29393103373674438426473)
          ·
            refine ⟨22044827530255828819855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29393103373674438426473 22044827530255828819855)
            ·
              refine ⟨33067241295383743229783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22044827530255828819855 33067241295383743229783)
              ·
                refine ⟨49600861943075614844675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33067241295383743229783 49600861943075614844675)
                ·
                  refine ⟨74401292914613422267013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49600861943075614844675 74401292914613422267013)
                  ·
                    refine ⟨13950242421490016675065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74401292914613422267013 13950242421490016675065)
                    ·
                      refine ⟨10462681816117512506299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 13950242421490016675065 10462681816117512506299)
                      ·
                        rfl

theorem cell23_20376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_20376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20376 prefixEnd_20376 := by exact prefixLift 20376
  have htrace : WordTrace (prefixWord ++ tailWord_20376) baseStart_20376 baseEnd_20376 := by
    simpa [prefixWord, tailWord_20376, baseEnd_20376] using wordTrace_append hprefix tailTrace_20376
  have hstable : (prefixWord ++ tailWord_20376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20376).length < 2 ^ (prefixWord ++ tailWord_20376).sum := by decide
  have hdescent : baseEnd_20376 < baseStart_20376 := by decide
  rcases family_descends (prefixWord ++ tailWord_20376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20415 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 4]
def baseStart_20415 : Nat := 118140960795 + 20415 * 2 ^ 59
def prefixEnd_20415 : Nat := 4983230072969 + 3 ^ 40 * 20415 * 2
def baseEnd_20415 : Nat := 10482707561642859918619

theorem tailTrace_20415 : CollatzResearch.WordTrace tailWord_20415 prefixEnd_20415 10482707561642859918619 := by
  unfold tailWord_20415
  simp only [CollatzResearch.WordTrace]
  refine ⟨744596221047416449526699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 496397480698277633017799 744596221047416449526699)
  ·
    refine ⟨1116894331571124674290049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 744596221047416449526699 1116894331571124674290049)
    ·
      refine ⟨837670748678343505717537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1116894331571124674290049 837670748678343505717537)
      ·
        refine ⟨628253061508757629288153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 837670748678343505717537 628253061508757629288153)
        ·
          refine ⟨471189796131568221966115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 628253061508757629288153 471189796131568221966115)
          ·
            refine ⟨706784694197352332949173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471189796131568221966115 706784694197352332949173)
            ·
              refine ⟨66261065081001781213985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 706784694197352332949173 66261065081001781213985)
              ·
                refine ⟨49695798810751335910489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66261065081001781213985 49695798810751335910489)
                ·
                  refine ⟨37271849108063501932867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49695798810751335910489 37271849108063501932867)
                  ·
                    refine ⟨55907773662095252899301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37271849108063501932867 55907773662095252899301)
                    ·
                      refine ⟨10482707561642859918619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 55907773662095252899301 10482707561642859918619)
                      ·
                        rfl

theorem cell23_20415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_20415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20415 prefixEnd_20415 := by exact prefixLift 20415
  have htrace : WordTrace (prefixWord ++ tailWord_20415) baseStart_20415 baseEnd_20415 := by
    simpa [prefixWord, tailWord_20415, baseEnd_20415] using wordTrace_append hprefix tailTrace_20415
  have hstable : (prefixWord ++ tailWord_20415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20415).length < 2 ^ (prefixWord ++ tailWord_20415).sum := by decide
  have hdescent : baseEnd_20415 < baseStart_20415 := by decide
  rcases family_descends (prefixWord ++ tailWord_20415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20452 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_20452 : Nat := 118140960795 + 20452 * 2 ^ 59
def prefixEnd_20452 : Nat := 4983230072969 + 3 ^ 40 * 20452 * 2
def baseEnd_20452 : Nat := 10501706345859215155949

theorem tailTrace_20452 : CollatzResearch.WordTrace tailWord_20452 prefixEnd_20452 10501706345859215155949 := by
  unfold tailWord_20452
  simp only [CollatzResearch.WordTrace]
  refine ⟨372972860956685884311805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 497297147942247845749073 372972860956685884311805)
  ·
    refine ⟨139864822858757206616927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 372972860956685884311805 139864822858757206616927)
    ·
      refine ⟨209797234288135809925391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139864822858757206616927 209797234288135809925391)
      ·
        refine ⟨314695851432203714888087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209797234288135809925391 314695851432203714888087)
        ·
          refine ⟨472043777148305572332131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314695851432203714888087 472043777148305572332131)
          ·
            refine ⟨708065665722458358498197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472043777148305572332131 708065665722458358498197)
            ·
              refine ⟨33190578080740235554603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 708065665722458358498197 33190578080740235554603)
              ·
                refine ⟨49785867121110353331905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33190578080740235554603 49785867121110353331905)
                ·
                  refine ⟨37339400340832764998929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49785867121110353331905 37339400340832764998929)
                  ·
                    refine ⟨28004550255624573749197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37339400340832764998929 28004550255624573749197)
                    ·
                      refine ⟨10501706345859215155949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 28004550255624573749197 10501706345859215155949)
                      ·
                        rfl

theorem cell23_20452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_20452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20452 prefixEnd_20452 := by exact prefixLift 20452
  have htrace : WordTrace (prefixWord ++ tailWord_20452) baseStart_20452 baseEnd_20452 := by
    simpa [prefixWord, tailWord_20452, baseEnd_20452] using wordTrace_append hprefix tailTrace_20452
  have hstable : (prefixWord ++ tailWord_20452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20452).length < 2 ^ (prefixWord ++ tailWord_20452).sum := by decide
  have hdescent : baseEnd_20452 < baseStart_20452 := by decide
  rcases family_descends (prefixWord ++ tailWord_20452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20485 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_20485 : Nat := 118140960795 + 20485 * 2 ^ 59
def prefixEnd_20485 : Nat := 4983230072969 + 3 ^ 40 * 20485 * 2
def baseEnd_20485 : Nat := 3506217069152528681099

theorem tailTrace_20485 : CollatzResearch.WordTrace tailWord_20485 prefixEnd_20485 3506217069152528681099 := by
  unfold tailWord_20485
  simp only [CollatzResearch.WordTrace]
  refine ⟨747149330793818404574909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 498099553862545603049939 747149330793818404574909)
  ·
    refine ⟨280180999047681901715591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 747149330793818404574909 280180999047681901715591)
    ·
      refine ⟨420271498571522852573387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280180999047681901715591 420271498571522852573387)
      ·
        refine ⟨630407247857284278860081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420271498571522852573387 630407247857284278860081)
        ·
          refine ⟨472805435892963209145061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630407247857284278860081 472805435892963209145061)
          ·
            refine ⟨88651019229930601714699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 472805435892963209145061 88651019229930601714699)
            ·
              refine ⟨132976528844895902572049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88651019229930601714699 132976528844895902572049)
              ·
                refine ⟨99732396633671926929037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132976528844895902572049 99732396633671926929037)
                ·
                  refine ⟨37399648737626972598389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99732396633671926929037 37399648737626972598389)
                  ·
                    refine ⟨3506217069152528681099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37399648737626972598389 3506217069152528681099)
                    ·
                      rfl

theorem cell23_20485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_20485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20485 prefixEnd_20485 := by exact prefixLift 20485
  have htrace : WordTrace (prefixWord ++ tailWord_20485) baseStart_20485 baseEnd_20485 := by
    simpa [prefixWord, tailWord_20485, baseEnd_20485] using wordTrace_append hprefix tailTrace_20485
  have hstable : (prefixWord ++ tailWord_20485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20485).length < 2 ^ (prefixWord ++ tailWord_20485).sum := by decide
  have hdescent : baseEnd_20485 < baseStart_20485 := by decide
  rcases family_descends (prefixWord ++ tailWord_20485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20492 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 1, 5, 2]
def baseStart_20492 : Nat := 118140960795 + 20492 * 2 ^ 59
def prefixEnd_20492 : Nat := 4983230072969 + 3 ^ 40 * 20492 * 2
def baseEnd_20492 : Nat := 10522245572039058655765

theorem tailTrace_20492 : CollatzResearch.WordTrace tailWord_20492 prefixEnd_20492 10522245572039058655765 := by
  unfold tailWord_20492
  simp only [CollatzResearch.WordTrace]
  refine ⟨373702320884229300039865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 498269761178972400053153 373702320884229300039865)
  ·
    refine ⟨280276740663171975029899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 373702320884229300039865 280276740663171975029899)
    ·
      refine ⟨420415110994757962544849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280276740663171975029899 420415110994757962544849)
      ·
        refine ⟨315311333246068471908637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420415110994757962544849 315311333246068471908637)
        ·
          refine ⟨118241749967275676965739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315311333246068471908637 118241749967275676965739)
          ·
            refine ⟨177362624950913515448609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118241749967275676965739 177362624950913515448609)
            ·
              refine ⟨133021968713185136586457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177362624950913515448609 133021968713185136586457)
              ·
                refine ⟨99766476534888852439843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133021968713185136586457 99766476534888852439843)
                ·
                  refine ⟨149649714802333278659765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99766476534888852439843 149649714802333278659765)
                  ·
                    refine ⟨14029660762718744874353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149649714802333278659765 14029660762718744874353)
                    ·
                      refine ⟨10522245572039058655765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14029660762718744874353 10522245572039058655765)
                      ·
                        rfl

theorem cell23_20492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_20492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20492 prefixEnd_20492 := by exact prefixLift 20492
  have htrace : WordTrace (prefixWord ++ tailWord_20492) baseStart_20492 baseEnd_20492 := by
    simpa [prefixWord, tailWord_20492, baseEnd_20492] using wordTrace_append hprefix tailTrace_20492
  have hstable : (prefixWord ++ tailWord_20492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20492).length < 2 ^ (prefixWord ++ tailWord_20492).sum := by decide
  have hdescent : baseEnd_20492 < baseStart_20492 := by decide
  rcases family_descends (prefixWord ++ tailWord_20492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20493 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_20493 : Nat := 118140960795 + 20493 * 2 ^ 59
def prefixEnd_20493 : Nat := 4983230072969 + 3 ^ 40 * 20493 * 2
def baseEnd_20493 : Nat := 3507586350897851581087

theorem tailTrace_20493 : CollatzResearch.WordTrace tailWord_20493 prefixEnd_20493 3507586350897851581087 := by
  unfold tailWord_20493
  simp only [CollatzResearch.WordTrace]
  refine ⟨747441114764835770866133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 498294076509890513910755 747441114764835770866133)
  ·
    refine ⟨17518151127300838379675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 747441114764835770866133 17518151127300838379675)
    ·
      refine ⟨26277226690951257569513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17518151127300838379675 26277226690951257569513)
      ·
        refine ⟨19707920018213443177135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26277226690951257569513 19707920018213443177135)
        ·
          refine ⟨29561880027320164765703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19707920018213443177135 29561880027320164765703)
          ·
            refine ⟨44342820040980247148555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29561880027320164765703 44342820040980247148555)
            ·
              refine ⟨66514230061470370722833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44342820040980247148555 66514230061470370722833)
              ·
                refine ⟨49885672546102778042125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66514230061470370722833 49885672546102778042125)
                ·
                  refine ⟨18707127204788541765797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49885672546102778042125 18707127204788541765797)
                  ·
                    refine ⟨3507586350897851581087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18707127204788541765797 3507586350897851581087)
                    ·
                      rfl

theorem cell23_20493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_20493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20493 prefixEnd_20493 := by exact prefixLift 20493
  have htrace : WordTrace (prefixWord ++ tailWord_20493) baseStart_20493 baseEnd_20493 := by
    simpa [prefixWord, tailWord_20493, baseEnd_20493] using wordTrace_append hprefix tailTrace_20493
  have hstable : (prefixWord ++ tailWord_20493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20493).length < 2 ^ (prefixWord ++ tailWord_20493).sum := by decide
  have hdescent : baseEnd_20493 < baseStart_20493 := by decide
  rcases family_descends (prefixWord ++ tailWord_20493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20509 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_20509 : Nat := 118140960795 + 20509 * 2 ^ 59
def prefixEnd_20509 : Nat := 4983230072969 + 3 ^ 40 * 20509 * 2
def baseEnd_20509 : Nat := 10530974743165492143187

theorem tailTrace_20509 : CollatzResearch.WordTrace tailWord_20509 prefixEnd_20509 10530974743165492143187 := by
  unfold tailWord_20509
  simp only [CollatzResearch.WordTrace]
  refine ⟨748024682706870503448581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 498683121804580335632387 748024682706870503448581)
  ·
    refine ⟨140254628007538219396609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 748024682706870503448581 140254628007538219396609)
    ·
      refine ⟨105190971005653664547457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140254628007538219396609 105190971005653664547457)
      ·
        refine ⟨78893228254240248410593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105190971005653664547457 78893228254240248410593)
        ·
          refine ⟨59169921190680186307945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78893228254240248410593 59169921190680186307945)
          ·
            refine ⟨44377440893010139730959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59169921190680186307945 44377440893010139730959)
            ·
              refine ⟨66566161339515209596439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44377440893010139730959 66566161339515209596439)
              ·
                refine ⟨99849242009272814394659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66566161339515209596439 99849242009272814394659)
                ·
                  refine ⟨149773863013909221591989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99849242009272814394659 149773863013909221591989)
                  ·
                    refine ⟨14041299657553989524249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149773863013909221591989 14041299657553989524249)
                    ·
                      refine ⟨10530974743165492143187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14041299657553989524249 10530974743165492143187)
                      ·
                        rfl

theorem cell23_20509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_20509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20509 prefixEnd_20509 := by exact prefixLift 20509
  have htrace : WordTrace (prefixWord ++ tailWord_20509) baseStart_20509 baseEnd_20509 := by
    simpa [prefixWord, tailWord_20509, baseEnd_20509] using wordTrace_append hprefix tailTrace_20509
  have hstable : (prefixWord ++ tailWord_20509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20509).length < 2 ^ (prefixWord ++ tailWord_20509).sum := by decide
  have hdescent : baseEnd_20509 < baseStart_20509 := by decide
  rcases family_descends (prefixWord ++ tailWord_20509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20515 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 1, 6]
def baseStart_20515 : Nat := 118140960795 + 20515 * 2 ^ 59
def prefixEnd_20515 : Nat := 4983230072969 + 3 ^ 40 * 20515 * 2
def baseEnd_20515 : Nat := 3511351875697489556053

theorem tailTrace_20515 : CollatzResearch.WordTrace tailWord_20515 prefixEnd_20515 3511351875697489556053 := by
  unfold tailWord_20515
  simp only [CollatzResearch.WordTrace]
  refine ⟨748243520685133528166999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 498829013790089018777999 748243520685133528166999)
  ·
    refine ⟨1122365281027700292250499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 748243520685133528166999 1122365281027700292250499)
    ·
      refine ⟨1683547921541550438375749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122365281027700292250499 1683547921541550438375749)
      ·
        refine ⟨315665235289040707195453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1683547921541550438375749 315665235289040707195453)
        ·
          refine ⟨118374463233390265198295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315665235289040707195453 118374463233390265198295)
          ·
            refine ⟨177561694850085397797443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118374463233390265198295 177561694850085397797443)
            ·
              refine ⟨266342542275128096696165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177561694850085397797443 266342542275128096696165)
              ·
                refine ⟨49939226676586518130531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266342542275128096696165 49939226676586518130531)
                ·
                  refine ⟨74908840014879777195797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49939226676586518130531 74908840014879777195797)
                  ·
                    refine ⟨3511351875697489556053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74908840014879777195797 3511351875697489556053)
                    ·
                      rfl

theorem cell23_20515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 6].length) (baseStart_20515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20515 prefixEnd_20515 := by exact prefixLift 20515
  have htrace : WordTrace (prefixWord ++ tailWord_20515) baseStart_20515 baseEnd_20515 := by
    simpa [prefixWord, tailWord_20515, baseEnd_20515] using wordTrace_append hprefix tailTrace_20515
  have hstable : (prefixWord ++ tailWord_20515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20515).length < 2 ^ (prefixWord ++ tailWord_20515).sum := by decide
  have hdescent : baseEnd_20515 < baseStart_20515 := by decide
  rcases family_descends (prefixWord ++ tailWord_20515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20535 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_20535 : Nat := 118140960795 + 20535 * 2 ^ 59
def prefixEnd_20535 : Nat := 4983230072969 + 3 ^ 40 * 20535 * 2
def baseEnd_20535 : Nat := 10544325240182390418067

theorem tailTrace_20535 : CollatzResearch.WordTrace tailWord_20535 prefixEnd_20535 10544325240182390418067 := by
  unfold tailWord_20535
  simp only [CollatzResearch.WordTrace]
  refine ⟨748972980612676943895059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 499315320408451295930039 748972980612676943895059)
  ·
    refine ⟨1123459470919015415842589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 748972980612676943895059 1123459470919015415842589)
    ·
      refine ⟨421297301594630780940971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1123459470919015415842589 421297301594630780940971)
      ·
        refine ⟨631945952391946171411457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421297301594630780940971 631945952391946171411457)
        ·
          refine ⟨473959464293959628558593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631945952391946171411457 473959464293959628558593)
          ·
            refine ⟨355469598220469721418945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473959464293959628558593 355469598220469721418945)
            ·
              refine ⟨266602198665352291064209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355469598220469721418945 266602198665352291064209)
              ·
                refine ⟨199951648999014218298157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266602198665352291064209 199951648999014218298157)
                ·
                  refine ⟨74981868374630331861809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199951648999014218298157 74981868374630331861809)
                  ·
                    refine ⟨56236401280972748896357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74981868374630331861809 56236401280972748896357)
                    ·
                      refine ⟨10544325240182390418067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 56236401280972748896357 10544325240182390418067)
                      ·
                        rfl

theorem cell23_20535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_20535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20535 prefixEnd_20535 := by exact prefixLift 20535
  have htrace : WordTrace (prefixWord ++ tailWord_20535) baseStart_20535 baseEnd_20535 := by
    simpa [prefixWord, tailWord_20535, baseEnd_20535] using wordTrace_append hprefix tailTrace_20535
  have hstable : (prefixWord ++ tailWord_20535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20535).length < 2 ^ (prefixWord ++ tailWord_20535).sum := by decide
  have hdescent : baseEnd_20535 < baseStart_20535 := by decide
  rcases family_descends (prefixWord ++ tailWord_20535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20562 : List Nat := [3, 2, 2, 1, 4, 1, 1, 9]
def baseStart_20562 : Nat := 118140960795 + 20562 * 2 ^ 59
def prefixEnd_20562 : Nat := 4983230072969 + 3 ^ 40 * 20562 * 2
def baseEnd_20562 : Nat := 391044045105695732609

theorem tailTrace_20562 : CollatzResearch.WordTrace tailWord_20562 prefixEnd_20562 391044045105695732609 := by
  unfold tailWord_20562
  simp only [CollatzResearch.WordTrace]
  refine ⟨187489437878715138781985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 499971834343240370085293 187489437878715138781985)
  ·
    refine ⟨140617078409036354086489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187489437878715138781985 140617078409036354086489)
    ·
      refine ⟨105462808806777265564867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140617078409036354086489 105462808806777265564867)
      ·
        refine ⟨158194213210165898347301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105462808806777265564867 158194213210165898347301)
        ·
          refine ⟨29661414976906105940119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158194213210165898347301 29661414976906105940119)
          ·
            refine ⟨44492122465359158910179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29661414976906105940119 44492122465359158910179)
            ·
              refine ⟨66738183698038738365269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44492122465359158910179 66738183698038738365269)
              ·
                refine ⟨391044045105695732609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 66738183698038738365269 391044045105695732609)
                ·
                  rfl

theorem cell23_20562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 9].length) (baseStart_20562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20562 prefixEnd_20562 := by exact prefixLift 20562
  have htrace : WordTrace (prefixWord ++ tailWord_20562) baseStart_20562 baseEnd_20562 := by
    simpa [prefixWord, tailWord_20562, baseEnd_20562] using wordTrace_append hprefix tailTrace_20562
  have hstable : (prefixWord ++ tailWord_20562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20562).length < 2 ^ (prefixWord ++ tailWord_20562).sum := by decide
  have hdescent : baseEnd_20562 < baseStart_20562 := by decide
  rcases family_descends (prefixWord ++ tailWord_20562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20566 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_20566 : Nat := 118140960795 + 20566 * 2 ^ 59
def prefixEnd_20566 : Nat := 4983230072969 + 3 ^ 40 * 20566 * 2
def baseEnd_20566 : Nat := 3520081046823923043475

theorem tailTrace_20566 : CollatzResearch.WordTrace tailWord_20566 prefixEnd_20566 3520081046823923043475 := by
  unfold tailWord_20566
  simp only [CollatzResearch.WordTrace]
  refine ⟨46881477718773077392097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 500069095666912825515701 46881477718773077392097)
  ·
    refine ⟨35161108289079808044073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46881477718773077392097 35161108289079808044073)
    ·
      refine ⟨26370831216809856033055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35161108289079808044073 26370831216809856033055)
      ·
        refine ⟨39556246825214784049583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26370831216809856033055 39556246825214784049583)
        ·
          refine ⟨59334370237822176074375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39556246825214784049583 59334370237822176074375)
          ·
            refine ⟨89001555356733264111563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59334370237822176074375 89001555356733264111563)
            ·
              refine ⟨133502333035099896167345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89001555356733264111563 133502333035099896167345)
              ·
                refine ⟨100126749776324922125509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133502333035099896167345 100126749776324922125509)
                ·
                  refine ⟨18773765583060922898533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100126749776324922125509 18773765583060922898533)
                  ·
                    refine ⟨3520081046823923043475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18773765583060922898533 3520081046823923043475)
                    ·
                      rfl

theorem cell23_20566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_20566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20566 prefixEnd_20566 := by exact prefixLift 20566
  have htrace : WordTrace (prefixWord ++ tailWord_20566) baseStart_20566 baseEnd_20566 := by
    simpa [prefixWord, tailWord_20566, baseEnd_20566] using wordTrace_append hprefix tailTrace_20566
  have hstable : (prefixWord ++ tailWord_20566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20566).length < 2 ^ (prefixWord ++ tailWord_20566).sum := by decide
  have hdescent : baseEnd_20566 < baseStart_20566 := by decide
  rcases family_descends (prefixWord ++ tailWord_20566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20585 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_20585 : Nat := 118140960795 + 20585 * 2 ^ 59
def prefixEnd_20585 : Nat := 4983230072969 + 3 ^ 40 * 20585 * 2
def baseEnd_20585 : Nat := 10569999272907194792837

theorem tailTrace_20585 : CollatzResearch.WordTrace tailWord_20585 prefixEnd_20585 10569999272907194792837 := by
  unfold tailWord_20585
  simp only [CollatzResearch.WordTrace]
  refine ⟨750796630431535483215209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 500531086954356988810139 750796630431535483215209)
  ·
    refine ⟨563097472823651612411407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 750796630431535483215209 563097472823651612411407)
    ·
      refine ⟨844646209235477418617111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563097472823651612411407 844646209235477418617111)
      ·
        refine ⟨1266969313853216127925667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844646209235477418617111 1266969313853216127925667)
        ·
          refine ⟨1900453970779824191888501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266969313853216127925667 1900453970779824191888501)
          ·
            refine ⟨178167559760608517989547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1900453970779824191888501 178167559760608517989547)
            ·
              refine ⟨267251339640912776984321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178167559760608517989547 267251339640912776984321)
              ·
                refine ⟨200438504730684582738241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267251339640912776984321 200438504730684582738241)
                ·
                  refine ⟨150328878548013437053681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200438504730684582738241 150328878548013437053681)
                  ·
                    refine ⟨112746658911010077790261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 150328878548013437053681 112746658911010077790261)
                    ·
                      refine ⟨10569999272907194792837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 112746658911010077790261 10569999272907194792837)
                      ·
                        rfl

theorem cell23_20585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_20585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20585 prefixEnd_20585 := by exact prefixLift 20585
  have htrace : WordTrace (prefixWord ++ tailWord_20585) baseStart_20585 baseEnd_20585 := by
    simpa [prefixWord, tailWord_20585, baseEnd_20585] using wordTrace_append hprefix tailTrace_20585
  have hstable : (prefixWord ++ tailWord_20585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20585).length < 2 ^ (prefixWord ++ tailWord_20585).sum := by decide
  have hdescent : baseEnd_20585 < baseStart_20585 := by decide
  rcases family_descends (prefixWord ++ tailWord_20585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20589 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_20589 : Nat := 118140960795 + 20589 * 2 ^ 59
def prefixEnd_20589 : Nat := 4983230072969 + 3 ^ 40 * 20589 * 2
def baseEnd_20589 : Nat := 10572053195525179142819

theorem tailTrace_20589 : CollatzResearch.WordTrace tailWord_20589 prefixEnd_20589 10572053195525179142819 := by
  unfold tailWord_20589
  simp only [CollatzResearch.WordTrace]
  refine ⟨750942522417044166360821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 500628348278029444240547 750942522417044166360821)
  ·
    refine ⟨70400861476597890596327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 750942522417044166360821 70400861476597890596327)
    ·
      refine ⟨105601292214896835894491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70400861476597890596327 105601292214896835894491)
      ·
        refine ⟨158401938322345253841737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105601292214896835894491 158401938322345253841737)
        ·
          refine ⟨118801453741758940381303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158401938322345253841737 118801453741758940381303)
          ·
            refine ⟨178202180612638410571955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118801453741758940381303 178202180612638410571955)
            ·
              refine ⟨267303270918957615857933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178202180612638410571955 267303270918957615857933)
              ·
                refine ⟨100238726594609105946725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267303270918957615857933 100238726594609105946725)
                ·
                  refine ⟨18794761236489207365011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100238726594609105946725 18794761236489207365011)
                  ·
                    refine ⟨28192141854733811047517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18794761236489207365011 28192141854733811047517)
                    ·
                      refine ⟨10572053195525179142819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 28192141854733811047517 10572053195525179142819)
                      ·
                        rfl

theorem cell23_20589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_20589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20589 prefixEnd_20589 := by exact prefixLift 20589
  have htrace : WordTrace (prefixWord ++ tailWord_20589) baseStart_20589 baseEnd_20589 := by
    simpa [prefixWord, tailWord_20589, baseEnd_20589] using wordTrace_append hprefix tailTrace_20589
  have hstable : (prefixWord ++ tailWord_20589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20589).length < 2 ^ (prefixWord ++ tailWord_20589).sum := by decide
  have hdescent : baseEnd_20589 < baseStart_20589 := by decide
  rcases family_descends (prefixWord ++ tailWord_20589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20590 : List Nat := [4, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_20590 : Nat := 118140960795 + 20590 * 2 ^ 59
def prefixEnd_20590 : Nat := 4983230072969 + 3 ^ 40 * 20590 * 2
def baseEnd_20590 : Nat := 10572566676179675230315

theorem tailTrace_20590 : CollatzResearch.WordTrace tailWord_20590 prefixEnd_20590 10572566676179675230315 := by
  unfold tailWord_20590
  simp only [CollatzResearch.WordTrace]
  refine ⟨93872374426677667143403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 500652663608947558098149 93872374426677667143403)
  ·
    refine ⟨140808561640016500715105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93872374426677667143403 140808561640016500715105)
    ·
      refine ⟨105606421230012375536329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140808561640016500715105 105606421230012375536329)
      ·
        refine ⟨79204815922509281652247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105606421230012375536329 79204815922509281652247)
        ·
          refine ⟨118807223883763922478371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79204815922509281652247 118807223883763922478371)
          ·
            refine ⟨178210835825645883717557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118807223883763922478371 178210835825645883717557)
            ·
              refine ⟨16707265858654301598521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178210835825645883717557 16707265858654301598521)
              ·
                refine ⟨12530449393990726198891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16707265858654301598521 12530449393990726198891)
                ·
                  refine ⟨18795674090986089298337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12530449393990726198891 18795674090986089298337)
                  ·
                    refine ⟨14096755568239566973753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18795674090986089298337 14096755568239566973753)
                    ·
                      refine ⟨10572566676179675230315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14096755568239566973753 10572566676179675230315)
                      ·
                        rfl

theorem cell23_20590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_20590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20590 prefixEnd_20590 := by exact prefixLift 20590
  have htrace : WordTrace (prefixWord ++ tailWord_20590) baseStart_20590 baseEnd_20590 := by
    simpa [prefixWord, tailWord_20590, baseEnd_20590] using wordTrace_append hprefix tailTrace_20590
  have hstable : (prefixWord ++ tailWord_20590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20590).length < 2 ^ (prefixWord ++ tailWord_20590).sum := by decide
  have hdescent : baseEnd_20590 < baseStart_20590 := by decide
  rcases family_descends (prefixWord ++ tailWord_20590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20616 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 3, 3, 2]
def baseStart_20616 : Nat := 118140960795 + 20616 * 2 ^ 59
def prefixEnd_20616 : Nat := 4983230072969 + 3 ^ 40 * 20616 * 2
def baseEnd_20616 : Nat := 10585917173196573505195

theorem tailTrace_20616 : CollatzResearch.WordTrace tailWord_20616 prefixEnd_20616 10585917173196573505195 := by
  unfold tailWord_20616
  simp only [CollatzResearch.WordTrace]
  refine ⟨375963646659613888796851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 501284862212818518395801 375963646659613888796851)
  ·
    refine ⟨563945469989420833195277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 375963646659613888796851 563945469989420833195277)
    ·
      refine ⟨211479551246032812448229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 563945469989420833195277 211479551246032812448229)
      ·
        refine ⟨39652415858631152334043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211479551246032812448229 39652415858631152334043)
        ·
          refine ⟨59478623787946728501065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39652415858631152334043 59478623787946728501065)
          ·
            refine ⟨44608967840960046375799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59478623787946728501065 44608967840960046375799)
            ·
              refine ⟨66913451761440069563699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44608967840960046375799 66913451761440069563699)
              ·
                refine ⟨100370177642160104345549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66913451761440069563699 100370177642160104345549)
                ·
                  refine ⟨37638816615810039129581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100370177642160104345549 37638816615810039129581)
                  ·
                    refine ⟨14114556230928764673593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37638816615810039129581 14114556230928764673593)
                    ·
                      refine ⟨10585917173196573505195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14114556230928764673593 10585917173196573505195)
                      ·
                        rfl

theorem cell23_20616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_20616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20616 prefixEnd_20616 := by exact prefixLift 20616
  have htrace : WordTrace (prefixWord ++ tailWord_20616) baseStart_20616 baseEnd_20616 := by
    simpa [prefixWord, tailWord_20616, baseEnd_20616] using wordTrace_append hprefix tailTrace_20616
  have hstable : (prefixWord ++ tailWord_20616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20616).length < 2 ^ (prefixWord ++ tailWord_20616).sum := by decide
  have hdescent : baseEnd_20616 < baseStart_20616 := by decide
  rcases family_descends (prefixWord ++ tailWord_20616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20629 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 1, 4, 2]
def baseStart_20629 : Nat := 118140960795 + 20629 * 2 ^ 59
def prefixEnd_20629 : Nat := 4983230072969 + 3 ^ 40 * 20629 * 2
def baseEnd_20629 : Nat := 10592592421705022642635

theorem tailTrace_20629 : CollatzResearch.WordTrace tailWord_20629 prefixEnd_20629 10592592421705022642635 := by
  unfold tailWord_20629
  simp only [CollatzResearch.WordTrace]
  refine ⟨752401442272130997816941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 501600961514753998544627 752401442272130997816941)
  ·
    refine ⟨282150540852049124181353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 752401442272130997816941 282150540852049124181353)
    ·
      refine ⟨211612905639036843136015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282150540852049124181353 211612905639036843136015)
      ·
        refine ⟨317419358458555264704023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211612905639036843136015 317419358458555264704023)
        ·
          refine ⟨476129037687832897056035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317419358458555264704023 476129037687832897056035)
          ·
            refine ⟨714193556531749345584053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476129037687832897056035 714193556531749345584053)
            ·
              refine ⟨66955645924851501148505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 714193556531749345584053 66955645924851501148505)
              ·
                refine ⟨50216734443638625861379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66955645924851501148505 50216734443638625861379)
                ·
                  refine ⟨75325101665457938792069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50216734443638625861379 75325101665457938792069)
                  ·
                    refine ⟨14123456562273363523513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75325101665457938792069 14123456562273363523513)
                    ·
                      refine ⟨10592592421705022642635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14123456562273363523513 10592592421705022642635)
                      ·
                        rfl

theorem cell23_20629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_20629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20629 prefixEnd_20629 := by exact prefixLift 20629
  have htrace : WordTrace (prefixWord ++ tailWord_20629) baseStart_20629 baseEnd_20629 := by
    simpa [prefixWord, tailWord_20629, baseEnd_20629] using wordTrace_append hprefix tailTrace_20629
  have hstable : (prefixWord ++ tailWord_20629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20629).length < 2 ^ (prefixWord ++ tailWord_20629).sum := by decide
  have hdescent : baseEnd_20629 < baseStart_20629 := by decide
  rcases family_descends (prefixWord ++ tailWord_20629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20655 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_20655 : Nat := 118140960795 + 20655 * 2 ^ 59
def prefixEnd_20655 : Nat := 4983230072969 + 3 ^ 40 * 20655 * 2
def baseEnd_20655 : Nat := 10605942918721920917515

theorem tailTrace_20655 : CollatzResearch.WordTrace tailWord_20655 prefixEnd_20655 10605942918721920917515 := by
  unfold tailWord_20655
  simp only [CollatzResearch.WordTrace]
  refine ⟨753349740177937438263419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 502233160118624958842279 753349740177937438263419)
  ·
    refine ⟨1130024610266906157395129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 753349740177937438263419 1130024610266906157395129)
    ·
      refine ⟨847518457700179618046347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1130024610266906157395129 847518457700179618046347)
      ·
        refine ⟨1271277686550269427069521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847518457700179618046347 1271277686550269427069521)
        ·
          refine ⟨953458264912702070302141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1271277686550269427069521 953458264912702070302141)
          ·
            refine ⟨357546849342263276363303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 953458264912702070302141 357546849342263276363303)
            ·
              refine ⟨536320274013394914544955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357546849342263276363303 536320274013394914544955)
              ·
                refine ⟨804480411020092371817433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536320274013394914544955 804480411020092371817433)
                ·
                  refine ⟨603360308265069278863075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 804480411020092371817433 603360308265069278863075)
                  ·
                    refine ⟨905040462397603918294613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 603360308265069278863075 905040462397603918294613)
                    ·
                      refine ⟨10605942918721920917515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 905040462397603918294613 10605942918721920917515)
                      ·
                        rfl

theorem cell23_20655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_20655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20655 prefixEnd_20655 := by exact prefixLift 20655
  have htrace : WordTrace (prefixWord ++ tailWord_20655) baseStart_20655 baseEnd_20655 := by
    simpa [prefixWord, tailWord_20655, baseEnd_20655] using wordTrace_append hprefix tailTrace_20655
  have hstable : (prefixWord ++ tailWord_20655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20655).length < 2 ^ (prefixWord ++ tailWord_20655).sum := by decide
  have hdescent : baseEnd_20655 < baseStart_20655 := by decide
  rcases family_descends (prefixWord ++ tailWord_20655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20682 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_20682 : Nat := 118140960795 + 20682 * 2 ^ 59
def prefixEnd_20682 : Nat := 4983230072969 + 3 ^ 40 * 20682 * 2
def baseEnd_20682 : Nat := 3539935632131105093297

theorem tailTrace_20682 : CollatzResearch.WordTrace tailWord_20682 prefixEnd_20682 3539935632131105093297 := by
  unfold tailWord_20682
  simp only [CollatzResearch.WordTrace]
  refine ⟨188583627770030262374075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 502889674053414032997533 188583627770030262374075)
  ·
    refine ⟨282875441655045393561113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188583627770030262374075 282875441655045393561113)
    ·
      refine ⟨212156581241284045170835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282875441655045393561113 212156581241284045170835)
      ·
        refine ⟨318234871861926067756253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212156581241284045170835 318234871861926067756253)
        ·
          refine ⟨119338076948222275408595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318234871861926067756253 119338076948222275408595)
          ·
            refine ⟨179007115422333413112893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119338076948222275408595 179007115422333413112893)
            ·
              refine ⟨67127668283375029917335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179007115422333413112893 67127668283375029917335)
              ·
                refine ⟨100691502425062544876003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67127668283375029917335 100691502425062544876003)
                ·
                  refine ⟨151037253637593817314005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100691502425062544876003 151037253637593817314005)
                  ·
                    refine ⟨3539935632131105093297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 151037253637593817314005 3539935632131105093297)
                    ·
                      rfl

theorem cell23_20682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_20682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20682 prefixEnd_20682 := by exact prefixLift 20682
  have htrace : WordTrace (prefixWord ++ tailWord_20682) baseStart_20682 baseEnd_20682 := by
    simpa [prefixWord, tailWord_20682, baseEnd_20682] using wordTrace_append hprefix tailTrace_20682
  have hstable : (prefixWord ++ tailWord_20682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20682).length < 2 ^ (prefixWord ++ tailWord_20682).sum := by decide
  have hdescent : baseEnd_20682 < baseStart_20682 := by decide
  rcases family_descends (prefixWord ++ tailWord_20682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20686 : List Nat := [4, 1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_20686 : Nat := 118140960795 + 20686 * 2 ^ 59
def prefixEnd_20686 : Nat := 4983230072969 + 3 ^ 40 * 20686 * 2
def baseEnd_20686 : Nat := 1180206757667922181097

theorem tailTrace_20686 : CollatzResearch.WordTrace tailWord_20686 prefixEnd_20686 1180206757667922181097 := by
  unfold tailWord_20686
  simp only [CollatzResearch.WordTrace]
  refine ⟨94310050383203716580239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 502986935377086488427941 94310050383203716580239)
  ·
    refine ⟨141465075574805574870359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94310050383203716580239 141465075574805574870359)
    ·
      refine ⟨212197613362208362305539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141465075574805574870359 212197613362208362305539)
      ·
        refine ⟨318296420043312543458309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212197613362208362305539 318296420043312543458309)
        ·
          refine ⟨59680578758121101898433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 318296420043312543458309 59680578758121101898433)
          ·
            refine ⟨44760434068590826423825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59680578758121101898433 44760434068590826423825)
            ·
              refine ⟨33570325551443119817869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44760434068590826423825 33570325551443119817869)
              ·
                refine ⟨12588872081791169931701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33570325551443119817869 12588872081791169931701)
                ·
                  refine ⟨1180206757667922181097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12588872081791169931701 1180206757667922181097)
                  ·
                    rfl

theorem cell23_20686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_20686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20686 prefixEnd_20686 := by exact prefixLift 20686
  have htrace : WordTrace (prefixWord ++ tailWord_20686) baseStart_20686 baseEnd_20686 := by
    simpa [prefixWord, tailWord_20686, baseEnd_20686] using wordTrace_append hprefix tailTrace_20686
  have hstable : (prefixWord ++ tailWord_20686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20686).length < 2 ^ (prefixWord ++ tailWord_20686).sum := by decide
  have hdescent : baseEnd_20686 < baseStart_20686 := by decide
  rcases family_descends (prefixWord ++ tailWord_20686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20739 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 3]
def baseStart_20739 : Nat := 118140960795 + 20739 * 2 ^ 59
def prefixEnd_20739 : Nat := 4983230072969 + 3 ^ 40 * 20739 * 2
def baseEnd_20739 : Nat := 10649075293699592267129

theorem tailTrace_20739 : CollatzResearch.WordTrace tailWord_20739 prefixEnd_20739 10649075293699592267129 := by
  unfold tailWord_20739
  simp only [CollatzResearch.WordTrace]
  refine ⟨756413471873619784321271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 504275647915746522880847 756413471873619784321271)
  ·
    refine ⟨1134620207810429676481907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 756413471873619784321271 1134620207810429676481907)
    ·
      refine ⟨1701930311715644514722861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1134620207810429676481907 1701930311715644514722861)
      ·
        refine ⟨638223866893366693021073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1701930311715644514722861 638223866893366693021073)
        ·
          refine ⟨478667900170025019765805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638223866893366693021073 478667900170025019765805)
          ·
            refine ⟨179500462563759382412177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 478667900170025019765805 179500462563759382412177)
            ·
              refine ⟨134625346922819536809133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179500462563759382412177 134625346922819536809133)
              ·
                refine ⟨50484505096057326303425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134625346922819536809133 50484505096057326303425)
                ·
                  refine ⟨37863378822042994727569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50484505096057326303425 37863378822042994727569)
                  ·
                    refine ⟨28397534116532246045677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37863378822042994727569 28397534116532246045677)
                    ·
                      refine ⟨10649075293699592267129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 28397534116532246045677 10649075293699592267129)
                      ·
                        rfl

theorem cell23_20739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_20739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20739 prefixEnd_20739 := by exact prefixLift 20739
  have htrace : WordTrace (prefixWord ++ tailWord_20739) baseStart_20739 baseEnd_20739 := by
    simpa [prefixWord, tailWord_20739, baseEnd_20739] using wordTrace_append hprefix tailTrace_20739
  have hstable : (prefixWord ++ tailWord_20739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20739).length < 2 ^ (prefixWord ++ tailWord_20739).sum := by decide
  have hdescent : baseEnd_20739 < baseStart_20739 := by decide
  rcases family_descends (prefixWord ++ tailWord_20739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20776 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 6]
def baseStart_20776 : Nat := 118140960795 + 20776 * 2 ^ 59
def prefixEnd_20776 : Nat := 4983230072969 + 3 ^ 40 * 20776 * 2
def baseEnd_20776 : Nat := 1185341564212883056051

theorem tailTrace_20776 : CollatzResearch.WordTrace tailWord_20776 prefixEnd_20776 1185341564212883056051 := by
  unfold tailWord_20776
  simp only [CollatzResearch.WordTrace]
  refine ⟨378881486369787551709091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 505175315159716735612121 378881486369787551709091)
  ·
    refine ⟨568322229554681327563637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 378881486369787551709091 568322229554681327563637)
    ·
      refine ⟨53280209020751374459091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 568322229554681327563637 53280209020751374459091)
      ·
        refine ⟨79920313531127061688637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53280209020751374459091 79920313531127061688637)
        ·
          refine ⟨29970117574172648133239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79920313531127061688637 29970117574172648133239)
          ·
            refine ⟨44955176361258972199859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29970117574172648133239 44955176361258972199859)
            ·
              refine ⟨67432764541888458299789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44955176361258972199859 67432764541888458299789)
              ·
                refine ⟨25287286703208171862421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67432764541888458299789 25287286703208171862421)
                ·
                  refine ⟨1185341564212883056051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25287286703208171862421 1185341564212883056051)
                  ·
                    rfl

theorem cell23_20776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 6].length) (baseStart_20776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20776 prefixEnd_20776 := by exact prefixLift 20776
  have htrace : WordTrace (prefixWord ++ tailWord_20776) baseStart_20776 baseEnd_20776 := by
    simpa [prefixWord, tailWord_20776, baseEnd_20776] using wordTrace_append hprefix tailTrace_20776
  have hstable : (prefixWord ++ tailWord_20776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20776).length < 2 ^ (prefixWord ++ tailWord_20776).sum := by decide
  have hdescent : baseEnd_20776 < baseStart_20776 := by decide
  rcases family_descends (prefixWord ++ tailWord_20776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20789 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_20789 : Nat := 118140960795 + 20789 * 2 ^ 59
def prefixEnd_20789 : Nat := 4983230072969 + 3 ^ 40 * 20789 * 2
def baseEnd_20789 : Nat := 3558249775474798880633

theorem tailTrace_20789 : CollatzResearch.WordTrace tailWord_20789 prefixEnd_20789 3558249775474798880633 := by
  unfold tailWord_20789
  simp only [CollatzResearch.WordTrace]
  refine ⟨758237121692478323641421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 505491414461652215760947 758237121692478323641421)
  ·
    refine ⟨284338920634679371365533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 758237121692478323641421 284338920634679371365533)
    ·
      refine ⟨106627095238004764262075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284338920634679371365533 106627095238004764262075)
      ·
        refine ⟨159940642857007146393113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106627095238004764262075 159940642857007146393113)
        ·
          refine ⟨119955482142755359794835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159940642857007146393113 119955482142755359794835)
          ·
            refine ⟨179933223214133039692253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119955482142755359794835 179933223214133039692253)
            ·
              refine ⟨67474958705299889884595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179933223214133039692253 67474958705299889884595)
              ·
                refine ⟨101212438057949834826893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67474958705299889884595 101212438057949834826893)
                ·
                  refine ⟨37954664271731188060085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101212438057949834826893 37954664271731188060085)
                  ·
                    refine ⟨3558249775474798880633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37954664271731188060085 3558249775474798880633)
                    ·
                      rfl

theorem cell23_20789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_20789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20789 prefixEnd_20789 := by exact prefixLift 20789
  have htrace : WordTrace (prefixWord ++ tailWord_20789) baseStart_20789 baseEnd_20789 := by
    simpa [prefixWord, tailWord_20789, baseEnd_20789] using wordTrace_append hprefix tailTrace_20789
  have hstable : (prefixWord ++ tailWord_20789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20789).length < 2 ^ (prefixWord ++ tailWord_20789).sum := by decide
  have hdescent : baseEnd_20789 < baseStart_20789 := by decide
  rcases family_descends (prefixWord ++ tailWord_20789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20820 : List Nat := [2, 4, 1, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_20820 : Nat := 118140960795 + 20820 * 2 ^ 59
def prefixEnd_20820 : Nat := 4983230072969 + 3 ^ 40 * 20820 * 2
def baseEnd_20820 : Nat := 10690667226713775354257

theorem tailTrace_20820 : CollatzResearch.WordTrace tailWord_20820 prefixEnd_20820 10690667226713775354257 := by
  unfold tailWord_20820
  simp only [CollatzResearch.WordTrace]
  refine ⟨379683892290085309009957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 506245189720113745346609 379683892290085309009957)
  ·
    refine ⟨71190729804390995439367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 379683892290085309009957 71190729804390995439367)
    ·
      refine ⟨106786094706586493159051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71190729804390995439367 106786094706586493159051)
      ·
        refine ⟨160179142059879739738577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106786094706586493159051 160179142059879739738577)
        ·
          refine ⟨120134356544909804803933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160179142059879739738577 120134356544909804803933)
          ·
            refine ⟨45050383704341176801475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120134356544909804803933 45050383704341176801475)
            ·
              refine ⟨67575575556511765202213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45050383704341176801475 67575575556511765202213)
              ·
                refine ⟨12670420416845955975415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67575575556511765202213 12670420416845955975415)
                ·
                  refine ⟨19005630625268933963123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12670420416845955975415 19005630625268933963123)
                  ·
                    refine ⟨28508445937903400944685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19005630625268933963123 28508445937903400944685)
                    ·
                      refine ⟨10690667226713775354257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 28508445937903400944685 10690667226713775354257)
                      ·
                        rfl

theorem cell23_20820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_20820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20820 prefixEnd_20820 := by exact prefixLift 20820
  have htrace : WordTrace (prefixWord ++ tailWord_20820) baseStart_20820 baseEnd_20820 := by
    simpa [prefixWord, tailWord_20820, baseEnd_20820] using wordTrace_append hprefix tailTrace_20820
  have hstable : (prefixWord ++ tailWord_20820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20820).length < 2 ^ (prefixWord ++ tailWord_20820).sum := by decide
  have hdescent : baseEnd_20820 < baseStart_20820 := by decide
  rcases family_descends (prefixWord ++ tailWord_20820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20836 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_20836 : Nat := 118140960795 + 20836 * 2 ^ 59
def prefixEnd_20836 : Nat := 4983230072969 + 3 ^ 40 * 20836 * 2
def baseEnd_20836 : Nat := 3566294305728570918061

theorem tailTrace_20836 : CollatzResearch.WordTrace tailWord_20836 prefixEnd_20836 3566294305728570918061 := by
  unfold tailWord_20836
  simp only [CollatzResearch.WordTrace]
  refine ⟨379975676261102675301181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 506634235014803567068241 379975676261102675301181)
  ·
    refine ⟨142490878597913503237943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 379975676261102675301181 142490878597913503237943)
    ·
      refine ⟨213736317896870254856915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142490878597913503237943 213736317896870254856915)
      ·
        refine ⟨320604476845305382285373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213736317896870254856915 320604476845305382285373)
        ·
          refine ⟨120226678816989518357015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320604476845305382285373 120226678816989518357015)
          ·
            refine ⟨180340018225484277535523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120226678816989518357015 180340018225484277535523)
            ·
              refine ⟨270510027338226416303285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180340018225484277535523 270510027338226416303285)
              ·
                refine ⟨25360315062958726528433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270510027338226416303285 25360315062958726528433)
                ·
                  refine ⟨19020236297219044896325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25360315062958726528433 19020236297219044896325)
                  ·
                    refine ⟨3566294305728570918061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19020236297219044896325 3566294305728570918061)
                    ·
                      rfl

theorem cell23_20836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_20836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20836 prefixEnd_20836 := by exact prefixLift 20836
  have htrace : WordTrace (prefixWord ++ tailWord_20836) baseStart_20836 baseEnd_20836 := by
    simpa [prefixWord, tailWord_20836, baseEnd_20836] using wordTrace_append hprefix tailTrace_20836
  have hstable : (prefixWord ++ tailWord_20836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20836).length < 2 ^ (prefixWord ++ tailWord_20836).sum := by decide
  have hdescent : baseEnd_20836 < baseStart_20836 := by decide
  rcases family_descends (prefixWord ++ tailWord_20836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20854 : List Nat := [5, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_20854 : Nat := 118140960795 + 20854 * 2 ^ 59
def prefixEnd_20854 : Nat := 4983230072969 + 3 ^ 40 * 20854 * 2
def baseEnd_20854 : Nat := 10708125568966642329101

theorem tailTrace_20854 : CollatzResearch.WordTrace tailWord_20854 prefixEnd_20854 10708125568966642329101 := by
  unfold tailWord_20854
  simp only [CollatzResearch.WordTrace]
  refine ⟨47537991653562151547351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 507071910971329616505077 47537991653562151547351)
  ·
    refine ⟨71306987480343227321027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47537991653562151547351 71306987480343227321027)
    ·
      refine ⟨106960481220514840981541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71306987480343227321027 106960481220514840981541)
      ·
        refine ⟨20055090228846532684039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106960481220514840981541 20055090228846532684039)
        ·
          refine ⟨30082635343269799026059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20055090228846532684039 30082635343269799026059)
          ·
            refine ⟨45123953014904698539089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30082635343269799026059 45123953014904698539089)
            ·
              refine ⟨33842964761178523904317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45123953014904698539089 33842964761178523904317)
              ·
                refine ⟨12691111785441946464119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33842964761178523904317 12691111785441946464119)
                ·
                  refine ⟨19036667678162919696179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12691111785441946464119 19036667678162919696179)
                  ·
                    refine ⟨28555001517244379544269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19036667678162919696179 28555001517244379544269)
                    ·
                      refine ⟨10708125568966642329101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 28555001517244379544269 10708125568966642329101)
                      ·
                        rfl

theorem cell23_20854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_20854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20854 prefixEnd_20854 := by exact prefixLift 20854
  have htrace : WordTrace (prefixWord ++ tailWord_20854) baseStart_20854 baseEnd_20854 := by
    simpa [prefixWord, tailWord_20854, baseEnd_20854] using wordTrace_append hprefix tailTrace_20854
  have hstable : (prefixWord ++ tailWord_20854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20854).length < 2 ^ (prefixWord ++ tailWord_20854).sum := by decide
  have hdescent : baseEnd_20854 < baseStart_20854 := by decide
  rcases family_descends (prefixWord ++ tailWord_20854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20919 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_20919 : Nat := 118140960795 + 20919 * 2 ^ 59
def prefixEnd_20919 : Nat := 4983230072969 + 3 ^ 40 * 20919 * 2
def baseEnd_20919 : Nat := 10741501811508888016301

theorem tailTrace_20919 : CollatzResearch.WordTrace tailWord_20919 prefixEnd_20919 10741501811508888016301 := by
  unfold tailWord_20919
  simp only [CollatzResearch.WordTrace]
  refine ⟨762978611221510525873811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 508652407481007017249207 762978611221510525873811)
  ·
    refine ⟨1144467916832265788810717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 762978611221510525873811 1144467916832265788810717)
    ·
      refine ⟨429175468812099670804019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1144467916832265788810717 429175468812099670804019)
      ·
        refine ⟨643763203218149506206029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429175468812099670804019 643763203218149506206029)
        ·
          refine ⟨241411201206806064827261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 643763203218149506206029 241411201206806064827261)
          ·
            refine ⟨90529200452552274310223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241411201206806064827261 90529200452552274310223)
            ·
              refine ⟨135793800678828411465335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90529200452552274310223 135793800678828411465335)
              ·
                refine ⟨203690701018242617198003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135793800678828411465335 203690701018242617198003)
                ·
                  refine ⟨305536051527363925797005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203690701018242617198003 305536051527363925797005)
                  ·
                    refine ⟨114576019322761472173877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305536051527363925797005 114576019322761472173877)
                    ·
                      refine ⟨10741501811508888016301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 114576019322761472173877 10741501811508888016301)
                      ·
                        rfl

theorem cell23_20919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_20919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20919 prefixEnd_20919 := by exact prefixLift 20919
  have htrace : WordTrace (prefixWord ++ tailWord_20919) baseStart_20919 baseEnd_20919 := by
    simpa [prefixWord, tailWord_20919, baseEnd_20919] using wordTrace_append hprefix tailTrace_20919
  have hstable : (prefixWord ++ tailWord_20919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20919).length < 2 ^ (prefixWord ++ tailWord_20919).sum := by decide
  have hdescent : baseEnd_20919 < baseStart_20919 := by decide
  rcases family_descends (prefixWord ++ tailWord_20919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20950 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_20950 : Nat := 118140960795 + 20950 * 2 ^ 59
def prefixEnd_20950 : Nat := 4983230072969 + 3 ^ 40 * 20950 * 2
def baseEnd_20950 : Nat := 10757419711798266728659

theorem tailTrace_20950 : CollatzResearch.WordTrace tailWord_20950 prefixEnd_20950 10757419711798266728659 := by
  unfold tailWord_20950
  simp only [CollatzResearch.WordTrace]
  refine ⟨47756829631825176265769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 509406182739468546834869 47756829631825176265769)
  ·
    refine ⟨35817622223868882199327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47756829631825176265769 35817622223868882199327)
    ·
      refine ⟨53726433335803323298991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35817622223868882199327 53726433335803323298991)
      ·
        refine ⟨80589650003704984948487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53726433335803323298991 80589650003704984948487)
        ·
          refine ⟨120884475005557477422731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80589650003704984948487 120884475005557477422731)
          ·
            refine ⟨181326712508336216134097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120884475005557477422731 181326712508336216134097)
            ·
              refine ⟨135995034381252162100573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181326712508336216134097 135995034381252162100573)
              ·
                refine ⟨50998137892969560787715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135995034381252162100573 50998137892969560787715)
                ·
                  refine ⟨76497206839454341181573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50998137892969560787715 76497206839454341181573)
                  ·
                    refine ⟨14343226282397688971545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76497206839454341181573 14343226282397688971545)
                    ·
                      refine ⟨10757419711798266728659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14343226282397688971545 10757419711798266728659)
                      ·
                        rfl

theorem cell23_20950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_20950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20950 prefixEnd_20950 := by exact prefixLift 20950
  have htrace : WordTrace (prefixWord ++ tailWord_20950) baseStart_20950 baseEnd_20950 := by
    simpa [prefixWord, tailWord_20950, baseEnd_20950] using wordTrace_append hprefix tailTrace_20950
  have hstable : (prefixWord ++ tailWord_20950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20950).length < 2 ^ (prefixWord ++ tailWord_20950).sum := by decide
  have hdescent : baseEnd_20950 < baseStart_20950 := by decide
  rcases family_descends (prefixWord ++ tailWord_20950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20979 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 5]
def baseStart_20979 : Nat := 118140960795 + 20979 * 2 ^ 59
def prefixEnd_20979 : Nat := 4983230072969 + 3 ^ 40 * 20979 * 2
def baseEnd_20979 : Nat := 10772310650778653266025

theorem tailTrace_20979 : CollatzResearch.WordTrace tailWord_20979 prefixEnd_20979 10772310650778653266025 := by
  unfold tailWord_20979
  simp only [CollatzResearch.WordTrace]
  refine ⟨765166991004140773057991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 510111327336093848705327 765166991004140773057991)
  ·
    refine ⟨1147750486506211159586987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 765166991004140773057991 1147750486506211159586987)
    ·
      refine ⟨1721625729759316739380481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1147750486506211159586987 1721625729759316739380481)
      ·
        refine ⟨1291219297319487554535361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1721625729759316739380481 1291219297319487554535361)
        ·
          refine ⟨968414472989615665901521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1291219297319487554535361 968414472989615665901521)
          ·
            refine ⟨726310854742211749426141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 968414472989615665901521 726310854742211749426141)
            ·
              refine ⟨272366570528329406034803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 726310854742211749426141 272366570528329406034803)
              ·
                refine ⟨408549855792494109052205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272366570528329406034803 408549855792494109052205)
                ·
                  refine ⟨153206195922185290894577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408549855792494109052205 153206195922185290894577)
                  ·
                    refine ⟨114904646941638968170933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153206195922185290894577 114904646941638968170933)
                    ·
                      refine ⟨10772310650778653266025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 114904646941638968170933 10772310650778653266025)
                      ·
                        rfl

theorem cell23_20979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_20979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20979 prefixEnd_20979 := by exact prefixLift 20979
  have htrace : WordTrace (prefixWord ++ tailWord_20979) baseStart_20979 baseEnd_20979 := by
    simpa [prefixWord, tailWord_20979, baseEnd_20979] using wordTrace_append hprefix tailTrace_20979
  have hstable : (prefixWord ++ tailWord_20979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20979).length < 2 ^ (prefixWord ++ tailWord_20979).sum := by decide
  have hdescent : baseEnd_20979 < baseStart_20979 := by decide
  rcases family_descends (prefixWord ++ tailWord_20979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20993 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_20993 : Nat := 118140960795 + 20993 * 2 ^ 59
def prefixEnd_20993 : Nat := 4983230072969 + 3 ^ 40 * 20993 * 2
def baseEnd_20993 : Nat := 10779499379941598490961

theorem tailTrace_20993 : CollatzResearch.WordTrace tailWord_20993 prefixEnd_20993 10779499379941598490961 := by
  unfold tailWord_20993
  simp only [CollatzResearch.WordTrace]
  refine ⟨765677612953421164067633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 510451741968947442711755 765677612953421164067633)
  ·
    refine ⟨574258209715065873050725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 765677612953421164067633 574258209715065873050725)
    ·
      refine ⟨107673414321574851197011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 574258209715065873050725 107673414321574851197011)
      ·
        refine ⟨161510121482362276795517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107673414321574851197011 161510121482362276795517)
        ·
          refine ⟨60566295555885853798319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161510121482362276795517 60566295555885853798319)
          ·
            refine ⟨90849443333828780697479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60566295555885853798319 90849443333828780697479)
            ·
              refine ⟨136274165000743171046219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90849443333828780697479 136274165000743171046219)
              ·
                refine ⟨204411247501114756569329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136274165000743171046219 204411247501114756569329)
                ·
                  refine ⟨153308435625836067426997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204411247501114756569329 153308435625836067426997)
                  ·
                    refine ⟨14372665839922131321281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 153308435625836067426997 14372665839922131321281)
                    ·
                      refine ⟨10779499379941598490961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14372665839922131321281 10779499379941598490961)
                      ·
                        rfl

theorem cell23_20993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_20993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_20993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_20993 prefixEnd_20993 := by exact prefixLift 20993
  have htrace : WordTrace (prefixWord ++ tailWord_20993) baseStart_20993 baseEnd_20993 := by
    simpa [prefixWord, tailWord_20993, baseEnd_20993] using wordTrace_append hprefix tailTrace_20993
  have hstable : (prefixWord ++ tailWord_20993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20993).length < 2 ^ (prefixWord ++ tailWord_20993).sum := by decide
  have hdescent : baseEnd_20993 < baseStart_20993 := by decide
  rcases family_descends (prefixWord ++ tailWord_20993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21019 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 6]
def baseStart_21019 : Nat := 118140960795 + 21019 * 2 ^ 59
def prefixEnd_21019 : Nat := 4983230072969 + 3 ^ 40 * 21019 * 2
def baseEnd_21019 : Nat := 10792849876958496765841

theorem tailTrace_21019 : CollatzResearch.WordTrace tailWord_21019 prefixEnd_21019 10792849876958496765841 := by
  unfold tailWord_21019
  simp only [CollatzResearch.WordTrace]
  refine ⟨766625910859227604514111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 511083940572818403009407 766625910859227604514111)
  ·
    refine ⟨1149938866288841406771167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 766625910859227604514111 1149938866288841406771167)
    ·
      refine ⟨1724908299433262110156751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149938866288841406771167 1724908299433262110156751)
      ·
        refine ⟨2587362449149893165235127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724908299433262110156751 2587362449149893165235127)
        ·
          refine ⟨3881043673724839747852691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2587362449149893165235127 3881043673724839747852691)
          ·
            refine ⟨5821565510587259621779037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3881043673724839747852691 5821565510587259621779037)
            ·
              refine ⟨2183087066470222358167139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5821565510587259621779037 2183087066470222358167139)
              ·
                refine ⟨3274630599705333537250709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183087066470222358167139 3274630599705333537250709)
                ·
                  refine ⟨153498309361187509558627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3274630599705333537250709 153498309361187509558627)
                  ·
                    refine ⟨230247464041781264337941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 153498309361187509558627 230247464041781264337941)
                    ·
                      refine ⟨10792849876958496765841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 230247464041781264337941 10792849876958496765841)
                      ·
                        rfl

theorem cell23_21019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_21019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21019 prefixEnd_21019 := by exact prefixLift 21019
  have htrace : WordTrace (prefixWord ++ tailWord_21019) baseStart_21019 baseEnd_21019 := by
    simpa [prefixWord, tailWord_21019, baseEnd_21019] using wordTrace_append hprefix tailTrace_21019
  have hstable : (prefixWord ++ tailWord_21019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21019).length < 2 ^ (prefixWord ++ tailWord_21019).sum := by decide
  have hdescent : baseEnd_21019 < baseStart_21019 := by decide
  rcases family_descends (prefixWord ++ tailWord_21019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21039 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_21039 : Nat := 118140960795 + 21039 * 2 ^ 59
def prefixEnd_21039 : Nat := 4983230072969 + 3 ^ 40 * 21039 * 2
def baseEnd_21039 : Nat := 10803119490048418515749

theorem tailTrace_21039 : CollatzResearch.WordTrace tailWord_21039 prefixEnd_21039 10803119490048418515749 := by
  unfold tailWord_21039
  simp only [CollatzResearch.WordTrace]
  refine ⟨767355370786771020242171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 511570247191180680161447 767355370786771020242171)
  ·
    refine ⟨1151033056180156530363257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767355370786771020242171 1151033056180156530363257)
    ·
      refine ⟨863274792135117397772443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1151033056180156530363257 863274792135117397772443)
      ·
        refine ⟨1294912188202676096658665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863274792135117397772443 1294912188202676096658665)
        ·
          refine ⟨971184141152007072493999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1294912188202676096658665 971184141152007072493999)
          ·
            refine ⟨1456776211728010608740999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971184141152007072493999 1456776211728010608740999)
            ·
              refine ⟨2185164317592015913111499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456776211728010608740999 2185164317592015913111499)
              ·
                refine ⟨3277746476388023869667249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185164317592015913111499 3277746476388023869667249)
                ·
                  refine ⟨2458309857291017902250437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3277746476388023869667249 2458309857291017902250437)
                  ·
                    refine ⟨460933098242065856671957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2458309857291017902250437 460933098242065856671957)
                    ·
                      refine ⟨10803119490048418515749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 460933098242065856671957 10803119490048418515749)
                      ·
                        rfl

theorem cell23_21039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_21039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21039 prefixEnd_21039 := by exact prefixLift 21039
  have htrace : WordTrace (prefixWord ++ tailWord_21039) baseStart_21039 baseEnd_21039 := by
    simpa [prefixWord, tailWord_21039, baseEnd_21039] using wordTrace_append hprefix tailTrace_21039
  have hstable : (prefixWord ++ tailWord_21039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21039).length < 2 ^ (prefixWord ++ tailWord_21039).sum := by decide
  have hdescent : baseEnd_21039 < baseStart_21039 := by decide
  rcases family_descends (prefixWord ++ tailWord_21039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21050 : List Nat := [3, 1, 1, 1, 3, 3, 2, 4, 1, 4]
def baseStart_21050 : Nat := 118140960795 + 21050 * 2 ^ 59
def prefixEnd_21050 : Nat := 4983230072969 + 3 ^ 40 * 21050 * 2
def baseEnd_21050 : Nat := 3602922592415958492733

theorem tailTrace_21050 : CollatzResearch.WordTrace tailWord_21050 prefixEnd_21050 3602922592415958492733 := by
  unfold tailWord_21050
  simp only [CollatzResearch.WordTrace]
  refine ⟨191939143436729974723151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 511837715831279932595069 191939143436729974723151)
  ·
    refine ⟨287908715155094962084727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191939143436729974723151 287908715155094962084727)
    ·
      refine ⟨431863072732642443127091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287908715155094962084727 431863072732642443127091)
      ·
        refine ⟨647794609098963664690637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431863072732642443127091 647794609098963664690637)
        ·
          refine ⟨242922978412111374258989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 647794609098963664690637 242922978412111374258989)
          ·
            refine ⟨91096116904541765347121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242922978412111374258989 91096116904541765347121)
            ·
              refine ⟨68322087678406324010341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91096116904541765347121 68322087678406324010341)
              ·
                refine ⟨12810391439701185751939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68322087678406324010341 12810391439701185751939)
                ·
                  refine ⟨19215587159551778627909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12810391439701185751939 19215587159551778627909)
                  ·
                    refine ⟨3602922592415958492733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19215587159551778627909 3602922592415958492733)
                    ·
                      rfl

theorem cell23_21050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_21050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21050 prefixEnd_21050 := by exact prefixLift 21050
  have htrace : WordTrace (prefixWord ++ tailWord_21050) baseStart_21050 baseEnd_21050 := by
    simpa [prefixWord, tailWord_21050, baseEnd_21050] using wordTrace_append hprefix tailTrace_21050
  have hstable : (prefixWord ++ tailWord_21050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21050).length < 2 ^ (prefixWord ++ tailWord_21050).sum := by decide
  have hdescent : baseEnd_21050 < baseStart_21050 := by decide
  rcases family_descends (prefixWord ++ tailWord_21050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21084 : List Nat := [2, 2, 4, 1, 3, 2, 1, 3, 1, 4]
def baseStart_21084 : Nat := 118140960795 + 21084 * 2 ^ 59
def prefixEnd_21084 : Nat := 4983230072969 + 3 ^ 40 * 21084 * 2
def baseEnd_21084 : Nat := 3608742039833580817681

theorem tailTrace_21084 : CollatzResearch.WordTrace tailWord_21084 prefixEnd_21084 3608742039833580817681 := by
  unfold tailWord_21084
  simp only [CollatzResearch.WordTrace]
  refine ⟨384498327811871852815153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 512664437082495803753537 384498327811871852815153)
  ·
    refine ⟨288373745858903889611365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 384498327811871852815153 288373745858903889611365)
    ·
      refine ⟨54070077348544479302131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288373745858903889611365 54070077348544479302131)
      ·
        refine ⟨81105116022816718953197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54070077348544479302131 81105116022816718953197)
        ·
          refine ⟨30414418508556269607449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81105116022816718953197 30414418508556269607449)
          ·
            refine ⟨22810813881417202205587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30414418508556269607449 22810813881417202205587)
            ·
              refine ⟨34216220822125803308381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22810813881417202205587 34216220822125803308381)
              ·
                refine ⟨12831082808297176240643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34216220822125803308381 12831082808297176240643)
                ·
                  refine ⟨19246624212445764360965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12831082808297176240643 19246624212445764360965)
                  ·
                    refine ⟨3608742039833580817681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19246624212445764360965 3608742039833580817681)
                    ·
                      rfl

theorem cell23_21084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_21084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21084 prefixEnd_21084 := by exact prefixLift 21084
  have htrace : WordTrace (prefixWord ++ tailWord_21084) baseStart_21084 baseEnd_21084 := by
    simpa [prefixWord, tailWord_21084, baseEnd_21084] using wordTrace_append hprefix tailTrace_21084
  have hstable : (prefixWord ++ tailWord_21084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21084).length < 2 ^ (prefixWord ++ tailWord_21084).sum := by decide
  have hdescent : baseEnd_21084 < baseStart_21084 := by decide
  rcases family_descends (prefixWord ++ tailWord_21084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21130 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_21130 : Nat := 118140960795 + 21130 * 2 ^ 59
def prefixEnd_21130 : Nat := 4983230072969 + 3 ^ 40 * 21130 * 2
def baseEnd_21130 : Nat := 10849846229607562477831

theorem tailTrace_21130 : CollatzResearch.WordTrace tailWord_21130 prefixEnd_21130 10849846229607562477831 := by
  unfold tailWord_21130
  simp only [CollatzResearch.WordTrace]
  refine ⟨192668603364273390451211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 513782942304729041203229 192668603364273390451211)
  ·
    refine ⟨289002905046410085676817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192668603364273390451211 289002905046410085676817)
    ·
      refine ⟨216752178784807564257613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289002905046410085676817 216752178784807564257613)
      ·
        refine ⟨81282067044302836596605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216752178784807564257613 81282067044302836596605)
        ·
          refine ⟨30480775141613563723727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81282067044302836596605 30480775141613563723727)
          ·
            refine ⟨45721162712420345585591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30480775141613563723727 45721162712420345585591)
            ·
              refine ⟨68581744068630518378387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45721162712420345585591 68581744068630518378387)
              ·
                refine ⟨102872616102945777567581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68581744068630518378387 102872616102945777567581)
                ·
                  refine ⟨38577231038604666587843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102872616102945777567581 38577231038604666587843)
                  ·
                    refine ⟨57865846557906999881765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38577231038604666587843 57865846557906999881765)
                    ·
                      refine ⟨10849846229607562477831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 57865846557906999881765 10849846229607562477831)
                      ·
                        rfl

theorem cell23_21130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_21130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21130 prefixEnd_21130 := by exact prefixLift 21130
  have htrace : WordTrace (prefixWord ++ tailWord_21130) baseStart_21130 baseEnd_21130 := by
    simpa [prefixWord, tailWord_21130, baseEnd_21130] using wordTrace_append hprefix tailTrace_21130
  have hstable : (prefixWord ++ tailWord_21130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21130).length < 2 ^ (prefixWord ++ tailWord_21130).sum := by decide
  have hdescent : baseEnd_21130 < baseStart_21130 := by decide
  rcases family_descends (prefixWord ++ tailWord_21130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21140 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_21140 : Nat := 118140960795 + 21140 * 2 ^ 59
def prefixEnd_21140 : Nat := 4983230072969 + 3 ^ 40 * 21140 * 2
def baseEnd_21140 : Nat := 3618327012050841117595

theorem tailTrace_21140 : CollatzResearch.WordTrace tailWord_21140 prefixEnd_21140 3618327012050841117595 := by
  unfold tailWord_21140
  simp only [CollatzResearch.WordTrace]
  refine ⟨385519571710432634834437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 514026095613910179779249 385519571710432634834437)
  ·
    refine ⟨72284919695706119031457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 385519571710432634834437 72284919695706119031457)
    ·
      refine ⟨54213689771779589273593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72284919695706119031457 54213689771779589273593)
      ·
        refine ⟨40660267328834691955195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54213689771779589273593 40660267328834691955195)
        ·
          refine ⟨60990400993252037932793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40660267328834691955195 60990400993252037932793)
          ·
            refine ⟨45742800744939028449595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60990400993252037932793 45742800744939028449595)
            ·
              refine ⟨68614201117408542674393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45742800744939028449595 68614201117408542674393)
              ·
                refine ⟨51460650838056407005795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68614201117408542674393 51460650838056407005795)
                ·
                  refine ⟨77190976257084610508693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51460650838056407005795 77190976257084610508693)
                  ·
                    refine ⟨3618327012050841117595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77190976257084610508693 3618327012050841117595)
                    ·
                      rfl

theorem cell23_21140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_21140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21140 prefixEnd_21140 := by exact prefixLift 21140
  have htrace : WordTrace (prefixWord ++ tailWord_21140) baseStart_21140 baseEnd_21140 := by
    simpa [prefixWord, tailWord_21140, baseEnd_21140] using wordTrace_append hprefix tailTrace_21140
  have hstable : (prefixWord ++ tailWord_21140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21140).length < 2 ^ (prefixWord ++ tailWord_21140).sum := by decide
  have hdescent : baseEnd_21140 < baseStart_21140 := by decide
  rcases family_descends (prefixWord ++ tailWord_21140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21143 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_21143 : Nat := 118140960795 + 21143 * 2 ^ 59
def prefixEnd_21143 : Nat := 4983230072969 + 3 ^ 40 * 21143 * 2
def baseEnd_21143 : Nat := 10856521478116011615271

theorem tailTrace_21143 : CollatzResearch.WordTrace tailWord_21143 prefixEnd_21143 10856521478116011615271 := by
  unfold tailWord_21143
  simp only [CollatzResearch.WordTrace]
  refine ⟨771148562409996782028083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 514099041606664521352055 771148562409996782028083)
  ·
    refine ⟨1156722843614995173042125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 771148562409996782028083 1156722843614995173042125)
    ·
      refine ⟨433771066355623189890797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1156722843614995173042125 433771066355623189890797)
      ·
        refine ⟨162664149883358696209049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 433771066355623189890797 162664149883358696209049)
        ·
          refine ⟨121998112412519022156787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162664149883358696209049 121998112412519022156787)
          ·
            refine ⟨182997168618778533235181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121998112412519022156787 182997168618778533235181)
            ·
              refine ⟨68623938232041949963193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182997168618778533235181 68623938232041949963193)
              ·
                refine ⟨51467953674031462472395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68623938232041949963193 51467953674031462472395)
                ·
                  refine ⟨77201930511047193708593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51467953674031462472395 77201930511047193708593)
                  ·
                    refine ⟨57901447883285395281445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77201930511047193708593 57901447883285395281445)
                    ·
                      refine ⟨10856521478116011615271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 57901447883285395281445 10856521478116011615271)
                      ·
                        rfl

theorem cell23_21143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_21143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21143 prefixEnd_21143 := by exact prefixLift 21143
  have htrace : WordTrace (prefixWord ++ tailWord_21143) baseStart_21143 baseEnd_21143 := by
    simpa [prefixWord, tailWord_21143, baseEnd_21143] using wordTrace_append hprefix tailTrace_21143
  have hstable : (prefixWord ++ tailWord_21143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21143).length < 2 ^ (prefixWord ++ tailWord_21143).sum := by decide
  have hdescent : baseEnd_21143 < baseStart_21143 := by decide
  rcases family_descends (prefixWord ++ tailWord_21143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21153 : List Nat := [1, 2, 3, 3, 4, 10]
def baseStart_21153 : Nat := 118140960795 + 21153 * 2 ^ 59
def prefixEnd_21153 : Nat := 4983230072969 + 3 ^ 40 * 21153 * 2
def baseEnd_21153 : Nat := 44698174010950504075

theorem tailTrace_21153 : CollatzResearch.WordTrace tailWord_21153 prefixEnd_21153 44698174010950504075 := by
  unfold tailWord_21153
  simp only [CollatzResearch.WordTrace]
  refine ⟨771513292373768489892113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 514342194915845659928075 771513292373768489892113)
  ·
    refine ⟨578634969280326367419085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 771513292373768489892113 578634969280326367419085)
    ·
      refine ⟨216988113480122387782157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 578634969280326367419085 216988113480122387782157)
      ·
        refine ⟨81370542555045895418309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216988113480122387782157 81370542555045895418309)
        ·
          refine ⟨15256976729071105390933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81370542555045895418309 15256976729071105390933)
          ·
            refine ⟨44698174010950504075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 15256976729071105390933 44698174010950504075)
            ·
              rfl

theorem cell23_21153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 10].length) (baseStart_21153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21153 prefixEnd_21153 := by exact prefixLift 21153
  have htrace : WordTrace (prefixWord ++ tailWord_21153) baseStart_21153 baseEnd_21153 := by
    simpa [prefixWord, tailWord_21153, baseEnd_21153] using wordTrace_append hprefix tailTrace_21153
  have hstable : (prefixWord ++ tailWord_21153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21153).length < 2 ^ (prefixWord ++ tailWord_21153).sum := by decide
  have hdescent : baseEnd_21153 < baseStart_21153 := by decide
  rcases family_descends (prefixWord ++ tailWord_21153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21176 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_21176 : Nat := 118140960795 + 21176 * 2 ^ 59
def prefixEnd_21176 : Nat := 4983230072969 + 3 ^ 40 * 21176 * 2
def baseEnd_21176 : Nat := 10873466339714382502619

theorem tailTrace_21176 : CollatzResearch.WordTrace tailWord_21176 prefixEnd_21176 10873466339714382502619 := by
  unfold tailWord_21176
  simp only [CollatzResearch.WordTrace]
  refine ⟨386176085645221708989691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 514901447526962278652921 386176085645221708989691)
  ·
    refine ⟨579264128467832563484537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 386176085645221708989691 579264128467832563484537)
    ·
      refine ⟨434448096350874422613403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 579264128467832563484537 434448096350874422613403)
      ·
        refine ⟨651672144526311633920105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434448096350874422613403 651672144526311633920105)
        ·
          refine ⟨488754108394733725440079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 651672144526311633920105 488754108394733725440079)
          ·
            refine ⟨733131162592100588160119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488754108394733725440079 733131162592100588160119)
            ·
              refine ⟨1099696743888150882240179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733131162592100588160119 1099696743888150882240179)
              ·
                refine ⟨1649545115832226323360269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099696743888150882240179 1649545115832226323360269)
                ·
                  refine ⟨618579418437084871260101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1649545115832226323360269 618579418437084871260101)
                  ·
                    refine ⟨115983640956953413361269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 618579418437084871260101 115983640956953413361269)
                    ·
                      refine ⟨10873466339714382502619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 115983640956953413361269 10873466339714382502619)
                      ·
                        rfl

theorem cell23_21176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_21176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21176 prefixEnd_21176 := by exact prefixLift 21176
  have htrace : WordTrace (prefixWord ++ tailWord_21176) baseStart_21176 baseEnd_21176 := by
    simpa [prefixWord, tailWord_21176, baseEnd_21176] using wordTrace_append hprefix tailTrace_21176
  have hstable : (prefixWord ++ tailWord_21176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21176).length < 2 ^ (prefixWord ++ tailWord_21176).sum := by decide
  have hdescent : baseEnd_21176 < baseStart_21176 := by decide
  rcases family_descends (prefixWord ++ tailWord_21176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21180 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_21180 : Nat := 118140960795 + 21180 * 2 ^ 59
def prefixEnd_21180 : Nat := 4983230072969 + 3 ^ 40 * 21180 * 2
def baseEnd_21180 : Nat := 10875520262332366852601

theorem tailTrace_21180 : CollatzResearch.WordTrace tailWord_21180 prefixEnd_21180 10875520262332366852601 := by
  unfold tailWord_21180
  simp only [CollatzResearch.WordTrace]
  refine ⟨386249031637976050562497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 514998708850634734083329 386249031637976050562497)
  ·
    refine ⟨289686773728482037921873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 386249031637976050562497 289686773728482037921873)
    ·
      refine ⟨217265080296361528441405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289686773728482037921873 217265080296361528441405)
      ·
        refine ⟨81474405111135573165527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217265080296361528441405 81474405111135573165527)
        ·
          refine ⟨122211607666703359748291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81474405111135573165527 122211607666703359748291)
          ·
            refine ⟨183317411500055039622437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122211607666703359748291 183317411500055039622437)
            ·
              refine ⟨34372014656260319929207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183317411500055039622437 34372014656260319929207)
              ·
                refine ⟨51558021984390479893811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34372014656260319929207 51558021984390479893811)
                ·
                  refine ⟨77337032976585719840717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51558021984390479893811 77337032976585719840717)
                  ·
                    refine ⟨29001387366219644940269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77337032976585719840717 29001387366219644940269)
                    ·
                      refine ⟨10875520262332366852601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 29001387366219644940269 10875520262332366852601)
                      ·
                        rfl

theorem cell23_21180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_21180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21180 prefixEnd_21180 := by exact prefixLift 21180
  have htrace : WordTrace (prefixWord ++ tailWord_21180) baseStart_21180 baseEnd_21180 := by
    simpa [prefixWord, tailWord_21180, baseEnd_21180] using wordTrace_append hprefix tailTrace_21180
  have hstable : (prefixWord ++ tailWord_21180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21180).length < 2 ^ (prefixWord ++ tailWord_21180).sum := by decide
  have hdescent : baseEnd_21180 < baseStart_21180 := by decide
  rcases family_descends (prefixWord ++ tailWord_21180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21207 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 1, 3, 2]
def baseStart_21207 : Nat := 118140960795 + 21207 * 2 ^ 59
def prefixEnd_21207 : Nat := 4983230072969 + 3 ^ 40 * 21207 * 2
def baseEnd_21207 : Nat := 10889384240003761214977

theorem tailTrace_21207 : CollatzResearch.WordTrace tailWord_21207 prefixEnd_21207 10889384240003761214977 := by
  unfold tailWord_21207
  simp only [CollatzResearch.WordTrace]
  refine ⟨773482834178135712357875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 515655222785423808238583 773482834178135712357875)
  ·
    refine ⟨1160224251267203568536813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 773482834178135712357875 1160224251267203568536813)
    ·
      refine ⟨435084094225201338201305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1160224251267203568536813 435084094225201338201305)
      ·
        refine ⟨326313070668901003650979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435084094225201338201305 326313070668901003650979)
        ·
          refine ⟨489469606003351505476469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326313070668901003650979 489469606003351505476469)
          ·
            refine ⟨45887775562814203638419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 489469606003351505476469 45887775562814203638419)
            ·
              refine ⟨68831663344221305457629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45887775562814203638419 68831663344221305457629)
              ·
                refine ⟨25811873754082989546611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68831663344221305457629 25811873754082989546611)
                ·
                  refine ⟨38717810631124484319917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25811873754082989546611 38717810631124484319917)
                  ·
                    refine ⟨14519178986671681619969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38717810631124484319917 14519178986671681619969)
                    ·
                      refine ⟨10889384240003761214977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14519178986671681619969 10889384240003761214977)
                      ·
                        rfl

theorem cell23_21207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_21207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21207 prefixEnd_21207 := by exact prefixLift 21207
  have htrace : WordTrace (prefixWord ++ tailWord_21207) baseStart_21207 baseEnd_21207 := by
    simpa [prefixWord, tailWord_21207, baseEnd_21207] using wordTrace_append hprefix tailTrace_21207
  have hstable : (prefixWord ++ tailWord_21207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21207).length < 2 ^ (prefixWord ++ tailWord_21207).sum := by decide
  have hdescent : baseEnd_21207 < baseStart_21207 := by decide
  rcases family_descends (prefixWord ++ tailWord_21207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21233 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_21233 : Nat := 118140960795 + 21233 * 2 ^ 59
def prefixEnd_21233 : Nat := 4983230072969 + 3 ^ 40 * 21233 * 2
def baseEnd_21233 : Nat := 10902734737020659489857

theorem tailTrace_21233 : CollatzResearch.WordTrace tailWord_21233 prefixEnd_21233 10902734737020659489857 := by
  unfold tailWord_21233
  simp only [CollatzResearch.WordTrace]
  refine ⟨774431132083942152804353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 516287421389294768536235 774431132083942152804353)
  ·
    refine ⟨580823349062956614603265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 774431132083942152804353 580823349062956614603265)
    ·
      refine ⟨435617511797217460952449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 580823349062956614603265 435617511797217460952449)
      ·
        refine ⟨326713133847913095714337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435617511797217460952449 326713133847913095714337)
        ·
          refine ⟨245034850385934821785753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326713133847913095714337 245034850385934821785753)
          ·
            refine ⟨183776137789451116339315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245034850385934821785753 183776137789451116339315)
            ·
              refine ⟨275664206684176674508973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183776137789451116339315 275664206684176674508973)
              ·
                refine ⟨103374077506566252940865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275664206684176674508973 103374077506566252940865)
                ·
                  refine ⟨77530558129924689705649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103374077506566252940865 77530558129924689705649)
                  ·
                    refine ⟨58147918597443517279237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77530558129924689705649 58147918597443517279237)
                    ·
                      refine ⟨10902734737020659489857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 58147918597443517279237 10902734737020659489857)
                      ·
                        rfl

theorem cell23_21233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_21233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21233 prefixEnd_21233 := by exact prefixLift 21233
  have htrace : WordTrace (prefixWord ++ tailWord_21233) baseStart_21233 baseEnd_21233 := by
    simpa [prefixWord, tailWord_21233, baseEnd_21233] using wordTrace_append hprefix tailTrace_21233
  have hstable : (prefixWord ++ tailWord_21233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21233).length < 2 ^ (prefixWord ++ tailWord_21233).sum := by decide
  have hdescent : baseEnd_21233 < baseStart_21233 := by decide
  rcases family_descends (prefixWord ++ tailWord_21233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21253 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 1, 5, 3]
def baseStart_21253 : Nat := 118140960795 + 21253 * 2 ^ 59
def prefixEnd_21253 : Nat := 4983230072969 + 3 ^ 40 * 21253 * 2
def baseEnd_21253 : Nat := 10913004350110581239765

theorem tailTrace_21253 : CollatzResearch.WordTrace tailWord_21253 prefixEnd_21253 10913004350110581239765 := by
  unfold tailWord_21253
  simp only [CollatzResearch.WordTrace]
  refine ⟨775160592011485568532413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 516773728007657045688275 775160592011485568532413)
  ·
    refine ⟨290685222004307088199655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 775160592011485568532413 290685222004307088199655)
    ·
      refine ⟨436027833006460632299483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290685222004307088199655 436027833006460632299483)
      ·
        refine ⟨654041749509690948449225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436027833006460632299483 654041749509690948449225)
        ·
          refine ⟨490531312132268211336919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654041749509690948449225 490531312132268211336919)
          ·
            refine ⟨735796968198402317005379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490531312132268211336919 735796968198402317005379)
            ·
              refine ⟨1103695452297603475508069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735796968198402317005379 1103695452297603475508069)
              ·
                refine ⟨206942897305800651657763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1103695452297603475508069 206942897305800651657763)
                ·
                  refine ⟨310414345958700977486645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206942897305800651657763 310414345958700977486645)
                  ·
                    refine ⟨29101344933628216639373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 310414345958700977486645 29101344933628216639373)
                    ·
                      refine ⟨10913004350110581239765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 29101344933628216639373 10913004350110581239765)
                      ·
                        rfl

theorem cell23_21253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_21253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21253 prefixEnd_21253 := by exact prefixLift 21253
  have htrace : WordTrace (prefixWord ++ tailWord_21253) baseStart_21253 baseEnd_21253 := by
    simpa [prefixWord, tailWord_21253, baseEnd_21253] using wordTrace_append hprefix tailTrace_21253
  have hstable : (prefixWord ++ tailWord_21253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21253).length < 2 ^ (prefixWord ++ tailWord_21253).sum := by decide
  have hdescent : baseEnd_21253 < baseStart_21253 := by decide
  rcases family_descends (prefixWord ++ tailWord_21253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21387 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 2, 3, 2]
def baseStart_21387 : Nat := 118140960795 + 21387 * 2 ^ 59
def prefixEnd_21387 : Nat := 4983230072969 + 3 ^ 40 * 21387 * 2
def baseEnd_21387 : Nat := 10981810757813056964149

theorem tailTrace_21387 : CollatzResearch.WordTrace tailWord_21387 prefixEnd_21387 10981810757813056964149 := by
  unfold tailWord_21387
  simp only [CollatzResearch.WordTrace]
  refine ⟨780047973526026453910415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 520031982350684302606943 780047973526026453910415)
  ·
    refine ⟨1170071960289039680865623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 780047973526026453910415 1170071960289039680865623)
    ·
      refine ⟨1755107940433559521298435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1170071960289039680865623 1755107940433559521298435)
      ·
        refine ⟨2632661910650339281947653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1755107940433559521298435 2632661910650339281947653)
        ·
          refine ⟨493624108246938615365185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2632661910650339281947653 493624108246938615365185)
          ·
            refine ⟨370218081185203961523889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493624108246938615365185 370218081185203961523889)
            ·
              refine ⟨277663560888902971142917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370218081185203961523889 277663560888902971142917)
              ·
                refine ⟨52061917666669307089297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277663560888902971142917 52061917666669307089297)
                ·
                  refine ⟨39046438250001980316973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52061917666669307089297 39046438250001980316973)
                  ·
                    refine ⟨14642414343750742618865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39046438250001980316973 14642414343750742618865)
                    ·
                      refine ⟨10981810757813056964149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14642414343750742618865 10981810757813056964149)
                      ·
                        rfl

theorem cell23_21387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 3, 2].length) (baseStart_21387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21387 prefixEnd_21387 := by exact prefixLift 21387
  have htrace : WordTrace (prefixWord ++ tailWord_21387) baseStart_21387 baseEnd_21387 := by
    simpa [prefixWord, tailWord_21387, baseEnd_21387] using wordTrace_append hprefix tailTrace_21387
  have hstable : (prefixWord ++ tailWord_21387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21387).length < 2 ^ (prefixWord ++ tailWord_21387).sum := by decide
  have hdescent : baseEnd_21387 < baseStart_21387 := by decide
  rcases family_descends (prefixWord ++ tailWord_21387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21417 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 4]
def baseStart_21417 : Nat := 118140960795 + 21417 * 2 ^ 59
def prefixEnd_21417 : Nat := 4983230072969 + 3 ^ 40 * 21417 * 2
def baseEnd_21417 : Nat := 10997215177447939589011

theorem tailTrace_21417 : CollatzResearch.WordTrace tailWord_21417 prefixEnd_21417 10997215177447939589011 := by
  unfold tailWord_21417
  simp only [CollatzResearch.WordTrace]
  refine ⟨781142163417341577502505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 520761442278227718335003 781142163417341577502505)
  ·
    refine ⟨585856622563006183126879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 781142163417341577502505 585856622563006183126879)
    ·
      refine ⟨878784933844509274690319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 585856622563006183126879 878784933844509274690319)
      ·
        refine ⟨1318177400766763912035479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878784933844509274690319 1318177400766763912035479)
        ·
          refine ⟨1977266101150145868053219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318177400766763912035479 1977266101150145868053219)
          ·
            refine ⟨2965899151725218802079829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977266101150145868053219 2965899151725218802079829)
            ·
              refine ⟨34756630684279907836873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2965899151725218802079829 34756630684279907836873)
              ·
                refine ⟨26067473013209930877655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34756630684279907836873 26067473013209930877655)
                ·
                  refine ⟨39101209519814896316483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26067473013209930877655 39101209519814896316483)
                  ·
                    refine ⟨58651814279722344474725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39101209519814896316483 58651814279722344474725)
                    ·
                      refine ⟨10997215177447939589011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 58651814279722344474725 10997215177447939589011)
                      ·
                        rfl

theorem cell23_21417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 4].length) (baseStart_21417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21417 prefixEnd_21417 := by exact prefixLift 21417
  have htrace : WordTrace (prefixWord ++ tailWord_21417) baseStart_21417 baseEnd_21417 := by
    simpa [prefixWord, tailWord_21417, baseEnd_21417] using wordTrace_append hprefix tailTrace_21417
  have hstable : (prefixWord ++ tailWord_21417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21417).length < 2 ^ (prefixWord ++ tailWord_21417).sum := by decide
  have hdescent : baseEnd_21417 < baseStart_21417 := by decide
  rcases family_descends (prefixWord ++ tailWord_21417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21440 : List Nat := [2, 1, 1, 2, 3, 5, 9]
def baseStart_21440 : Nat := 118140960795 + 21440 * 2 ^ 59
def prefixEnd_21440 : Nat := 4983230072969 + 3 ^ 40 * 21440 * 2
def baseEnd_21440 : Nat := 135913891759275921005

theorem tailTrace_21440 : CollatzResearch.WordTrace tailWord_21440 prefixEnd_21440 135913891759275921005 := by
  unfold tailWord_21440
  simp only [CollatzResearch.WordTrace]
  refine ⟨390990521167008252794887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 521320694889344337059849 390990521167008252794887)
  ·
    refine ⟨586485781750512379192331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 390990521167008252794887 586485781750512379192331)
    ·
      refine ⟨879728672625768568788497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586485781750512379192331 879728672625768568788497)
      ·
        refine ⟨659796504469326426591373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 879728672625768568788497 659796504469326426591373)
        ·
          refine ⟨247423689175997409971765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 659796504469326426591373 247423689175997409971765)
          ·
            refine ⟨23195970860249757184853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 247423689175997409971765 23195970860249757184853)
            ·
              refine ⟨135913891759275921005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 23195970860249757184853 135913891759275921005)
              ·
                rfl

theorem cell23_21440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 9].length) (baseStart_21440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21440 prefixEnd_21440 := by exact prefixLift 21440
  have htrace : WordTrace (prefixWord ++ tailWord_21440) baseStart_21440 baseEnd_21440 := by
    simpa [prefixWord, tailWord_21440, baseEnd_21440] using wordTrace_append hprefix tailTrace_21440
  have hstable : (prefixWord ++ tailWord_21440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21440).length < 2 ^ (prefixWord ++ tailWord_21440).sum := by decide
  have hdescent : baseEnd_21440 < baseStart_21440 := by decide
  rcases family_descends (prefixWord ++ tailWord_21440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21451 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 3, 2, 2]
def baseStart_21451 : Nat := 118140960795 + 21451 * 2 ^ 59
def prefixEnd_21451 : Nat := 4983230072969 + 3 ^ 40 * 21451 * 2
def baseEnd_21451 : Nat := 11014673519700806563855

theorem tailTrace_21451 : CollatzResearch.WordTrace tailWord_21451 prefixEnd_21451 11014673519700806563855 := by
  unfold tailWord_21451
  simp only [CollatzResearch.WordTrace]
  refine ⟨782382245294165384240207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 521588163529443589493471 782382245294165384240207)
  ·
    refine ⟨1173573367941248076360311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 782382245294165384240207 1173573367941248076360311)
    ·
      refine ⟨1760360051911872114540467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1173573367941248076360311 1760360051911872114540467)
      ·
        refine ⟨2640540077867808171810701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1760360051911872114540467 2640540077867808171810701)
        ·
          refine ⟨990202529200428064429013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2640540077867808171810701 990202529200428064429013)
          ·
            refine ⟨23207871778135032760055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 990202529200428064429013 23207871778135032760055)
            ·
              refine ⟨34811807667202549140083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23207871778135032760055 34811807667202549140083)
              ·
                refine ⟨52217711500803823710125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34811807667202549140083 52217711500803823710125)
                ·
                  refine ⟨19581641812801433891297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52217711500803823710125 19581641812801433891297)
                  ·
                    refine ⟨14686231359601075418473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19581641812801433891297 14686231359601075418473)
                    ·
                      refine ⟨11014673519700806563855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14686231359601075418473 11014673519700806563855)
                      ·
                        rfl

theorem cell23_21451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 2, 2].length) (baseStart_21451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21451 prefixEnd_21451 := by exact prefixLift 21451
  have htrace : WordTrace (prefixWord ++ tailWord_21451) baseStart_21451 baseEnd_21451 := by
    simpa [prefixWord, tailWord_21451, baseEnd_21451] using wordTrace_append hprefix tailTrace_21451
  have hstable : (prefixWord ++ tailWord_21451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21451).length < 2 ^ (prefixWord ++ tailWord_21451).sum := by decide
  have hdescent : baseEnd_21451 < baseStart_21451 := by decide
  rcases family_descends (prefixWord ++ tailWord_21451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21471 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 1, 2, 3]
def baseStart_21471 : Nat := 118140960795 + 21471 * 2 ^ 59
def prefixEnd_21471 : Nat := 4983230072969 + 3 ^ 40 * 21471 * 2
def baseEnd_21471 : Nat := 11024943132790728313763

theorem tailTrace_21471 : CollatzResearch.WordTrace tailWord_21471 prefixEnd_21471 11024943132790728313763 := by
  unfold tailWord_21471
  simp only [CollatzResearch.WordTrace]
  refine ⟨783111705221708799968267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 522074470147805866645511 783111705221708799968267)
  ·
    refine ⟨1174667557832563199952401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 783111705221708799968267 1174667557832563199952401)
    ·
      refine ⟨881000668374422399964301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1174667557832563199952401 881000668374422399964301)
      ·
        refine ⟨330375250640408399986613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 881000668374422399964301 330375250640408399986613)
        ·
          refine ⟨30972679747538287498745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 330375250640408399986613 30972679747538287498745)
          ·
            refine ⟨23229509810653715624059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30972679747538287498745 23229509810653715624059)
            ·
              refine ⟨34844264715980573436089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23229509810653715624059 34844264715980573436089)
              ·
                refine ⟨26133198536985430077067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34844264715980573436089 26133198536985430077067)
                ·
                  refine ⟨39199797805478145115601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26133198536985430077067 39199797805478145115601)
                  ·
                    refine ⟨29399848354108608836701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39199797805478145115601 29399848354108608836701)
                    ·
                      refine ⟨11024943132790728313763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 29399848354108608836701 11024943132790728313763)
                      ·
                        rfl

theorem cell23_21471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_21471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21471 prefixEnd_21471 := by exact prefixLift 21471
  have htrace : WordTrace (prefixWord ++ tailWord_21471) baseStart_21471 baseEnd_21471 := by
    simpa [prefixWord, tailWord_21471, baseEnd_21471] using wordTrace_append hprefix tailTrace_21471
  have hstable : (prefixWord ++ tailWord_21471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21471).length < 2 ^ (prefixWord ++ tailWord_21471).sum := by decide
  have hdescent : baseEnd_21471 < baseStart_21471 := by decide
  rcases family_descends (prefixWord ++ tailWord_21471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21480 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_21480 : Nat := 118140960795 + 21480 * 2 ^ 59
def prefixEnd_21480 : Nat := 4983230072969 + 3 ^ 40 * 21480 * 2
def baseEnd_21480 : Nat := 11029564458681193101221

theorem tailTrace_21480 : CollatzResearch.WordTrace tailWord_21480 prefixEnd_21480 11029564458681193101221 := by
  unfold tailWord_21480
  simp only [CollatzResearch.WordTrace]
  refine ⟨391719981094551668522947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 522293308126068891363929 391719981094551668522947)
  ·
    refine ⟨587579971641827502784421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 391719981094551668522947 587579971641827502784421)
    ·
      refine ⟨110171244682842656772079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 587579971641827502784421 110171244682842656772079)
      ·
        refine ⟨165256867024263985158119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110171244682842656772079 165256867024263985158119)
        ·
          refine ⟨247885300536395977737179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165256867024263985158119 247885300536395977737179)
          ·
            refine ⟨371827950804593966605769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247885300536395977737179 371827950804593966605769)
            ·
              refine ⟨278870963103445474954327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371827950804593966605769 278870963103445474954327)
              ·
                refine ⟨418306444655168212431491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278870963103445474954327 418306444655168212431491)
                ·
                  refine ⟨627459666982752318647237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418306444655168212431491 627459666982752318647237)
                  ·
                    refine ⟨117648687559266059746357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 627459666982752318647237 117648687559266059746357)
                    ·
                      refine ⟨11029564458681193101221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 117648687559266059746357 11029564458681193101221)
                      ·
                        rfl

theorem cell23_21480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_21480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21480 prefixEnd_21480 := by exact prefixLift 21480
  have htrace : WordTrace (prefixWord ++ tailWord_21480) baseStart_21480 baseEnd_21480 := by
    simpa [prefixWord, tailWord_21480, baseEnd_21480] using wordTrace_append hprefix tailTrace_21480
  have hstable : (prefixWord ++ tailWord_21480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21480).length < 2 ^ (prefixWord ++ tailWord_21480).sum := by decide
  have hdescent : baseEnd_21480 < baseStart_21480 := by decide
  rcases family_descends (prefixWord ++ tailWord_21480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21558 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_21558 : Nat := 118140960795 + 21558 * 2 ^ 59
def prefixEnd_21558 : Nat := 4983230072969 + 3 ^ 40 * 21558 * 2
def baseEnd_21558 : Nat := 11069615949731887925863

theorem tailTrace_21558 : CollatzResearch.WordTrace tailWord_21558 prefixEnd_21558 11069615949731887925863 := by
  unfold tailWord_21558
  simp only [CollatzResearch.WordTrace]
  refine ⟨49142803494157666149083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 524189903937681772256885 49142803494157666149083)
  ·
    refine ⟨73714205241236499223625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49142803494157666149083 73714205241236499223625)
    ·
      refine ⟨55285653930927374417719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73714205241236499223625 55285653930927374417719)
      ·
        refine ⟨82928480896391061626579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55285653930927374417719 82928480896391061626579)
        ·
          refine ⟨124392721344586592439869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82928480896391061626579 124392721344586592439869)
          ·
            refine ⟨46647270504219972164951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124392721344586592439869 46647270504219972164951)
            ·
              refine ⟨69970905756329958247427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46647270504219972164951 69970905756329958247427)
              ·
                refine ⟨104956358634494937371141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69970905756329958247427 104956358634494937371141)
                ·
                  refine ⟨19679317243967800757089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104956358634494937371141 19679317243967800757089)
                  ·
                    refine ⟨14759487932975850567817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19679317243967800757089 14759487932975850567817)
                    ·
                      refine ⟨11069615949731887925863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14759487932975850567817 11069615949731887925863)
                      ·
                        rfl

theorem cell23_21558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_21558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21558 prefixEnd_21558 := by exact prefixLift 21558
  have htrace : WordTrace (prefixWord ++ tailWord_21558) baseStart_21558 baseEnd_21558 := by
    simpa [prefixWord, tailWord_21558, baseEnd_21558] using wordTrace_append hprefix tailTrace_21558
  have hstable : (prefixWord ++ tailWord_21558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21558).length < 2 ^ (prefixWord ++ tailWord_21558).sum := by decide
  have hdescent : baseEnd_21558 < baseStart_21558 := by decide
  rcases family_descends (prefixWord ++ tailWord_21558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21564 : List Nat := [2, 2, 2, 2, 2, 2, 2, 4, 5]
def baseStart_21564 : Nat := 118140960795 + 21564 * 2 ^ 59
def prefixEnd_21564 : Nat := 4983230072969 + 3 ^ 40 * 21564 * 2
def baseEnd_21564 : Nat := 1230299648184318272315

theorem tailTrace_21564 : CollatzResearch.WordTrace tailWord_21564 prefixEnd_21564 1230299648184318272315 := by
  unfold tailWord_21564
  simp only [CollatzResearch.WordTrace]
  refine ⟨393251846942392841551873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 524335795923190455402497 393251846942392841551873)
  ·
    refine ⟨294938885206794631163905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 393251846942392841551873 294938885206794631163905)
    ·
      refine ⟨221204163905095973372929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294938885206794631163905 221204163905095973372929)
      ·
        refine ⟨165903122928821980029697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221204163905095973372929 165903122928821980029697)
        ·
          refine ⟨124427342196616485022273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165903122928821980029697 124427342196616485022273)
          ·
            refine ⟨93320506647462363766705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124427342196616485022273 93320506647462363766705)
            ·
              refine ⟨69990379985596772825029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93320506647462363766705 69990379985596772825029)
              ·
                refine ⟨13123196247299394904693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69990379985596772825029 13123196247299394904693)
                ·
                  refine ⟨1230299648184318272315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13123196247299394904693 1230299648184318272315)
                  ·
                    rfl

theorem cell23_21564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_21564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21564 prefixEnd_21564 := by exact prefixLift 21564
  have htrace : WordTrace (prefixWord ++ tailWord_21564) baseStart_21564 baseEnd_21564 := by
    simpa [prefixWord, tailWord_21564, baseEnd_21564] using wordTrace_append hprefix tailTrace_21564
  have hstable : (prefixWord ++ tailWord_21564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21564).length < 2 ^ (prefixWord ++ tailWord_21564).sum := by decide
  have hdescent : baseEnd_21564 < baseStart_21564 := by decide
  rcases family_descends (prefixWord ++ tailWord_21564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21614 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_21614 : Nat := 118140960795 + 21614 * 2 ^ 59
def prefixEnd_21614 : Nat := 4983230072969 + 3 ^ 40 * 21614 * 2
def baseEnd_21614 : Nat := 11098370866383668825605

theorem tailTrace_21614 : CollatzResearch.WordTrace tailWord_21614 prefixEnd_21614 11098370866383668825605 := by
  unfold tailWord_21614
  simp only [CollatzResearch.WordTrace]
  refine ⟨98540917962955527802987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 525551562469096148282597 98540917962955527802987)
  ·
    refine ⟨147811376944433291704481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98540917962955527802987 147811376944433291704481)
    ·
      refine ⟨110858532708324968778361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147811376944433291704481 110858532708324968778361)
      ·
        refine ⟨83143899531243726583771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110858532708324968778361 83143899531243726583771)
        ·
          refine ⟨124715849296865589875657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83143899531243726583771 124715849296865589875657)
          ·
            refine ⟨93536886972649192406743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124715849296865589875657 93536886972649192406743)
            ·
              refine ⟨140305330458973788610115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93536886972649192406743 140305330458973788610115)
              ·
                refine ⟨210457995688460682915173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140305330458973788610115 210457995688460682915173)
                ·
                  refine ⟨39460874191586378046595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210457995688460682915173 39460874191586378046595)
                  ·
                    refine ⟨59191311287379567069893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39460874191586378046595 59191311287379567069893)
                    ·
                      refine ⟨11098370866383668825605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 59191311287379567069893 11098370866383668825605)
                      ·
                        rfl

theorem cell23_21614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_21614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21614 prefixEnd_21614 := by exact prefixLift 21614
  have htrace : WordTrace (prefixWord ++ tailWord_21614) baseStart_21614 baseEnd_21614 := by
    simpa [prefixWord, tailWord_21614, baseEnd_21614] using wordTrace_append hprefix tailTrace_21614
  have hstable : (prefixWord ++ tailWord_21614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21614).length < 2 ^ (prefixWord ++ tailWord_21614).sum := by decide
  have hdescent : baseEnd_21614 < baseStart_21614 := by decide
  rcases family_descends (prefixWord ++ tailWord_21614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21617 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 3, 4, 3]
def baseStart_21617 : Nat := 118140960795 + 21617 * 2 ^ 59
def prefixEnd_21617 : Nat := 4983230072969 + 3 ^ 40 * 21617 * 2
def baseEnd_21617 : Nat := 11099911308347157088091

theorem tailTrace_21617 : CollatzResearch.WordTrace tailWord_21617 prefixEnd_21617 11099911308347157088091 := by
  unfold tailWord_21617
  simp only [CollatzResearch.WordTrace]
  refine ⟨788436762692775734783105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 525624508461850489855403 788436762692775734783105)
  ·
    refine ⟨591327572019581801087329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 788436762692775734783105 591327572019581801087329)
    ·
      refine ⟨443495679014686350815497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 591327572019581801087329 443495679014686350815497)
      ·
        refine ⟨332621759261014763111623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443495679014686350815497 332621759261014763111623)
        ·
          refine ⟨498932638891522144667435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332621759261014763111623 498932638891522144667435)
          ·
            refine ⟨748398958337283217001153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498932638891522144667435 748398958337283217001153)
            ·
              refine ⟨561299218752962412750865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748398958337283217001153 561299218752962412750865)
              ·
                refine ⟨420974414064721809563149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561299218752962412750865 420974414064721809563149)
                ·
                  refine ⟨157865405274270678586181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420974414064721809563149 157865405274270678586181)
                  ·
                    refine ⟨29599763488925752234909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 157865405274270678586181 29599763488925752234909)
                    ·
                      refine ⟨11099911308347157088091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 29599763488925752234909 11099911308347157088091)
                      ·
                        rfl

theorem cell23_21617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_21617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21617 prefixEnd_21617 := by exact prefixLift 21617
  have htrace : WordTrace (prefixWord ++ tailWord_21617) baseStart_21617 baseEnd_21617 := by
    simpa [prefixWord, tailWord_21617, baseEnd_21617] using wordTrace_append hprefix tailTrace_21617
  have hstable : (prefixWord ++ tailWord_21617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21617).length < 2 ^ (prefixWord ++ tailWord_21617).sum := by decide
  have hdescent : baseEnd_21617 < baseStart_21617 := by decide
  rcases family_descends (prefixWord ++ tailWord_21617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21621 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_21621 : Nat := 118140960795 + 21621 * 2 ^ 59
def prefixEnd_21621 : Nat := 4983230072969 + 3 ^ 40 * 21621 * 2
def baseEnd_21621 : Nat := 11101965230965141438073

theorem tailTrace_21621 : CollatzResearch.WordTrace tailWord_21621 prefixEnd_21621 11101965230965141438073 := by
  unfold tailWord_21621
  simp only [CollatzResearch.WordTrace]
  refine ⟨788582654678284417928717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 525721769785522945285811 788582654678284417928717)
  ·
    refine ⟨295718495504356656723269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 788582654678284417928717 295718495504356656723269)
    ·
      refine ⟨55447217907066873135613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295718495504356656723269 55447217907066873135613)
      ·
        refine ⟨20792706715150077425855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55447217907066873135613 20792706715150077425855)
        ·
          refine ⟨31189060072725116138783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20792706715150077425855 31189060072725116138783)
          ·
            refine ⟨46783590109087674208175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31189060072725116138783 46783590109087674208175)
            ·
              refine ⟨70175385163631511312263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46783590109087674208175 70175385163631511312263)
              ·
                refine ⟨105263077745447266968395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70175385163631511312263 105263077745447266968395)
                ·
                  refine ⟨157894616618170900452593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105263077745447266968395 157894616618170900452593)
                  ·
                    refine ⟨118420962463628175339445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157894616618170900452593 118420962463628175339445)
                    ·
                      refine ⟨11101965230965141438073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 118420962463628175339445 11101965230965141438073)
                      ·
                        rfl

theorem cell23_21621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_21621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21621 prefixEnd_21621 := by exact prefixLift 21621
  have htrace : WordTrace (prefixWord ++ tailWord_21621) baseStart_21621 baseEnd_21621 := by
    simpa [prefixWord, tailWord_21621, baseEnd_21621] using wordTrace_append hprefix tailTrace_21621
  have hstable : (prefixWord ++ tailWord_21621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21621).length < 2 ^ (prefixWord ++ tailWord_21621).sum := by decide
  have hdescent : baseEnd_21621 < baseStart_21621 := by decide
  rcases family_descends (prefixWord ++ tailWord_21621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21624 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 3, 4]
def baseStart_21624 : Nat := 118140960795 + 21624 * 2 ^ 59
def prefixEnd_21624 : Nat := 4983230072969 + 3 ^ 40 * 21624 * 2
def baseEnd_21624 : Nat := 3701168557642876566853

theorem tailTrace_21624 : CollatzResearch.WordTrace tailWord_21624 prefixEnd_21624 3701168557642876566853 := by
  unfold tailWord_21624
  simp only [CollatzResearch.WordTrace]
  refine ⟨394346036833707965143963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 525794715778277286858617 394346036833707965143963)
  ·
    refine ⟨591519055250561947715945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 394346036833707965143963 591519055250561947715945)
    ·
      refine ⟨443639291437921460786959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 591519055250561947715945 443639291437921460786959)
      ·
        refine ⟨665458937156882191180439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443639291437921460786959 665458937156882191180439)
        ·
          refine ⟨998188405735323286770659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665458937156882191180439 998188405735323286770659)
          ·
            refine ⟨1497282608602984930155989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998188405735323286770659 1497282608602984930155989)
            ·
              refine ⟨35092561139132459300531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1497282608602984930155989 35092561139132459300531)
              ·
                refine ⟨52638841708698688950797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35092561139132459300531 52638841708698688950797)
                ·
                  refine ⟨19739565640762008356549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52638841708698688950797 19739565640762008356549)
                  ·
                    refine ⟨3701168557642876566853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19739565640762008356549 3701168557642876566853)
                    ·
                      rfl

theorem cell23_21624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_21624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21624 prefixEnd_21624 := by exact prefixLift 21624
  have htrace : WordTrace (prefixWord ++ tailWord_21624) baseStart_21624 baseEnd_21624 := by
    simpa [prefixWord, tailWord_21624, baseEnd_21624] using wordTrace_append hprefix tailTrace_21624
  have hstable : (prefixWord ++ tailWord_21624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21624).length < 2 ^ (prefixWord ++ tailWord_21624).sum := by decide
  have hdescent : baseEnd_21624 < baseStart_21624 := by decide
  rcases family_descends (prefixWord ++ tailWord_21624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21671 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 6]
def baseStart_21671 : Nat := 118140960795 + 21671 * 2 ^ 59
def prefixEnd_21671 : Nat := 4983230072969 + 3 ^ 40 * 21671 * 2
def baseEnd_21671 : Nat := 1236404362632216201427

theorem tailTrace_21671 : CollatzResearch.WordTrace tailWord_21671 prefixEnd_21671 1236404362632216201427 := by
  unfold tailWord_21671
  simp only [CollatzResearch.WordTrace]
  refine ⟨790406304497142957248867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 526937536331428638165911 790406304497142957248867)
  ·
    refine ⟨1185609456745714435873301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 790406304497142957248867 1185609456745714435873301)
    ·
      refine ⟨55575443284955364181561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1185609456745714435873301 55575443284955364181561)
      ·
        refine ⟨41681582463716523136171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55575443284955364181561 41681582463716523136171)
        ·
          refine ⟨62522373695574784704257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41681582463716523136171 62522373695574784704257)
          ·
            refine ⟨46891780271681088528193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62522373695574784704257 46891780271681088528193)
            ·
              refine ⟨35168835203760816396145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46891780271681088528193 35168835203760816396145)
              ·
                refine ⟨26376626402820612297109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35168835203760816396145 26376626402820612297109)
                ·
                  refine ⟨1236404362632216201427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26376626402820612297109 1236404362632216201427)
                  ·
                    rfl

theorem cell23_21671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 6].length) (baseStart_21671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21671 prefixEnd_21671 := by exact prefixLift 21671
  have htrace : WordTrace (prefixWord ++ tailWord_21671) baseStart_21671 baseEnd_21671 := by
    simpa [prefixWord, tailWord_21671, baseEnd_21671] using wordTrace_append hprefix tailTrace_21671
  have hstable : (prefixWord ++ tailWord_21671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21671).length < 2 ^ (prefixWord ++ tailWord_21671).sum := by decide
  have hdescent : baseEnd_21671 < baseStart_21671 := by decide
  rcases family_descends (prefixWord ++ tailWord_21671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21704 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_21704 : Nat := 118140960795 + 21704 * 2 ^ 59
def prefixEnd_21704 : Nat := 4983230072969 + 3 ^ 40 * 21704 * 2
def baseEnd_21704 : Nat := 11144584125288316700191

theorem tailTrace_21704 : CollatzResearch.WordTrace tailWord_21704 prefixEnd_21704 11144584125288316700191 := by
  unfold tailWord_21704
  simp only [CollatzResearch.WordTrace]
  refine ⟨395804956688794796600083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 527739942251726395466777 395804956688794796600083)
  ·
    refine ⟨593707435033192194900125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 395804956688794796600083 593707435033192194900125)
    ·
      refine ⟨222640288137447073087547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 593707435033192194900125 222640288137447073087547)
      ·
        refine ⟨333960432206170609631321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222640288137447073087547 333960432206170609631321)
        ·
          refine ⟨250470324154627957223491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333960432206170609631321 250470324154627957223491)
          ·
            refine ⟨375705486231941935835237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250470324154627957223491 375705486231941935835237)
            ·
              refine ⟨70444778668489112969107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 375705486231941935835237 70444778668489112969107)
              ·
                refine ⟨105667168002733669453661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70444778668489112969107 105667168002733669453661)
                ·
                  refine ⟨39625188001025126045123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105667168002733669453661 39625188001025126045123)
                  ·
                    refine ⟨59437782001537689067685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39625188001025126045123 59437782001537689067685)
                    ·
                      refine ⟨11144584125288316700191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 59437782001537689067685 11144584125288316700191)
                      ·
                        rfl

theorem cell23_21704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_21704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21704 prefixEnd_21704 := by exact prefixLift 21704
  have htrace : WordTrace (prefixWord ++ tailWord_21704) baseStart_21704 baseEnd_21704 := by
    simpa [prefixWord, tailWord_21704, baseEnd_21704] using wordTrace_append hprefix tailTrace_21704
  have hstable : (prefixWord ++ tailWord_21704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21704).length < 2 ^ (prefixWord ++ tailWord_21704).sum := by decide
  have hdescent : baseEnd_21704 < baseStart_21704 := by decide
  rcases family_descends (prefixWord ++ tailWord_21704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21707 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 5]
def baseStart_21707 : Nat := 118140960795 + 21707 * 2 ^ 59
def prefixEnd_21707 : Nat := 4983230072969 + 3 ^ 40 * 21707 * 2
def baseEnd_21707 : Nat := 11146124567251804962677

theorem tailTrace_21707 : CollatzResearch.WordTrace tailWord_21707 prefixEnd_21707 11146124567251804962677 := by
  unfold tailWord_21707
  simp only [CollatzResearch.WordTrace]
  refine ⟨791719332366721105559375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 527812888244480737039583 791719332366721105559375)
  ·
    refine ⟨1187578998550081658339063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 791719332366721105559375 1187578998550081658339063)
    ·
      refine ⟨1781368497825122487508595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1187578998550081658339063 1781368497825122487508595)
      ·
        refine ⟨2672052746737683731262893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781368497825122487508595 2672052746737683731262893)
        ·
          refine ⟨1002019780026631399223585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2672052746737683731262893 1002019780026631399223585)
          ·
            refine ⟨751514835019973549417689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002019780026631399223585 751514835019973549417689)
            ·
              refine ⟨563636126264980162063267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 751514835019973549417689 563636126264980162063267)
              ·
                refine ⟨845454189397470243094901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563636126264980162063267 845454189397470243094901)
                ·
                  refine ⟨79261330256012835290147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 845454189397470243094901 79261330256012835290147)
                  ·
                    refine ⟨118891995384019252935221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79261330256012835290147 118891995384019252935221)
                    ·
                      refine ⟨11146124567251804962677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 118891995384019252935221 11146124567251804962677)
                      ·
                        rfl

theorem cell23_21707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 5].length) (baseStart_21707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21707 prefixEnd_21707 := by exact prefixLift 21707
  have htrace : WordTrace (prefixWord ++ tailWord_21707) baseStart_21707 baseEnd_21707 := by
    simpa [prefixWord, tailWord_21707, baseEnd_21707] using wordTrace_append hprefix tailTrace_21707
  have hstable : (prefixWord ++ tailWord_21707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21707).length < 2 ^ (prefixWord ++ tailWord_21707).sum := by decide
  have hdescent : baseEnd_21707 < baseStart_21707 := by decide
  rcases family_descends (prefixWord ++ tailWord_21707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21714 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_21714 : Nat := 118140960795 + 21714 * 2 ^ 59
def prefixEnd_21714 : Nat := 4983230072969 + 3 ^ 40 * 21714 * 2
def baseEnd_21714 : Nat := 3716572977277759191715

theorem tailTrace_21714 : CollatzResearch.WordTrace tailWord_21714 prefixEnd_21714 3716572977277759191715 := by
  unfold tailWord_21714
  simp only [CollatzResearch.WordTrace]
  refine ⟨197993660835340325266049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 527983095560907534042797 197993660835340325266049)
  ·
    refine ⟨148495245626505243949537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197993660835340325266049 148495245626505243949537)
    ·
      refine ⟨111371434219878932962153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148495245626505243949537 111371434219878932962153)
      ·
        refine ⟨83528575664909199721615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111371434219878932962153 83528575664909199721615)
        ·
          refine ⟨125292863497363799582423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83528575664909199721615 125292863497363799582423)
          ·
            refine ⟨187939295246045699373635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125292863497363799582423 187939295246045699373635)
            ·
              refine ⟨281908942869068549060453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187939295246045699373635 281908942869068549060453)
              ·
                refine ⟨52857926787950352948835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281908942869068549060453 52857926787950352948835)
                ·
                  refine ⟨79286890181925529423253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52857926787950352948835 79286890181925529423253)
                  ·
                    refine ⟨3716572977277759191715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79286890181925529423253 3716572977277759191715)
                    ·
                      rfl

theorem cell23_21714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_21714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21714 prefixEnd_21714 := by exact prefixLift 21714
  have htrace : WordTrace (prefixWord ++ tailWord_21714) baseStart_21714 baseEnd_21714 := by
    simpa [prefixWord, tailWord_21714, baseEnd_21714] using wordTrace_append hprefix tailTrace_21714
  have hstable : (prefixWord ++ tailWord_21714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21714).length < 2 ^ (prefixWord ++ tailWord_21714).sum := by decide
  have hdescent : baseEnd_21714 < baseStart_21714 := by decide
  rcases family_descends (prefixWord ++ tailWord_21714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21721 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 7, 2, 2]
def baseStart_21721 : Nat := 118140960795 + 21721 * 2 ^ 59
def prefixEnd_21721 : Nat := 4983230072969 + 3 ^ 40 * 21721 * 2
def baseEnd_21721 : Nat := 11153313296414750187613

theorem tailTrace_21721 : CollatzResearch.WordTrace tailWord_21721 prefixEnd_21721 11153313296414750187613 := by
  unfold tailWord_21721
  simp only [CollatzResearch.WordTrace]
  refine ⟨792229954316001496569017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 528153302877334331046011 792229954316001496569017)
  ·
    refine ⟨594172465737001122426763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 792229954316001496569017 594172465737001122426763)
    ·
      refine ⟨891258698605501683640145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 594172465737001122426763 891258698605501683640145)
      ·
        refine ⟨668444023954126262730109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 891258698605501683640145 668444023954126262730109)
        ·
          refine ⟨250666508982797348523791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 668444023954126262730109 250666508982797348523791)
          ·
            refine ⟨375999763474196022785687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250666508982797348523791 375999763474196022785687)
            ·
              refine ⟨563999645211294034178531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375999763474196022785687 563999645211294034178531)
              ·
                refine ⟨845999467816941051267797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563999645211294034178531 845999467816941051267797)
                ·
                  refine ⟨19828112526959555889089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 845999467816941051267797 19828112526959555889089)
                  ·
                    refine ⟨14871084395219666916817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19828112526959555889089 14871084395219666916817)
                    ·
                      refine ⟨11153313296414750187613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14871084395219666916817 11153313296414750187613)
                      ·
                        rfl

theorem cell23_21721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 2, 2].length) (baseStart_21721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21721 prefixEnd_21721 := by exact prefixLift 21721
  have htrace : WordTrace (prefixWord ++ tailWord_21721) baseStart_21721 baseEnd_21721 := by
    simpa [prefixWord, tailWord_21721, baseEnd_21721] using wordTrace_append hprefix tailTrace_21721
  have hstable : (prefixWord ++ tailWord_21721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21721).length < 2 ^ (prefixWord ++ tailWord_21721).sum := by decide
  have hdescent : baseEnd_21721 < baseStart_21721 := by decide
  rcases family_descends (prefixWord ++ tailWord_21721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21738 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_21738 : Nat := 118140960795 + 21738 * 2 ^ 59
def prefixEnd_21738 : Nat := 4983230072969 + 3 ^ 40 * 21738 * 2
def baseEnd_21738 : Nat := 11162042467541183675035

theorem tailTrace_21738 : CollatzResearch.WordTrace tailWord_21738 prefixEnd_21738 11162042467541183675035 := by
  unfold tailWord_21738
  simp only [CollatzResearch.WordTrace]
  refine ⟨198212498813603349984467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 528566663502942266625245 198212498813603349984467)
  ·
    refine ⟨297318748220405024976701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198212498813603349984467 297318748220405024976701)
    ·
      refine ⟨111494530582651884366263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297318748220405024976701 111494530582651884366263)
      ·
        refine ⟨167241795873977826549395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111494530582651884366263 167241795873977826549395)
        ·
          refine ⟨250862693810966739824093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167241795873977826549395 250862693810966739824093)
          ·
            refine ⟨94073510179112527434035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250862693810966739824093 94073510179112527434035)
            ·
              refine ⟨141110265268668791151053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94073510179112527434035 141110265268668791151053)
              ·
                refine ⟨52916349475750796681645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141110265268668791151053 52916349475750796681645)
                ·
                  refine ⟨19843631053406548755617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52916349475750796681645 19843631053406548755617)
                  ·
                    refine ⟨14882723290054911566713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19843631053406548755617 14882723290054911566713)
                    ·
                      refine ⟨11162042467541183675035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14882723290054911566713 11162042467541183675035)
                      ·
                        rfl

theorem cell23_21738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_21738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21738 prefixEnd_21738 := by exact prefixLift 21738
  have htrace : WordTrace (prefixWord ++ tailWord_21738) baseStart_21738 baseEnd_21738 := by
    simpa [prefixWord, tailWord_21738, baseEnd_21738] using wordTrace_append hprefix tailTrace_21738
  have hstable : (prefixWord ++ tailWord_21738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21738).length < 2 ^ (prefixWord ++ tailWord_21738).sum := by decide
  have hdescent : baseEnd_21738 < baseStart_21738 := by decide
  rcases family_descends (prefixWord ++ tailWord_21738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21741 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_21741 : Nat := 118140960795 + 21741 * 2 ^ 59
def prefixEnd_21741 : Nat := 4983230072969 + 3 ^ 40 * 21741 * 2
def baseEnd_21741 : Nat := 11163582909504671937521

theorem tailTrace_21741 : CollatzResearch.WordTrace tailWord_21741 prefixEnd_21741 11163582909504671937521 := by
  unfold tailWord_21741
  simp only [CollatzResearch.WordTrace]
  refine ⟨792959414243544912297077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 528639609495696608198051 792959414243544912297077)
  ·
    refine ⟨74339945085332335527851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 792959414243544912297077 74339945085332335527851)
    ·
      refine ⟨111509917627998503291777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74339945085332335527851 111509917627998503291777)
      ·
        refine ⟨83632438220998877468833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111509917627998503291777 83632438220998877468833)
        ·
          refine ⟨62724328665749158101625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83632438220998877468833 62724328665749158101625)
          ·
            refine ⟨47043246499311868576219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62724328665749158101625 47043246499311868576219)
            ·
              refine ⟨70564869748967802864329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47043246499311868576219 70564869748967802864329)
              ·
                refine ⟨52923652311725852148247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70564869748967802864329 52923652311725852148247)
                ·
                  refine ⟨79385478467588778222371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52923652311725852148247 79385478467588778222371)
                  ·
                    refine ⟨119078217701383167333557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79385478467588778222371 119078217701383167333557)
                    ·
                      refine ⟨11163582909504671937521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 119078217701383167333557 11163582909504671937521)
                      ·
                        rfl

theorem cell23_21741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_21741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21741 prefixEnd_21741 := by exact prefixLift 21741
  have htrace : WordTrace (prefixWord ++ tailWord_21741) baseStart_21741 baseEnd_21741 := by
    simpa [prefixWord, tailWord_21741, baseEnd_21741] using wordTrace_append hprefix tailTrace_21741
  have hstable : (prefixWord ++ tailWord_21741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21741).length < 2 ^ (prefixWord ++ tailWord_21741).sum := by decide
  have hdescent : baseEnd_21741 < baseStart_21741 := by decide
  rcases family_descends (prefixWord ++ tailWord_21741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21758 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_21758 : Nat := 118140960795 + 21758 * 2 ^ 59
def prefixEnd_21758 : Nat := 4983230072969 + 3 ^ 40 * 21758 * 2
def baseEnd_21758 : Nat := 11172312080631105424943

theorem tailTrace_21758 : CollatzResearch.WordTrace tailWord_21758 prefixEnd_21758 11172312080631105424943 := by
  unfold tailWord_21758
  simp only [CollatzResearch.WordTrace]
  refine ⟨99197431897744601958241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 529052970121304543777285 99197431897744601958241)
  ·
    refine ⟨74398073923308451468681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99197431897744601958241 74398073923308451468681)
    ·
      refine ⟨55798555442481338601511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74398073923308451468681 55798555442481338601511)
      ·
        refine ⟨83697833163722007902267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55798555442481338601511 83697833163722007902267)
        ·
          refine ⟨125546749745583011853401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83697833163722007902267 125546749745583011853401)
          ·
            refine ⟨94160062309187258890051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125546749745583011853401 94160062309187258890051)
            ·
              refine ⟨141240093463780888335077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94160062309187258890051 141240093463780888335077)
              ·
                refine ⟨26482517524458916562827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141240093463780888335077 26482517524458916562827)
                ·
                  refine ⟨39723776286688374844241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26482517524458916562827 39723776286688374844241)
                  ·
                    refine ⟨29792832215016281133181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39723776286688374844241 29792832215016281133181)
                    ·
                      refine ⟨11172312080631105424943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 29792832215016281133181 11172312080631105424943)
                      ·
                        rfl

theorem cell23_21758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_21758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21758 prefixEnd_21758 := by exact prefixLift 21758
  have htrace : WordTrace (prefixWord ++ tailWord_21758) baseStart_21758 baseEnd_21758 := by
    simpa [prefixWord, tailWord_21758, baseEnd_21758] using wordTrace_append hprefix tailTrace_21758
  have hstable : (prefixWord ++ tailWord_21758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21758).length < 2 ^ (prefixWord ++ tailWord_21758).sum := by decide
  have hdescent : baseEnd_21758 < baseStart_21758 := by decide
  rcases family_descends (prefixWord ++ tailWord_21758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21761 : List Nat := [1, 2, 4, 1, 1, 5, 2, 7]
def baseStart_21761 : Nat := 118140960795 + 21761 * 2 ^ 59
def prefixEnd_21761 : Nat := 4983230072969 + 3 ^ 40 * 21761 * 2
def baseEnd_21761 : Nat := 413846389725725692127

theorem tailTrace_21761 : CollatzResearch.WordTrace tailWord_21761 prefixEnd_21761 413846389725725692127 := by
  unfold tailWord_21761
  simp only [CollatzResearch.WordTrace]
  refine ⟨793688874171088328025137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 529125916114058885350091 793688874171088328025137)
  ·
    refine ⟨595266655628316246018853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 793688874171088328025137 595266655628316246018853)
    ·
      refine ⟨111612497930309296128535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 595266655628316246018853 111612497930309296128535)
      ·
        refine ⟨167418746895463944192803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111612497930309296128535 167418746895463944192803)
        ·
          refine ⟨251128120343195916289205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167418746895463944192803 251128120343195916289205)
          ·
            refine ⟨23543261282174617152113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 251128120343195916289205 23543261282174617152113)
            ·
              refine ⟨17657445961630962864085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23543261282174617152113 17657445961630962864085)
              ·
                refine ⟨413846389725725692127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17657445961630962864085 413846389725725692127)
                ·
                  rfl

theorem cell23_21761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 7].length) (baseStart_21761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21761 prefixEnd_21761 := by exact prefixLift 21761
  have htrace : WordTrace (prefixWord ++ tailWord_21761) baseStart_21761 baseEnd_21761 := by
    simpa [prefixWord, tailWord_21761, baseEnd_21761] using wordTrace_append hprefix tailTrace_21761
  have hstable : (prefixWord ++ tailWord_21761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21761).length < 2 ^ (prefixWord ++ tailWord_21761).sum := by decide
  have hdescent : baseEnd_21761 < baseStart_21761 := by decide
  rcases family_descends (prefixWord ++ tailWord_21761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21771 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 4, 1, 3]
def baseStart_21771 : Nat := 118140960795 + 21771 * 2 ^ 59
def prefixEnd_21771 : Nat := 4983230072969 + 3 ^ 40 * 21771 * 2
def baseEnd_21771 : Nat := 11178987329139554562383

theorem tailTrace_21771 : CollatzResearch.WordTrace tailWord_21771 prefixEnd_21771 11178987329139554562383 := by
  unfold tailWord_21771
  simp only [CollatzResearch.WordTrace]
  refine ⟨794053604134860035889167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 529369069423240023926111 794053604134860035889167)
  ·
    refine ⟨1191080406202290053833751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 794053604134860035889167 1191080406202290053833751)
    ·
      refine ⟨1786620609303435080750627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191080406202290053833751 1786620609303435080750627)
      ·
        refine ⟨2679930913955152621125941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786620609303435080750627 2679930913955152621125941)
        ·
          refine ⟨251243523183295558230557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2679930913955152621125941 251243523183295558230557)
          ·
            refine ⟨94216321193735834336459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251243523183295558230557 94216321193735834336459)
            ·
              refine ⟨141324481790603751504689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94216321193735834336459 141324481790603751504689)
              ·
                refine ⟨105993361342952813628517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141324481790603751504689 105993361342952813628517)
                ·
                  refine ⟨19873755251803652555347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105993361342952813628517 19873755251803652555347)
                  ·
                    refine ⟨29810632877705478833021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19873755251803652555347 29810632877705478833021)
                    ·
                      refine ⟨11178987329139554562383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 29810632877705478833021 11178987329139554562383)
                      ·
                        rfl

theorem cell23_21771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 1, 3].length) (baseStart_21771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21771 prefixEnd_21771 := by exact prefixLift 21771
  have htrace : WordTrace (prefixWord ++ tailWord_21771) baseStart_21771 baseEnd_21771 := by
    simpa [prefixWord, tailWord_21771, baseEnd_21771] using wordTrace_append hprefix tailTrace_21771
  have hstable : (prefixWord ++ tailWord_21771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21771).length < 2 ^ (prefixWord ++ tailWord_21771).sum := by decide
  have hdescent : baseEnd_21771 < baseStart_21771 := by decide
  rcases family_descends (prefixWord ++ tailWord_21771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21772 : List Nat := [2, 2, 1, 2, 2, 5, 1, 3, 1, 2, 2]
def baseStart_21772 : Nat := 118140960795 + 21772 * 2 ^ 59
def prefixEnd_21772 : Nat := 4983230072969 + 3 ^ 40 * 21772 * 2
def baseEnd_21772 : Nat := 11179500809794050649879

theorem tailTrace_21772 : CollatzResearch.WordTrace tailWord_21772 prefixEnd_21772 11179500809794050649879 := by
  unfold tailWord_21772
  simp only [CollatzResearch.WordTrace]
  refine ⟨397045038565618603337785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 529393384754158137783713 397045038565618603337785)
  ·
    refine ⟨297783778924213952503339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 397045038565618603337785 297783778924213952503339)
    ·
      refine ⟨446675668386320928755009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297783778924213952503339 446675668386320928755009)
      ·
        refine ⟨335006751289740696566257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446675668386320928755009 335006751289740696566257)
        ·
          refine ⟨251255063467305522424693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335006751289740696566257 251255063467305522424693)
          ·
            refine ⟨23555162200059892727315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 251255063467305522424693 23555162200059892727315)
            ·
              refine ⟨35332743300089839090973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23555162200059892727315 35332743300089839090973)
              ·
                refine ⟨13249778737533689659115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35332743300089839090973 13249778737533689659115)
                ·
                  refine ⟨19874668106300534488673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13249778737533689659115 19874668106300534488673)
                  ·
                    refine ⟨14906001079725400866505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19874668106300534488673 14906001079725400866505)
                    ·
                      refine ⟨11179500809794050649879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14906001079725400866505 11179500809794050649879)
                      ·
                        rfl

theorem cell23_21772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_21772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21772 prefixEnd_21772 := by exact prefixLift 21772
  have htrace : WordTrace (prefixWord ++ tailWord_21772) baseStart_21772 baseEnd_21772 := by
    simpa [prefixWord, tailWord_21772, baseEnd_21772] using wordTrace_append hprefix tailTrace_21772
  have hstable : (prefixWord ++ tailWord_21772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21772).length < 2 ^ (prefixWord ++ tailWord_21772).sum := by decide
  have hdescent : baseEnd_21772 < baseStart_21772 := by decide
  rcases family_descends (prefixWord ++ tailWord_21772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21778 : List Nat := [3, 2, 4, 2, 1, 2, 9]
def baseStart_21778 : Nat := 118140960795 + 21778 * 2 ^ 59
def prefixEnd_21778 : Nat := 4983230072969 + 3 ^ 40 * 21778 * 2
def baseEnd_21778 : Nat := 138056564120012681171

theorem tailTrace_21778 : CollatzResearch.WordTrace tailWord_21778 prefixEnd_21778 138056564120012681171 := by
  unfold tailWord_21778
  simp only [CollatzResearch.WordTrace]
  refine ⟨198577228777375057848497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 529539276739666820929325 198577228777375057848497)
  ·
    refine ⟨148932921583031293386373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198577228777375057848497 148932921583031293386373)
    ·
      refine ⟨27924922796818367509945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148932921583031293386373 27924922796818367509945)
      ·
        refine ⟨20943692097613775632459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27924922796818367509945 20943692097613775632459)
        ·
          refine ⟨31415538146420663448689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20943692097613775632459 31415538146420663448689)
          ·
            refine ⟨23561653609815497586517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31415538146420663448689 23561653609815497586517)
            ·
              refine ⟨138056564120012681171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 23561653609815497586517 138056564120012681171)
              ·
                rfl

theorem cell23_21778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 9].length) (baseStart_21778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21778 prefixEnd_21778 := by exact prefixLift 21778
  have htrace : WordTrace (prefixWord ++ tailWord_21778) baseStart_21778 baseEnd_21778 := by
    simpa [prefixWord, tailWord_21778, baseEnd_21778] using wordTrace_append hprefix tailTrace_21778
  have hstable : (prefixWord ++ tailWord_21778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21778).length < 2 ^ (prefixWord ++ tailWord_21778).sum := by decide
  have hdescent : baseEnd_21778 < baseStart_21778 := by decide
  rcases family_descends (prefixWord ++ tailWord_21778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21781 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 5, 3, 2]
def baseStart_21781 : Nat := 118140960795 + 21781 * 2 ^ 59
def prefixEnd_21781 : Nat := 4983230072969 + 3 ^ 40 * 21781 * 2
def baseEnd_21781 : Nat := 11184122135684515437337

theorem tailTrace_21781 : CollatzResearch.WordTrace tailWord_21781 prefixEnd_21781 11184122135684515437337 := by
  unfold tailWord_21781
  simp only [CollatzResearch.WordTrace]
  refine ⟨794418334098631743753197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 529612222732421162502131 794418334098631743753197)
  ·
    refine ⟨297906875286986903907449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 794418334098631743753197 297906875286986903907449)
    ·
      refine ⟨223430156465240177930587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297906875286986903907449 223430156465240177930587)
      ·
        refine ⟨335145234697860266895881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223430156465240177930587 335145234697860266895881)
        ·
          refine ⟨251358926023395200171911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335145234697860266895881 251358926023395200171911)
          ·
            refine ⟨377038389035092800257867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251358926023395200171911 377038389035092800257867)
            ·
              refine ⟨565557583552639200386801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377038389035092800257867 565557583552639200386801)
              ·
                refine ⟨424168187664479400290101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565557583552639200386801 424168187664479400290101)
                ·
                  refine ⟨39765767593544943777197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 424168187664479400290101 39765767593544943777197)
                  ·
                    refine ⟨14912162847579353916449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39765767593544943777197 14912162847579353916449)
                    ·
                      refine ⟨11184122135684515437337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14912162847579353916449 11184122135684515437337)
                      ·
                        rfl

theorem cell23_21781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_21781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21781 prefixEnd_21781 := by exact prefixLift 21781
  have htrace : WordTrace (prefixWord ++ tailWord_21781) baseStart_21781 baseEnd_21781 := by
    simpa [prefixWord, tailWord_21781, baseEnd_21781] using wordTrace_append hprefix tailTrace_21781
  have hstable : (prefixWord ++ tailWord_21781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21781).length < 2 ^ (prefixWord ++ tailWord_21781).sum := by decide
  have hdescent : baseEnd_21781 < baseStart_21781 := by decide
  rcases family_descends (prefixWord ++ tailWord_21781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21789 : List Nat := [1, 4, 2, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_21789 : Nat := 118140960795 + 21789 * 2 ^ 59
def prefixEnd_21789 : Nat := 4983230072969 + 3 ^ 40 * 21789 * 2
def baseEnd_21789 : Nat := 11188229980920484137301

theorem tailTrace_21789 : CollatzResearch.WordTrace tailWord_21789 prefixEnd_21789 11188229980920484137301 := by
  unfold tailWord_21789
  simp only [CollatzResearch.WordTrace]
  refine ⟨794710118069649110044421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 529806745379766073362947 794710118069649110044421)
  ·
    refine ⟨149008147138059208133329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 794710118069649110044421 149008147138059208133329)
    ·
      refine ⟨111756110353544406099997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149008147138059208133329 111756110353544406099997)
      ·
        refine ⟨41908541382579152287499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111756110353544406099997 41908541382579152287499)
        ·
          refine ⟨62862812073868728431249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41908541382579152287499 62862812073868728431249)
          ·
            refine ⟨47147109055401546323437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62862812073868728431249 47147109055401546323437)
            ·
              refine ⟨17680165895775579871289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47147109055401546323437 17680165895775579871289)
              ·
                refine ⟨13260124421831684903467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17680165895775579871289 13260124421831684903467)
                ·
                  refine ⟨19890186632747527355201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13260124421831684903467 19890186632747527355201)
                  ·
                    refine ⟨14917639974560645516401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19890186632747527355201 14917639974560645516401)
                    ·
                      refine ⟨11188229980920484137301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14917639974560645516401 11188229980920484137301)
                      ·
                        rfl

theorem cell23_21789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_21789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21789 prefixEnd_21789 := by exact prefixLift 21789
  have htrace : WordTrace (prefixWord ++ tailWord_21789) baseStart_21789 baseEnd_21789 := by
    simpa [prefixWord, tailWord_21789, baseEnd_21789] using wordTrace_append hprefix tailTrace_21789
  have hstable : (prefixWord ++ tailWord_21789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21789).length < 2 ^ (prefixWord ++ tailWord_21789).sum := by decide
  have hdescent : baseEnd_21789 < baseStart_21789 := by decide
  rcases family_descends (prefixWord ++ tailWord_21789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21845 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 2, 2, 2]
def baseStart_21845 : Nat := 118140960795 + 21845 * 2 ^ 59
def prefixEnd_21845 : Nat := 4983230072969 + 3 ^ 40 * 21845 * 2
def baseEnd_21845 : Nat := 11216984897572265037043

theorem tailTrace_21845 : CollatzResearch.WordTrace tailWord_21845 prefixEnd_21845 11216984897572265037043 := by
  unfold tailWord_21845
  simp only [CollatzResearch.WordTrace]
  refine ⟨796752605866770674082989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 531168403911180449388659 796752605866770674082989)
  ·
    refine ⟨298782227200039002781121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 796752605866770674082989 298782227200039002781121)
    ·
      refine ⟨224086670400029252085841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298782227200039002781121 224086670400029252085841)
      ·
        refine ⟨168065002800021939064381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224086670400029252085841 168065002800021939064381)
        ·
          refine ⟨63024376050008227149143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168065002800021939064381 63024376050008227149143)
          ·
            refine ⟨94536564075012340723715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63024376050008227149143 94536564075012340723715)
            ·
              refine ⟨141804846112518511085573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94536564075012340723715 141804846112518511085573)
              ·
                refine ⟨26588408646097220828545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141804846112518511085573 26588408646097220828545)
                ·
                  refine ⟨19941306484572915621409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26588408646097220828545 19941306484572915621409)
                  ·
                    refine ⟨14955979863429686716057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19941306484572915621409 14955979863429686716057)
                    ·
                      refine ⟨11216984897572265037043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14955979863429686716057 11216984897572265037043)
                      ·
                        rfl

theorem cell23_21845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_21845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21845 prefixEnd_21845 := by exact prefixLift 21845
  have htrace : WordTrace (prefixWord ++ tailWord_21845) baseStart_21845 baseEnd_21845 := by
    simpa [prefixWord, tailWord_21845, baseEnd_21845] using wordTrace_append hprefix tailTrace_21845
  have hstable : (prefixWord ++ tailWord_21845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21845).length < 2 ^ (prefixWord ++ tailWord_21845).sum := by decide
  have hdescent : baseEnd_21845 < baseStart_21845 := by decide
  rcases family_descends (prefixWord ++ tailWord_21845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21861 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 2, 3, 3]
def baseStart_21861 : Nat := 118140960795 + 21861 * 2 ^ 59
def prefixEnd_21861 : Nat := 4983230072969 + 3 ^ 40 * 21861 * 2
def baseEnd_21861 : Nat := 11225200588044202436969

theorem tailTrace_21861 : CollatzResearch.WordTrace tailWord_21861 prefixEnd_21861 11225200588044202436969 := by
  unfold tailWord_21861
  simp only [CollatzResearch.WordTrace]
  refine ⟨797336173808805406665437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 531557449205870271110291 797336173808805406665437)
  ·
    refine ⟨299001065178302027499539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 797336173808805406665437 299001065178302027499539)
    ·
      refine ⟨448501597767453041249309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299001065178302027499539 448501597767453041249309)
      ·
        refine ⟨168188099162794890468491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448501597767453041249309 168188099162794890468491)
        ·
          refine ⟨252282148744192335702737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168188099162794890468491 252282148744192335702737)
          ·
            refine ⟨189211611558144251777053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252282148744192335702737 189211611558144251777053)
            ·
              refine ⟨70954354334304094416395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189211611558144251777053 70954354334304094416395)
              ·
                refine ⟨106431531501456141624593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70954354334304094416395 106431531501456141624593)
                ·
                  refine ⟨79823648626092106218445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106431531501456141624593 79823648626092106218445)
                  ·
                    refine ⟨29933868234784539831917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79823648626092106218445 29933868234784539831917)
                    ·
                      refine ⟨11225200588044202436969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 29933868234784539831917 11225200588044202436969)
                      ·
                        rfl

theorem cell23_21861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_21861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21861 prefixEnd_21861 := by exact prefixLift 21861
  have htrace : WordTrace (prefixWord ++ tailWord_21861) baseStart_21861 baseEnd_21861 := by
    simpa [prefixWord, tailWord_21861, baseEnd_21861] using wordTrace_append hprefix tailTrace_21861
  have hstable : (prefixWord ++ tailWord_21861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21861).length < 2 ^ (prefixWord ++ tailWord_21861).sum := by decide
  have hdescent : baseEnd_21861 < baseStart_21861 := by decide
  rcases family_descends (prefixWord ++ tailWord_21861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21871 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 2, 5, 2]
def baseStart_21871 : Nat := 118140960795 + 21871 * 2 ^ 59
def prefixEnd_21871 : Nat := 4983230072969 + 3 ^ 40 * 21871 * 2
def baseEnd_21871 : Nat := 11230335394589163311923

theorem tailTrace_21871 : CollatzResearch.WordTrace tailWord_21871 prefixEnd_21871 11230335394589163311923 := by
  unfold tailWord_21871
  simp only [CollatzResearch.WordTrace]
  refine ⟨797700903772577114529467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 531800602515051409686311 797700903772577114529467)
  ·
    refine ⟨1196551355658865671794201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 797700903772577114529467 1196551355658865671794201)
    ·
      refine ⟨897413516744149253845651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1196551355658865671794201 897413516744149253845651)
      ·
        refine ⟨1346120275116223880768477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897413516744149253845651 1346120275116223880768477)
        ·
          refine ⟨504795103168583955288179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1346120275116223880768477 504795103168583955288179)
          ·
            refine ⟨757192654752875932932269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504795103168583955288179 757192654752875932932269)
            ·
              refine ⟨283947245532328474849601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 757192654752875932932269 283947245532328474849601)
              ·
                refine ⟨212960434149246356137201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283947245532328474849601 212960434149246356137201)
                ·
                  refine ⟨159720325611934767102901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212960434149246356137201 159720325611934767102901)
                  ·
                    refine ⟨14973780526118884415897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 159720325611934767102901 14973780526118884415897)
                    ·
                      refine ⟨11230335394589163311923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 14973780526118884415897 11230335394589163311923)
                      ·
                        rfl

theorem cell23_21871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 5, 2].length) (baseStart_21871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21871 prefixEnd_21871 := by exact prefixLift 21871
  have htrace : WordTrace (prefixWord ++ tailWord_21871) baseStart_21871 baseEnd_21871 := by
    simpa [prefixWord, tailWord_21871, baseEnd_21871] using wordTrace_append hprefix tailTrace_21871
  have hstable : (prefixWord ++ tailWord_21871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21871).length < 2 ^ (prefixWord ++ tailWord_21871).sum := by decide
  have hdescent : baseEnd_21871 < baseStart_21871 := by decide
  rcases family_descends (prefixWord ++ tailWord_21871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21881 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 2, 5]
def baseStart_21881 : Nat := 118140960795 + 21881 * 2 ^ 59
def prefixEnd_21881 : Nat := 4983230072969 + 3 ^ 40 * 21881 * 2
def baseEnd_21881 : Nat := 3745156733711374728959

theorem tailTrace_21881 : CollatzResearch.WordTrace tailWord_21881 prefixEnd_21881 3745156733711374728959 := by
  unfold tailWord_21881
  simp only [CollatzResearch.WordTrace]
  refine ⟨798065633736348822393497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 532043755824232548262331 798065633736348822393497)
  ·
    refine ⟨598549225302261616795123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 798065633736348822393497 598549225302261616795123)
    ·
      refine ⟨897823837953392425192685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598549225302261616795123 897823837953392425192685)
      ·
        refine ⟨336683939232522159447257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 897823837953392425192685 336683939232522159447257)
        ·
          refine ⟨252512954424391619585443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336683939232522159447257 252512954424391619585443)
          ·
            refine ⟨378769431636587429378165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252512954424391619585443 378769431636587429378165)
            ·
              refine ⟨35509634215930071504203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 378769431636587429378165 35509634215930071504203)
              ·
                refine ⟨53264451323895107256305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35509634215930071504203 53264451323895107256305)
                ·
                  refine ⟨39948338492921330442229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53264451323895107256305 39948338492921330442229)
                  ·
                    refine ⟨3745156733711374728959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39948338492921330442229 3745156733711374728959)
                    ·
                      rfl

theorem cell23_21881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 5].length) (baseStart_21881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21881 prefixEnd_21881 := by exact prefixLift 21881
  have htrace : WordTrace (prefixWord ++ tailWord_21881) baseStart_21881 baseEnd_21881 := by
    simpa [prefixWord, tailWord_21881, baseEnd_21881] using wordTrace_append hprefix tailTrace_21881
  have hstable : (prefixWord ++ tailWord_21881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21881).length < 2 ^ (prefixWord ++ tailWord_21881).sum := by decide
  have hdescent : baseEnd_21881 < baseStart_21881 := by decide
  rcases family_descends (prefixWord ++ tailWord_21881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21941 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 8]
def baseStart_21941 : Nat := 118140960795 + 21941 * 2 ^ 59
def prefixEnd_21941 : Nat := 4983230072969 + 3 ^ 40 * 21941 * 2
def baseEnd_21941 : Nat := 1251808782267098826289

theorem tailTrace_21941 : CollatzResearch.WordTrace tailWord_21941 prefixEnd_21941 1251808782267098826289 := by
  unfold tailWord_21941
  simp only [CollatzResearch.WordTrace]
  refine ⟨800254013518979069577677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 533502675679319379718451 800254013518979069577677)
  ·
    refine ⟨300095255069617151091629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 800254013518979069577677 300095255069617151091629)
    ·
      refine ⟨112535720651106431659361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300095255069617151091629 112535720651106431659361)
      ·
        refine ⟨84401790488329823744521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112535720651106431659361 84401790488329823744521)
        ·
          refine ⟨63301342866247367808391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84401790488329823744521 63301342866247367808391)
          ·
            refine ⟨94952014299371051712587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63301342866247367808391 94952014299371051712587)
            ·
              refine ⟨142428021449056577568881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94952014299371051712587 142428021449056577568881)
              ·
                refine ⟨106821016086792433176661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142428021449056577568881 106821016086792433176661)
                ·
                  refine ⟨1251808782267098826289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 106821016086792433176661 1251808782267098826289)
                  ·
                    rfl

theorem cell23_21941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_21941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21941 prefixEnd_21941 := by exact prefixLift 21941
  have htrace : WordTrace (prefixWord ++ tailWord_21941) baseStart_21941 baseEnd_21941 := by
    simpa [prefixWord, tailWord_21941, baseEnd_21941] using wordTrace_append hprefix tailTrace_21941
  have hstable : (prefixWord ++ tailWord_21941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21941).length < 2 ^ (prefixWord ++ tailWord_21941).sum := by decide
  have hdescent : baseEnd_21941 < baseStart_21941 := by decide
  rcases family_descends (prefixWord ++ tailWord_21941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21962 : List Nat := [3, 1, 2, 1, 2, 4, 3, 2, 1, 4]
def baseStart_21962 : Nat := 118140960795 + 21962 * 2 ^ 59
def prefixEnd_21962 : Nat := 4983230072969 + 3 ^ 40 * 21962 * 2
def baseEnd_21962 : Nat := 3759020711382769091335

theorem tailTrace_21962 : CollatzResearch.WordTrace tailWord_21962 prefixEnd_21962 3759020711382769091335 := by
  unfold tailWord_21962
  simp only [CollatzResearch.WordTrace]
  refine ⟨200254986610724914023035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 534013297628599770728093 200254986610724914023035)
  ·
    refine ⟨300382479916087371034553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200254986610724914023035 300382479916087371034553)
    ·
      refine ⟨225286859937065528275915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300382479916087371034553 225286859937065528275915)
      ·
        refine ⟨337930289905598292413873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225286859937065528275915 337930289905598292413873)
        ·
          refine ⟨253447717429198719310405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337930289905598292413873 253447717429198719310405)
          ·
            refine ⟨47521447017974759870701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253447717429198719310405 47521447017974759870701)
            ·
              refine ⟨17820542631740534951513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47521447017974759870701 17820542631740534951513)
              ·
                refine ⟨13365406973805401213635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17820542631740534951513 13365406973805401213635)
                ·
                  refine ⟨20048110460708101820453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13365406973805401213635 20048110460708101820453)
                  ·
                    refine ⟨3759020711382769091335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20048110460708101820453 3759020711382769091335)
                    ·
                      rfl

theorem cell23_21962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_21962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_21962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_21962 prefixEnd_21962 := by exact prefixLift 21962
  have htrace : WordTrace (prefixWord ++ tailWord_21962) baseStart_21962 baseEnd_21962 := by
    simpa [prefixWord, tailWord_21962, baseEnd_21962] using wordTrace_append hprefix tailTrace_21962
  have hstable : (prefixWord ++ tailWord_21962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21962).length < 2 ^ (prefixWord ++ tailWord_21962).sum := by decide
  have hdescent : baseEnd_21962 < baseStart_21962 := by decide
  rcases family_descends (prefixWord ++ tailWord_21962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22001 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 3, 6]
def baseStart_22001 : Nat := 118140960795 + 22001 * 2 ^ 59
def prefixEnd_22001 : Nat := 4983230072969 + 3 ^ 40 * 22001 * 2
def baseEnd_22001 : Nat := 3765695959891218228775

theorem tailTrace_22001 : CollatzResearch.WordTrace tailWord_22001 prefixEnd_22001 3765695959891218228775 := by
  unfold tailWord_22001
  simp only [CollatzResearch.WordTrace]
  refine ⟨802442393301609316761857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 534961595534406211174571 802442393301609316761857)
  ·
    refine ⟨601831794976206987571393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 802442393301609316761857 601831794976206987571393)
    ·
      refine ⟨451373846232155240678545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 601831794976206987571393 451373846232155240678545)
      ·
        refine ⟨338530384674116430508909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451373846232155240678545 338530384674116430508909)
        ·
          refine ⟨126948894252793661440841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338530384674116430508909 126948894252793661440841)
          ·
            refine ⟨95211670689595246080631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126948894252793661440841 95211670689595246080631)
            ·
              refine ⟨142817506034392869120947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95211670689595246080631 142817506034392869120947)
              ·
                refine ⟨214226259051589303681421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142817506034392869120947 214226259051589303681421)
                ·
                  refine ⟨80334847144345988880533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214226259051589303681421 80334847144345988880533)
                  ·
                    refine ⟨3765695959891218228775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80334847144345988880533 3765695959891218228775)
                    ·
                      rfl

theorem cell23_22001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_22001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22001 prefixEnd_22001 := by exact prefixLift 22001
  have htrace : WordTrace (prefixWord ++ tailWord_22001) baseStart_22001 baseEnd_22001 := by
    simpa [prefixWord, tailWord_22001, baseEnd_22001] using wordTrace_append hprefix tailTrace_22001
  have hstable : (prefixWord ++ tailWord_22001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22001).length < 2 ^ (prefixWord ++ tailWord_22001).sum := by decide
  have hdescent : baseEnd_22001 < baseStart_22001 := by decide
  rcases family_descends (prefixWord ++ tailWord_22001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22021 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_22021 : Nat := 118140960795 + 22021 * 2 ^ 59
def prefixEnd_22021 : Nat := 4983230072969 + 3 ^ 40 * 22021 * 2
def baseEnd_22021 : Nat := 11307357492763576436233

theorem tailTrace_22021 : CollatzResearch.WordTrace tailWord_22021 prefixEnd_22021 11307357492763576436233 := by
  unfold tailWord_22021
  simp only [CollatzResearch.WordTrace]
  refine ⟨803171853229152732489917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 535447902152768488326611 803171853229152732489917)
  ·
    refine ⟨301189444960932274683719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 803171853229152732489917 301189444960932274683719)
    ·
      refine ⟨451784167441398412025579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301189444960932274683719 451784167441398412025579)
      ·
        refine ⟨677676251162097618038369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451784167441398412025579 677676251162097618038369)
        ·
          refine ⟨508257188371573213528777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677676251162097618038369 508257188371573213528777)
          ·
            refine ⟨381192891278679910146583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508257188371573213528777 381192891278679910146583)
            ·
              refine ⟨571789336918019865219875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381192891278679910146583 571789336918019865219875)
              ·
                refine ⟨857684005377029797829813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571789336918019865219875 857684005377029797829813)
                ·
                  refine ⟨80407875504096543546545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 857684005377029797829813 80407875504096543546545)
                  ·
                    refine ⟨60305906628072407659909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80407875504096543546545 60305906628072407659909)
                    ·
                      refine ⟨11307357492763576436233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 60305906628072407659909 11307357492763576436233)
                      ·
                        rfl

theorem cell23_22021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_22021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22021 prefixEnd_22021 := by exact prefixLift 22021
  have htrace : WordTrace (prefixWord ++ tailWord_22021) baseStart_22021 baseEnd_22021 := by
    simpa [prefixWord, tailWord_22021, baseEnd_22021] using wordTrace_append hprefix tailTrace_22021
  have hstable : (prefixWord ++ tailWord_22021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22021).length < 2 ^ (prefixWord ++ tailWord_22021).sum := by decide
  have hdescent : baseEnd_22021 < baseStart_22021 := by decide
  rcases family_descends (prefixWord ++ tailWord_22021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22025 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 3, 2, 2]
def baseStart_22025 : Nat := 118140960795 + 22025 * 2 ^ 59
def prefixEnd_22025 : Nat := 4983230072969 + 3 ^ 40 * 22025 * 2
def baseEnd_22025 : Nat := 11309411415381560786215

theorem tailTrace_22025 : CollatzResearch.WordTrace tailWord_22025 prefixEnd_22025 11309411415381560786215 := by
  unfold tailWord_22025
  simp only [CollatzResearch.WordTrace]
  refine ⟨803317745214661415635529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 535545163476440943757019 803317745214661415635529)
  ·
    refine ⟨602488308910996061726647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 803317745214661415635529 602488308910996061726647)
    ·
      refine ⟨903732463366494092589971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 602488308910996061726647 903732463366494092589971)
      ·
        refine ⟨1355598695049741138884957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903732463366494092589971 1355598695049741138884957)
        ·
          refine ⟨508349510643652927081859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1355598695049741138884957 508349510643652927081859)
          ·
            refine ⟨762524265965479390622789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508349510643652927081859 762524265965479390622789)
            ·
              refine ⟨142973299868527385741773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 762524265965479390622789 142973299868527385741773)
              ·
                refine ⟨53614987450697769653165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142973299868527385741773 53614987450697769653165)
                ·
                  refine ⟨20105620294011663619937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53614987450697769653165 20105620294011663619937)
                  ·
                    refine ⟨15079215220508747714953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20105620294011663619937 15079215220508747714953)
                    ·
                      refine ⟨11309411415381560786215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15079215220508747714953 11309411415381560786215)
                      ·
                        rfl

theorem cell23_22025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 2, 2].length) (baseStart_22025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22025 prefixEnd_22025 := by exact prefixLift 22025
  have htrace : WordTrace (prefixWord ++ tailWord_22025) baseStart_22025 baseEnd_22025 := by
    simpa [prefixWord, tailWord_22025, baseEnd_22025] using wordTrace_append hprefix tailTrace_22025
  have hstable : (prefixWord ++ tailWord_22025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22025).length < 2 ^ (prefixWord ++ tailWord_22025).sum := by decide
  have hdescent : baseEnd_22025 < baseStart_22025 := by decide
  rcases family_descends (prefixWord ++ tailWord_22025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22045 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_22045 : Nat := 118140960795 + 22045 * 2 ^ 59
def prefixEnd_22045 : Nat := 4983230072969 + 3 ^ 40 * 22045 * 2
def baseEnd_22045 : Nat := 11319681028471482536123

theorem tailTrace_22045 : CollatzResearch.WordTrace tailWord_22045 prefixEnd_22045 11319681028471482536123 := by
  unfold tailWord_22045
  simp only [CollatzResearch.WordTrace]
  refine ⟨804047205142204831363589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 536031470094803220909059 804047205142204831363589)
  ·
    refine ⟨150758850964163405880673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 804047205142204831363589 150758850964163405880673)
    ·
      refine ⟨113069138223122554410505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150758850964163405880673 113069138223122554410505)
      ·
        refine ⟨84801853667341915807879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113069138223122554410505 84801853667341915807879)
        ·
          refine ⟨127202780501012873711819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84801853667341915807879 127202780501012873711819)
          ·
            refine ⟨190804170751519310567729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127202780501012873711819 190804170751519310567729)
            ·
              refine ⟨143103128063639482925797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190804170751519310567729 143103128063639482925797)
              ·
                refine ⟨26831836511932403048587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143103128063639482925797 26831836511932403048587)
                ·
                  refine ⟨40247754767898604572881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26831836511932403048587 40247754767898604572881)
                  ·
                    refine ⟨30185816075923953429661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40247754767898604572881 30185816075923953429661)
                    ·
                      refine ⟨11319681028471482536123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 30185816075923953429661 11319681028471482536123)
                      ·
                        rfl

theorem cell23_22045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_22045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22045 prefixEnd_22045 := by exact prefixLift 22045
  have htrace : WordTrace (prefixWord ++ tailWord_22045) baseStart_22045 baseEnd_22045 := by
    simpa [prefixWord, tailWord_22045, baseEnd_22045] using wordTrace_append hprefix tailTrace_22045
  have hstable : (prefixWord ++ tailWord_22045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22045).length < 2 ^ (prefixWord ++ tailWord_22045).sum := by decide
  have hdescent : baseEnd_22045 < baseStart_22045 := by decide
  rcases family_descends (prefixWord ++ tailWord_22045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22046 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_22046 : Nat := 118140960795 + 22046 * 2 ^ 59
def prefixEnd_22046 : Nat := 4983230072969 + 3 ^ 40 * 22046 * 2
def baseEnd_22046 : Nat := 11320194509125978623619

theorem tailTrace_22046 : CollatzResearch.WordTrace tailWord_22046 prefixEnd_22046 11320194509125978623619 := by
  unfold tailWord_22046
  simp only [CollatzResearch.WordTrace]
  refine ⟨100510459767322750268749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 536055785425721334766661 100510459767322750268749)
  ·
    refine ⟨37691422412746031350781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100510459767322750268749 37691422412746031350781)
    ·
      refine ⟨14134283404779761756543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37691422412746031350781 14134283404779761756543)
      ·
        refine ⟨21201425107169642634815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14134283404779761756543 21201425107169642634815)
        ·
          refine ⟨31802137660754463952223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21201425107169642634815 31802137660754463952223)
          ·
            refine ⟨47703206491131695928335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31802137660754463952223 47703206491131695928335)
            ·
              refine ⟨71554809736697543892503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47703206491131695928335 71554809736697543892503)
              ·
                refine ⟨107332214605046315838755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71554809736697543892503 107332214605046315838755)
                ·
                  refine ⟨160998321907569473758133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107332214605046315838755 160998321907569473758133)
                  ·
                    refine ⟨15093592678834638164825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 160998321907569473758133 15093592678834638164825)
                    ·
                      refine ⟨11320194509125978623619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15093592678834638164825 11320194509125978623619)
                      ·
                        rfl

theorem cell23_22046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_22046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22046 prefixEnd_22046 := by exact prefixLift 22046
  have htrace : WordTrace (prefixWord ++ tailWord_22046) baseStart_22046 baseEnd_22046 := by
    simpa [prefixWord, tailWord_22046, baseEnd_22046] using wordTrace_append hprefix tailTrace_22046
  have hstable : (prefixWord ++ tailWord_22046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22046).length < 2 ^ (prefixWord ++ tailWord_22046).sum := by decide
  have hdescent : baseEnd_22046 < baseStart_22046 := by decide
  rcases family_descends (prefixWord ++ tailWord_22046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22062 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_22062 : Nat := 118140960795 + 22062 * 2 ^ 59
def prefixEnd_22062 : Nat := 4983230072969 + 3 ^ 40 * 22062 * 2
def baseEnd_22062 : Nat := 11328410199597916023545

theorem tailTrace_22062 : CollatzResearch.WordTrace tailWord_22062 prefixEnd_22062 11328410199597916023545 := by
  unfold tailWord_22062
  simp only [CollatzResearch.WordTrace]
  refine ⟨100583405760077091841555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 536444830720411156488293 100583405760077091841555)
  ·
    refine ⟨150875108640115637762333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100583405760077091841555 150875108640115637762333)
    ·
      refine ⟨56578165740043364160875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150875108640115637762333 56578165740043364160875)
      ·
        refine ⟨84867248610065046241313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56578165740043364160875 84867248610065046241313)
        ·
          refine ⟨63650436457548784680985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84867248610065046241313 63650436457548784680985)
          ·
            refine ⟨47737827343161588510739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63650436457548784680985 47737827343161588510739)
            ·
              refine ⟨71606741014742382766109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47737827343161588510739 71606741014742382766109)
              ·
                refine ⟨26852527880528393537291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71606741014742382766109 26852527880528393537291)
                ·
                  refine ⟨40278791820792590305937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26852527880528393537291 40278791820792590305937)
                  ·
                    refine ⟨30209093865594442729453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40278791820792590305937 30209093865594442729453)
                    ·
                      refine ⟨11328410199597916023545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 30209093865594442729453 11328410199597916023545)
                      ·
                        rfl

theorem cell23_22062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_22062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22062 prefixEnd_22062 := by exact prefixLift 22062
  have htrace : WordTrace (prefixWord ++ tailWord_22062) baseStart_22062 baseEnd_22062 := by
    simpa [prefixWord, tailWord_22062, baseEnd_22062] using wordTrace_append hprefix tailTrace_22062
  have hstable : (prefixWord ++ tailWord_22062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22062).length < 2 ^ (prefixWord ++ tailWord_22062).sum := by decide
  have hdescent : baseEnd_22062 < baseStart_22062 := by decide
  rcases family_descends (prefixWord ++ tailWord_22062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22086 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_22086 : Nat := 118140960795 + 22086 * 2 ^ 59
def prefixEnd_22086 : Nat := 4983230072969 + 3 ^ 40 * 22086 * 2
def baseEnd_22086 : Nat := 3780244578435274041145

theorem tailTrace_22086 : CollatzResearch.WordTrace tailWord_22086 prefixEnd_22086 3780244578435274041145 := by
  unfold tailWord_22086
  simp only [CollatzResearch.WordTrace]
  refine ⟨25173206187302151050191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 537028398662445889070741 25173206187302151050191)
  ·
    refine ⟨37759809280953226575287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25173206187302151050191 37759809280953226575287)
    ·
      refine ⟨56639713921429839862931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37759809280953226575287 56639713921429839862931)
      ·
        refine ⟨84959570882144759794397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56639713921429839862931 84959570882144759794397)
        ·
          refine ⟨31859839080804284922899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84959570882144759794397 31859839080804284922899)
          ·
            refine ⟨47789758621206427384349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31859839080804284922899 47789758621206427384349)
            ·
              refine ⟨17921159482952410269131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47789758621206427384349 17921159482952410269131)
              ·
                refine ⟨26881739224428615403697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17921159482952410269131 26881739224428615403697)
                ·
                  refine ⟨20161304418321461552773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26881739224428615403697 20161304418321461552773)
                  ·
                    refine ⟨3780244578435274041145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20161304418321461552773 3780244578435274041145)
                    ·
                      rfl

theorem cell23_22086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_22086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22086 prefixEnd_22086 := by exact prefixLift 22086
  have htrace : WordTrace (prefixWord ++ tailWord_22086) baseStart_22086 baseEnd_22086 := by
    simpa [prefixWord, tailWord_22086, baseEnd_22086] using wordTrace_append hprefix tailTrace_22086
  have hstable : (prefixWord ++ tailWord_22086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22086).length < 2 ^ (prefixWord ++ tailWord_22086).sum := by decide
  have hdescent : baseEnd_22086 < baseStart_22086 := by decide
  rcases family_descends (prefixWord ++ tailWord_22086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22121 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 9]
def baseStart_22121 : Nat := 118140960795 + 22121 * 2 ^ 59
def prefixEnd_22121 : Nat := 4983230072969 + 3 ^ 40 * 22121 * 2
def baseEnd_22121 : Nat := 1262078395357020576197

theorem tailTrace_22121 : CollatzResearch.WordTrace tailWord_22121 prefixEnd_22121 1262078395357020576197 := by
  unfold tailWord_22121
  simp only [CollatzResearch.WordTrace]
  refine ⟨806819152866869811130217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 537879435244579874086811 806819152866869811130217)
  ·
    refine ⟨605114364650152358347663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 806819152866869811130217 605114364650152358347663)
    ·
      refine ⟨907671546975228537521495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605114364650152358347663 907671546975228537521495)
      ·
        refine ⟨1361507320462842806282243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907671546975228537521495 1361507320462842806282243)
        ·
          refine ⟨2042260980694264209423365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361507320462842806282243 2042260980694264209423365)
          ·
            refine ⟨382923933880174539266881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2042260980694264209423365 382923933880174539266881)
            ·
              refine ⟨287192950410130904450161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382923933880174539266881 287192950410130904450161)
              ·
                refine ⟨215394712807598178337621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287192950410130904450161 215394712807598178337621)
                ·
                  refine ⟨1262078395357020576197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 215394712807598178337621 1262078395357020576197)
                  ·
                    rfl

theorem cell23_22121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 9].length) (baseStart_22121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22121 prefixEnd_22121 := by exact prefixLift 22121
  have htrace : WordTrace (prefixWord ++ tailWord_22121) baseStart_22121 baseEnd_22121 := by
    simpa [prefixWord, tailWord_22121, baseEnd_22121] using wordTrace_append hprefix tailTrace_22121
  have hstable : (prefixWord ++ tailWord_22121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22121).length < 2 ^ (prefixWord ++ tailWord_22121).sum := by decide
  have hdescent : baseEnd_22121 < baseStart_22121 := by decide
  rcases family_descends (prefixWord ++ tailWord_22121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22215 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 3, 4]
def baseStart_22215 : Nat := 118140960795 + 22215 * 2 ^ 59
def prefixEnd_22215 : Nat := 4983230072969 + 3 ^ 40 * 22215 * 2
def baseEnd_22215 : Nat := 3802324246578605803447

theorem tailTrace_22215 : CollatzResearch.WordTrace tailWord_22215 prefixEnd_22215 3802324246578605803447 := by
  unfold tailWord_22215
  simp only [CollatzResearch.WordTrace]
  refine ⟨810247614526323865052099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 540165076350882576701399 810247614526323865052099)
  ·
    refine ⟨1215371421789485797578149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810247614526323865052099 1215371421789485797578149)
    ·
      refine ⟨227882141585528587045903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1215371421789485797578149 227882141585528587045903)
      ·
        refine ⟨341823212378292880568855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227882141585528587045903 341823212378292880568855)
        ·
          refine ⟨512734818567439320853283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341823212378292880568855 512734818567439320853283)
          ·
            refine ⟨769102227851158981279925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512734818567439320853283 769102227851158981279925)
            ·
              refine ⟨72103333861046154494993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 769102227851158981279925 72103333861046154494993)
              ·
                refine ⟨54077500395784615871245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72103333861046154494993 54077500395784615871245)
                ·
                  refine ⟨20279062648419230951717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54077500395784615871245 20279062648419230951717)
                  ·
                    refine ⟨3802324246578605803447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20279062648419230951717 3802324246578605803447)
                    ·
                      rfl

theorem cell23_22215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_22215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22215 prefixEnd_22215 := by exact prefixLift 22215
  have htrace : WordTrace (prefixWord ++ tailWord_22215) baseStart_22215 baseEnd_22215 := by
    simpa [prefixWord, tailWord_22215, baseEnd_22215] using wordTrace_append hprefix tailTrace_22215
  have hstable : (prefixWord ++ tailWord_22215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22215).length < 2 ^ (prefixWord ++ tailWord_22215).sum := by decide
  have hdescent : baseEnd_22215 < baseStart_22215 := by decide
  rcases family_descends (prefixWord ++ tailWord_22215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22225 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 1, 4, 3]
def baseStart_22225 : Nat := 118140960795 + 22225 * 2 ^ 59
def prefixEnd_22225 : Nat := 4983230072969 + 3 ^ 40 * 22225 * 2
def baseEnd_22225 : Nat := 11412107546280778285295

theorem tailTrace_22225 : CollatzResearch.WordTrace tailWord_22225 prefixEnd_22225 11412107546280778285295 := by
  unfold tailWord_22225
  simp only [CollatzResearch.WordTrace]
  refine ⟨810612344490095572916129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 540408229660063715277419 810612344490095572916129)
  ·
    refine ⟨607959258367571679687097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 810612344490095572916129 607959258367571679687097)
    ·
      refine ⟨455969443775678759765323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 607959258367571679687097 455969443775678759765323)
      ·
        refine ⟨683954165663518139647985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455969443775678759765323 683954165663518139647985)
        ·
          refine ⟨512965624247638604735989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683954165663518139647985 512965624247638604735989)
          ·
            refine ⟨48090527273216119193999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 512965624247638604735989 48090527273216119193999)
            ·
              refine ⟨72135790909824178790999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48090527273216119193999 72135790909824178790999)
              ·
                refine ⟨108203686364736268186499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72135790909824178790999 108203686364736268186499)
                ·
                  refine ⟨162305529547104402279749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108203686364736268186499 162305529547104402279749)
                  ·
                    refine ⟨30432286790082075427453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162305529547104402279749 30432286790082075427453)
                    ·
                      refine ⟨11412107546280778285295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 30432286790082075427453 11412107546280778285295)
                      ·
                        rfl

theorem cell23_22225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_22225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22225 prefixEnd_22225 := by exact prefixLift 22225
  have htrace : WordTrace (prefixWord ++ tailWord_22225) baseStart_22225 baseEnd_22225 := by
    simpa [prefixWord, tailWord_22225, baseEnd_22225] using wordTrace_append hprefix tailTrace_22225
  have hstable : (prefixWord ++ tailWord_22225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22225).length < 2 ^ (prefixWord ++ tailWord_22225).sum := by decide
  have hdescent : baseEnd_22225 < baseStart_22225 := by decide
  rcases family_descends (prefixWord ++ tailWord_22225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22275 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 1, 5]
def baseStart_22275 : Nat := 118140960795 + 22275 * 2 ^ 59
def prefixEnd_22275 : Nat := 4983230072969 + 3 ^ 40 * 22275 * 2
def baseEnd_22275 : Nat := 3812593859668527553355

theorem tailTrace_22275 : CollatzResearch.WordTrace tailWord_22275 prefixEnd_22275 3812593859668527553355 := by
  unfold tailWord_22275
  simp only [CollatzResearch.WordTrace]
  refine ⟨812435994308954112236279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 541623996205969408157519 812435994308954112236279)
  ·
    refine ⟨1218653991463431168354419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 812435994308954112236279 1218653991463431168354419)
    ·
      refine ⟨1827980987195146752531629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218653991463431168354419 1827980987195146752531629)
      ·
        refine ⟨685492870198180032199361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1827980987195146752531629 685492870198180032199361)
        ·
          refine ⟨514119652648635024149521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685492870198180032199361 514119652648635024149521)
          ·
            refine ⟨385589739486476268112141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514119652648635024149521 385589739486476268112141)
            ·
              refine ⟨144596152307428600542053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 385589739486476268112141 144596152307428600542053)
              ·
                refine ⟨27111778557642862601635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144596152307428600542053 27111778557642862601635)
                ·
                  refine ⟨40667667836464293902453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27111778557642862601635 40667667836464293902453)
                  ·
                    refine ⟨3812593859668527553355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40667667836464293902453 3812593859668527553355)
                    ·
                      rfl

theorem cell23_22275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 5].length) (baseStart_22275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22275 prefixEnd_22275 := by exact prefixLift 22275
  have htrace : WordTrace (prefixWord ++ tailWord_22275) baseStart_22275 baseEnd_22275 := by
    simpa [prefixWord, tailWord_22275, baseEnd_22275] using wordTrace_append hprefix tailTrace_22275
  have hstable : (prefixWord ++ tailWord_22275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22275).length < 2 ^ (prefixWord ++ tailWord_22275).sum := by decide
  have hdescent : baseEnd_22275 < baseStart_22275 := by decide
  rcases family_descends (prefixWord ++ tailWord_22275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22282 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2]
def baseStart_22282 : Nat := 118140960795 + 22282 * 2 ^ 59
def prefixEnd_22282 : Nat := 4983230072969 + 3 ^ 40 * 22282 * 2
def baseEnd_22282 : Nat := 11441375943587055272533

theorem tailTrace_22282 : CollatzResearch.WordTrace tailWord_22282 prefixEnd_22282 11441375943587055272533 := by
  unfold tailWord_22282
  simp only [CollatzResearch.WordTrace]
  refine ⟨203172826320898576935275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 541794203522396205160733 203172826320898576935275)
  ·
    refine ⟨304759239481347865402913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203172826320898576935275 304759239481347865402913)
    ·
      refine ⟨228569429611010899052185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304759239481347865402913 228569429611010899052185)
      ·
        refine ⟨171427072208258174289139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228569429611010899052185 171427072208258174289139)
        ·
          refine ⟨257140608312387261433709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171427072208258174289139 257140608312387261433709)
          ·
            refine ⟨96427728117145223037641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257140608312387261433709 96427728117145223037641)
            ·
              refine ⟨72320796087858917278231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96427728117145223037641 72320796087858917278231)
              ·
                refine ⟨108481194131788375917347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72320796087858917278231 108481194131788375917347)
                ·
                  refine ⟨162721791197682563876021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108481194131788375917347 162721791197682563876021)
                  ·
                    refine ⟨15255167924782740363377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 162721791197682563876021 15255167924782740363377)
                    ·
                      refine ⟨11441375943587055272533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15255167924782740363377 11441375943587055272533)
                      ·
                        rfl

theorem cell23_22282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_22282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22282 prefixEnd_22282 := by exact prefixLift 22282
  have htrace : WordTrace (prefixWord ++ tailWord_22282) baseStart_22282 baseEnd_22282 := by
    simpa [prefixWord, tailWord_22282, baseEnd_22282] using wordTrace_append hprefix tailTrace_22282
  have hstable : (prefixWord ++ tailWord_22282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22282).length < 2 ^ (prefixWord ++ tailWord_22282).sum := by decide
  have hdescent : baseEnd_22282 < baseStart_22282 := by decide
  rcases family_descends (prefixWord ++ tailWord_22282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22326 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_22326 : Nat := 118140960795 + 22326 * 2 ^ 59
def prefixEnd_22326 : Nat := 4983230072969 + 3 ^ 40 * 22326 * 2
def baseEnd_22326 : Nat := 3821323030794961040777

theorem tailTrace_22326 : CollatzResearch.WordTrace tailWord_22326 prefixEnd_22326 3821323030794961040777 := by
  unfold tailWord_22326
  simp only [CollatzResearch.WordTrace]
  refine ⟨50893507320261863896427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 542864078082793214895221 50893507320261863896427)
  ·
    refine ⟨76340260980392795844641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50893507320261863896427 76340260980392795844641)
    ·
      refine ⟨57255195735294596883481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76340260980392795844641 57255195735294596883481)
      ·
        refine ⟨42941396801470947662611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57255195735294596883481 42941396801470947662611)
        ·
          refine ⟨64412095202206421493917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42941396801470947662611 64412095202206421493917)
          ·
            refine ⟨24154535700827408060219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64412095202206421493917 24154535700827408060219)
            ·
              refine ⟨36231803551241112090329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24154535700827408060219 36231803551241112090329)
              ·
                refine ⟨27173852663430834067747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36231803551241112090329 27173852663430834067747)
                ·
                  refine ⟨40760778995146251101621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27173852663430834067747 40760778995146251101621)
                  ·
                    refine ⟨3821323030794961040777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40760778995146251101621 3821323030794961040777)
                    ·
                      rfl

theorem cell23_22326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_22326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22326 prefixEnd_22326 := by exact prefixLift 22326
  have htrace : WordTrace (prefixWord ++ tailWord_22326) baseStart_22326 baseEnd_22326 := by
    simpa [prefixWord, tailWord_22326, baseEnd_22326] using wordTrace_append hprefix tailTrace_22326
  have hstable : (prefixWord ++ tailWord_22326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22326).length < 2 ^ (prefixWord ++ tailWord_22326).sum := by decide
  have hdescent : baseEnd_22326 < baseStart_22326 := by decide
  rcases family_descends (prefixWord ++ tailWord_22326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22329 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 4]
def baseStart_22329 : Nat := 118140960795 + 22329 * 2 ^ 59
def prefixEnd_22329 : Nat := 4983230072969 + 3 ^ 40 * 22329 * 2
def baseEnd_22329 : Nat := 11465509534348371384817

theorem tailTrace_22329 : CollatzResearch.WordTrace tailWord_22329 prefixEnd_22329 11465509534348371384817 := by
  unfold tailWord_22329
  simp only [CollatzResearch.WordTrace]
  refine ⟨814405536113321334702041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 542937024075547556468027 814405536113321334702041)
  ·
    refine ⟨610804152084991001026531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 814405536113321334702041 610804152084991001026531)
    ·
      refine ⟨916206228127486501539797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610804152084991001026531 916206228127486501539797)
      ·
        refine ⟨21473583471737964879839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 916206228127486501539797 21473583471737964879839)
        ·
          refine ⟨32210375207606947319759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21473583471737964879839 32210375207606947319759)
          ·
            refine ⟨48315562811410420979639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32210375207606947319759 48315562811410420979639)
            ·
              refine ⟨72473344217115631469459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48315562811410420979639 72473344217115631469459)
              ·
                refine ⟨108710016325673447204189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72473344217115631469459 108710016325673447204189)
                ·
                  refine ⟨40766256122127542701571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108710016325673447204189 40766256122127542701571)
                  ·
                    refine ⟨61149384183191314052357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40766256122127542701571 61149384183191314052357)
                    ·
                      refine ⟨11465509534348371384817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 61149384183191314052357 11465509534348371384817)
                      ·
                        rfl

theorem cell23_22329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_22329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22329 prefixEnd_22329 := by exact prefixLift 22329
  have htrace : WordTrace (prefixWord ++ tailWord_22329) baseStart_22329 baseEnd_22329 := by
    simpa [prefixWord, tailWord_22329, baseEnd_22329] using wordTrace_append hprefix tailTrace_22329
  have hstable : (prefixWord ++ tailWord_22329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22329).length < 2 ^ (prefixWord ++ tailWord_22329).sum := by decide
  have hdescent : baseEnd_22329 < baseStart_22329 := by decide
  rcases family_descends (prefixWord ++ tailWord_22329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22346 : List Nat := [3, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2]
def baseStart_22346 : Nat := 118140960795 + 22346 * 2 ^ 59
def prefixEnd_22346 : Nat := 4983230072969 + 3 ^ 40 * 22346 * 2
def baseEnd_22346 : Nat := 11474238705474804872239

theorem tailTrace_22346 : CollatzResearch.WordTrace tailWord_22346 prefixEnd_22346 11474238705474804872239 := by
  unfold tailWord_22346
  simp only [CollatzResearch.WordTrace]
  refine ⟨203756394262933309517723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 543350384701155492047261 203756394262933309517723)
  ·
    refine ⟨305634591394399964276585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203756394262933309517723 305634591394399964276585)
    ·
      refine ⟨229225943545799973207439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305634591394399964276585 229225943545799973207439)
      ·
        refine ⟨343838915318699959811159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229225943545799973207439 343838915318699959811159)
        ·
          refine ⟨515758372978049939716739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343838915318699959811159 515758372978049939716739)
          ·
            refine ⟨773637559467074909575109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515758372978049939716739 773637559467074909575109)
            ·
              refine ⟨145057042400076545545333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 773637559467074909575109 145057042400076545545333)
              ·
                refine ⟨13599097725007176144875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145057042400076545545333 13599097725007176144875)
                ·
                  refine ⟨20398646587510764217313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13599097725007176144875 20398646587510764217313)
                  ·
                    refine ⟨15298984940633073162985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20398646587510764217313 15298984940633073162985)
                    ·
                      refine ⟨11474238705474804872239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15298984940633073162985 11474238705474804872239)
                      ·
                        rfl

theorem cell23_22346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_22346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22346 prefixEnd_22346 := by exact prefixLift 22346
  have htrace : WordTrace (prefixWord ++ tailWord_22346) baseStart_22346 baseEnd_22346 := by
    simpa [prefixWord, tailWord_22346, baseEnd_22346] using wordTrace_append hprefix tailTrace_22346
  have hstable : (prefixWord ++ tailWord_22346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22346).length < 2 ^ (prefixWord ++ tailWord_22346).sum := by decide
  have hdescent : baseEnd_22346 < baseStart_22346 := by decide
  rcases family_descends (prefixWord ++ tailWord_22346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22349 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_22349 : Nat := 118140960795 + 22349 * 2 ^ 59
def prefixEnd_22349 : Nat := 4983230072969 + 3 ^ 40 * 22349 * 2
def baseEnd_22349 : Nat := 11475779147438293134725

theorem tailTrace_22349 : CollatzResearch.WordTrace tailWord_22349 prefixEnd_22349 11475779147438293134725 := by
  unfold tailWord_22349
  simp only [CollatzResearch.WordTrace]
  refine ⟨815134996040864750430101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 543423330693909833620067 815134996040864750430101)
  ·
    refine ⟨38209452939415535176411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 815134996040864750430101 38209452939415535176411)
    ·
      refine ⟨57314179409123302764617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38209452939415535176411 57314179409123302764617)
      ·
        refine ⟨42985634556842477073463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57314179409123302764617 42985634556842477073463)
        ·
          refine ⟨64478451835263715610195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42985634556842477073463 64478451835263715610195)
          ·
            refine ⟨96717677752895573415293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64478451835263715610195 96717677752895573415293)
            ·
              refine ⟨36269129157335840030735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96717677752895573415293 36269129157335840030735)
              ·
                refine ⟨54403693736003760046103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36269129157335840030735 54403693736003760046103)
                ·
                  refine ⟨81605540604005640069155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54403693736003760046103 81605540604005640069155)
                  ·
                    refine ⟨122408310906008460103733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81605540604005640069155 122408310906008460103733)
                    ·
                      refine ⟨11475779147438293134725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 122408310906008460103733 11475779147438293134725)
                      ·
                        rfl

theorem cell23_22349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_22349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22349 prefixEnd_22349 := by exact prefixLift 22349
  have htrace : WordTrace (prefixWord ++ tailWord_22349) baseStart_22349 baseEnd_22349 := by
    simpa [prefixWord, tailWord_22349, baseEnd_22349] using wordTrace_append hprefix tailTrace_22349
  have hstable : (prefixWord ++ tailWord_22349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22349).length < 2 ^ (prefixWord ++ tailWord_22349).sum := by decide
  have hdescent : baseEnd_22349 < baseStart_22349 := by decide
  rcases family_descends (prefixWord ++ tailWord_22349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22385 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_22385 : Nat := 118140960795 + 22385 * 2 ^ 59
def prefixEnd_22385 : Nat := 4983230072969 + 3 ^ 40 * 22385 * 2
def baseEnd_22385 : Nat := 11494264451000152284559

theorem tailTrace_22385 : CollatzResearch.WordTrace tailWord_22385 prefixEnd_22385 11494264451000152284559 := by
  unfold tailWord_22385
  simp only [CollatzResearch.WordTrace]
  refine ⟨816448023910442898740609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 544298682606961932493739 816448023910442898740609)
  ·
    refine ⟨612336017932832174055457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 816448023910442898740609 612336017932832174055457)
    ·
      refine ⟨459252013449624130541593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 612336017932832174055457 459252013449624130541593)
      ·
        refine ⟨344439010087218097906195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459252013449624130541593 344439010087218097906195)
        ·
          refine ⟨516658515130827146859293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344439010087218097906195 516658515130827146859293)
          ·
            refine ⟨193746943174060180072235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 516658515130827146859293 193746943174060180072235)
            ·
              refine ⟨290620414761090270108353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193746943174060180072235 290620414761090270108353)
              ·
                refine ⟨217965311070817702581265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290620414761090270108353 217965311070817702581265)
                ·
                  refine ⟨163473983303113276935949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217965311070817702581265 163473983303113276935949)
                  ·
                    refine ⟨61302743738667478850981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163473983303113276935949 61302743738667478850981)
                    ·
                      refine ⟨11494264451000152284559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 61302743738667478850981 11494264451000152284559)
                      ·
                        rfl

theorem cell23_22385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_22385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22385 prefixEnd_22385 := by exact prefixLift 22385
  have htrace : WordTrace (prefixWord ++ tailWord_22385) baseStart_22385 baseEnd_22385 := by
    simpa [prefixWord, tailWord_22385, baseEnd_22385] using wordTrace_append hprefix tailTrace_22385
  have hstable : (prefixWord ++ tailWord_22385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22385).length < 2 ^ (prefixWord ++ tailWord_22385).sum := by decide
  have hdescent : baseEnd_22385 < baseStart_22385 := by decide
  rcases family_descends (prefixWord ++ tailWord_22385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22389 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_22389 : Nat := 118140960795 + 22389 * 2 ^ 59
def prefixEnd_22389 : Nat := 4983230072969 + 3 ^ 40 * 22389 * 2
def baseEnd_22389 : Nat := 11496318373618136634541

theorem tailTrace_22389 : CollatzResearch.WordTrace tailWord_22389 prefixEnd_22389 11496318373618136634541 := by
  unfold tailWord_22389
  simp only [CollatzResearch.WordTrace]
  refine ⟨816593915895951581886221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 544395943930634387924147 816593915895951581886221)
  ·
    refine ⟨306222718460981843207333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 816593915895951581886221 306222718460981843207333)
    ·
      refine ⟨57416759711434095601375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306222718460981843207333 57416759711434095601375)
      ·
        refine ⟨86125139567151143402063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57416759711434095601375 86125139567151143402063)
        ·
          refine ⟨129187709350726715103095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86125139567151143402063 129187709350726715103095)
          ·
            refine ⟨193781564026090072654643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129187709350726715103095 193781564026090072654643)
            ·
              refine ⟨290672346039135108981965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193781564026090072654643 290672346039135108981965)
              ·
                refine ⟨109002129764675665868237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290672346039135108981965 109002129764675665868237)
                ·
                  refine ⟨40875798661753374700589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109002129764675665868237 40875798661753374700589)
                  ·
                    refine ⟨15328424498157515512721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40875798661753374700589 15328424498157515512721)
                    ·
                      refine ⟨11496318373618136634541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15328424498157515512721 11496318373618136634541)
                      ·
                        rfl

theorem cell23_22389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_22389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22389 prefixEnd_22389 := by exact prefixLift 22389
  have htrace : WordTrace (prefixWord ++ tailWord_22389) baseStart_22389 baseEnd_22389 := by
    simpa [prefixWord, tailWord_22389, baseEnd_22389] using wordTrace_append hprefix tailTrace_22389
  have hstable : (prefixWord ++ tailWord_22389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22389).length < 2 ^ (prefixWord ++ tailWord_22389).sum := by decide
  have hdescent : baseEnd_22389 < baseStart_22389 := by decide
  rcases family_descends (prefixWord ++ tailWord_22389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22405 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_22405 : Nat := 118140960795 + 22405 * 2 ^ 59
def prefixEnd_22405 : Nat := 4983230072969 + 3 ^ 40 * 22405 * 2
def baseEnd_22405 : Nat := 11504534064090074034467

theorem tailTrace_22405 : CollatzResearch.WordTrace tailWord_22405 prefixEnd_22405 11504534064090074034467 := by
  unfold tailWord_22405
  simp only [CollatzResearch.WordTrace]
  refine ⟨817177483837986314468669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 544784989225324209645779 817177483837986314468669)
  ·
    refine ⟨306441556439244867925751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 817177483837986314468669 306441556439244867925751)
    ·
      refine ⟨459662334658867301888627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306441556439244867925751 459662334658867301888627)
      ·
        refine ⟨689493501988300952832941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459662334658867301888627 689493501988300952832941)
        ·
          refine ⟨258560063245612857312353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 689493501988300952832941 258560063245612857312353)
          ·
            refine ⟨193920047434209642984265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258560063245612857312353 193920047434209642984265)
            ·
              refine ⟨145440035575657232238199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193920047434209642984265 145440035575657232238199)
              ·
                refine ⟨218160053363485848357299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145440035575657232238199 218160053363485848357299)
                ·
                  refine ⟨327240080045228772535949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218160053363485848357299 327240080045228772535949)
                  ·
                    refine ⟨122715030016960789700981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 327240080045228772535949 122715030016960789700981)
                    ·
                      refine ⟨11504534064090074034467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 122715030016960789700981 11504534064090074034467)
                      ·
                        rfl

theorem cell23_22405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_22405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22405 prefixEnd_22405 := by exact prefixLift 22405
  have htrace : WordTrace (prefixWord ++ tailWord_22405) baseStart_22405 baseEnd_22405 := by
    simpa [prefixWord, tailWord_22405, baseEnd_22405] using wordTrace_append hprefix tailTrace_22405
  have hstable : (prefixWord ++ tailWord_22405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22405).length < 2 ^ (prefixWord ++ tailWord_22405).sum := by decide
  have hdescent : baseEnd_22405 < baseStart_22405 := by decide
  rcases family_descends (prefixWord ++ tailWord_22405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22425 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 7]
def baseStart_22425 : Nat := 118140960795 + 22425 * 2 ^ 59
def prefixEnd_22425 : Nat := 4983230072969 + 3 ^ 40 * 22425 * 2
def baseEnd_22425 : Nat := 1279422630797777309375

theorem tailTrace_22425 : CollatzResearch.WordTrace tailWord_22425 prefixEnd_22425 1279422630797777309375 := by
  unfold tailWord_22425
  simp only [CollatzResearch.WordTrace]
  refine ⟨817906943765529730196729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 545271295843686486797819 817906943765529730196729)
  ·
    refine ⟨613430207824147297647547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 817906943765529730196729 613430207824147297647547)
    ·
      refine ⟨920145311736220946471321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 613430207824147297647547 920145311736220946471321)
      ·
        refine ⟨690108983802165709853491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 920145311736220946471321 690108983802165709853491)
        ·
          refine ⟨1035163475703248564780237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690108983802165709853491 1035163475703248564780237)
          ·
            refine ⟨388186303388718211792589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1035163475703248564780237 388186303388718211792589)
            ·
              refine ⟨145569863770769329422221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388186303388718211792589 145569863770769329422221)
              ·
                refine ⟨54588698914038498533333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145569863770769329422221 54588698914038498533333)
                ·
                  refine ⟨1279422630797777309375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 54588698914038498533333 1279422630797777309375)
                  ·
                    rfl

theorem cell23_22425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 7].length) (baseStart_22425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22425 prefixEnd_22425 := by exact prefixLift 22425
  have htrace : WordTrace (prefixWord ++ tailWord_22425) baseStart_22425 baseEnd_22425 := by
    simpa [prefixWord, tailWord_22425, baseEnd_22425] using wordTrace_append hprefix tailTrace_22425
  have hstable : (prefixWord ++ tailWord_22425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22425).length < 2 ^ (prefixWord ++ tailWord_22425).sum := by decide
  have hdescent : baseEnd_22425 < baseStart_22425 := by decide
  rcases family_descends (prefixWord ++ tailWord_22425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22430 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_22430 : Nat := 118140960795 + 22430 * 2 ^ 59
def prefixEnd_22430 : Nat := 4983230072969 + 3 ^ 40 * 22430 * 2
def baseEnd_22430 : Nat := 11517371080452476221853

theorem tailTrace_22430 : CollatzResearch.WordTrace tailWord_22430 prefixEnd_22430 11517371080452476221853 := by
  unfold tailWord_22430
  simp only [CollatzResearch.WordTrace]
  refine ⟨102261163593426948016093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 545392872498277056085829 102261163593426948016093)
  ·
    refine ⟨38347936347535105506035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102261163593426948016093 38347936347535105506035)
    ·
      refine ⟨57521904521302658259053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38347936347535105506035 57521904521302658259053)
      ·
        refine ⟨21570714195488496847145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57521904521302658259053 21570714195488496847145)
        ·
          refine ⟨16178035646616372635359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21570714195488496847145 16178035646616372635359)
          ·
            refine ⟨24267053469924558953039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16178035646616372635359 24267053469924558953039)
            ·
              refine ⟨36400580204886838429559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24267053469924558953039 36400580204886838429559)
              ·
                refine ⟨54600870307330257644339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36400580204886838429559 54600870307330257644339)
                ·
                  refine ⟨81901305460995386466509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54600870307330257644339 81901305460995386466509)
                  ·
                    refine ⟨30712989547873269924941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81901305460995386466509 30712989547873269924941)
                    ·
                      refine ⟨11517371080452476221853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 30712989547873269924941 11517371080452476221853)
                      ·
                        rfl

theorem cell23_22430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_22430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22430 prefixEnd_22430 := by exact prefixLift 22430
  have htrace : WordTrace (prefixWord ++ tailWord_22430) baseStart_22430 baseEnd_22430 := by
    simpa [prefixWord, tailWord_22430, baseEnd_22430] using wordTrace_append hprefix tailTrace_22430
  have hstable : (prefixWord ++ tailWord_22430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22430).length < 2 ^ (prefixWord ++ tailWord_22430).sum := by decide
  have hdescent : baseEnd_22430 < baseStart_22430 := by decide
  rcases family_descends (prefixWord ++ tailWord_22430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22436 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 1, 4, 2]
def baseStart_22436 : Nat := 118140960795 + 22436 * 2 ^ 59
def prefixEnd_22436 : Nat := 4983230072969 + 3 ^ 40 * 22436 * 2
def baseEnd_22436 : Nat := 11520451964379452746825

theorem tailTrace_22436 : CollatzResearch.WordTrace tailWord_22436 prefixEnd_22436 11520451964379452746825 := by
  unfold tailWord_22436
  simp only [CollatzResearch.WordTrace]
  refine ⟨409154073362839304423581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 545538764483785739231441 409154073362839304423581)
  ·
    refine ⟨153432777511064739158843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 409154073362839304423581 153432777511064739158843)
    ·
      refine ⟨230149166266597108738265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153432777511064739158843 230149166266597108738265)
      ·
        refine ⟨172611874699947831553699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230149166266597108738265 172611874699947831553699)
        ·
          refine ⟨258917812049921747330549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172611874699947831553699 258917812049921747330549)
          ·
            refine ⟨24273544879680163812239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 258917812049921747330549 24273544879680163812239)
            ·
              refine ⟨36410317319520245718359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24273544879680163812239 36410317319520245718359)
              ·
                refine ⟨54615475979280368577539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36410317319520245718359 54615475979280368577539)
                ·
                  refine ⟨81923213968920552866309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54615475979280368577539 81923213968920552866309)
                  ·
                    refine ⟨15360602619172603662433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81923213968920552866309 15360602619172603662433)
                    ·
                      refine ⟨11520451964379452746825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15360602619172603662433 11520451964379452746825)
                      ·
                        rfl

theorem cell23_22436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_22436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22436 prefixEnd_22436 := by exact prefixLift 22436
  have htrace : WordTrace (prefixWord ++ tailWord_22436) baseStart_22436 baseEnd_22436 := by
    simpa [prefixWord, tailWord_22436, baseEnd_22436] using wordTrace_append hprefix tailTrace_22436
  have hstable : (prefixWord ++ tailWord_22436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22436).length < 2 ^ (prefixWord ++ tailWord_22436).sum := by decide
  have hdescent : baseEnd_22436 < baseStart_22436 := by decide
  rcases family_descends (prefixWord ++ tailWord_22436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22440 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_22440 : Nat := 118140960795 + 22440 * 2 ^ 59
def prefixEnd_22440 : Nat := 4983230072969 + 3 ^ 40 * 22440 * 2
def baseEnd_22440 : Nat := 11522505886997437096807

theorem tailTrace_22440 : CollatzResearch.WordTrace tailWord_22440 prefixEnd_22440 11522505886997437096807 := by
  unfold tailWord_22440
  simp only [CollatzResearch.WordTrace]
  refine ⟨409227019355593645996387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 545636025807458194661849 409227019355593645996387)
  ·
    refine ⟨613840529033390468994581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 409227019355593645996387 613840529033390468994581)
    ·
      refine ⟨28773774798440178234121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 613840529033390468994581 28773774798440178234121)
      ·
        refine ⟨21580331098830133675591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28773774798440178234121 21580331098830133675591)
        ·
          refine ⟨32370496648245200513387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21580331098830133675591 32370496648245200513387)
          ·
            refine ⟨48555744972367800770081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32370496648245200513387 48555744972367800770081)
            ·
              refine ⟨36416808729275850577561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48555744972367800770081 36416808729275850577561)
              ·
                refine ⟨27312606546956887933171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36416808729275850577561 27312606546956887933171)
                ·
                  refine ⟨40968909820435331899757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27312606546956887933171 40968909820435331899757)
                  ·
                    refine ⟨15363341182663249462409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40968909820435331899757 15363341182663249462409)
                    ·
                      refine ⟨11522505886997437096807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15363341182663249462409 11522505886997437096807)
                      ·
                        rfl

theorem cell23_22440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_22440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22440 prefixEnd_22440 := by exact prefixLift 22440
  have htrace : WordTrace (prefixWord ++ tailWord_22440) baseStart_22440 baseEnd_22440 := by
    simpa [prefixWord, tailWord_22440, baseEnd_22440] using wordTrace_append hprefix tailTrace_22440
  have hstable : (prefixWord ++ tailWord_22440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22440).length < 2 ^ (prefixWord ++ tailWord_22440).sum := by decide
  have hdescent : baseEnd_22440 < baseStart_22440 := by decide
  rcases family_descends (prefixWord ++ tailWord_22440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22472 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 4, 5]
def baseStart_22472 : Nat := 118140960795 + 22472 * 2 ^ 59
def prefixEnd_22472 : Nat := 4983230072969 + 3 ^ 40 * 22472 * 2
def baseEnd_22472 : Nat := 3846312422647103965553

theorem tailTrace_22472 : CollatzResearch.WordTrace tailWord_22472 prefixEnd_22472 3846312422647103965553 := by
  unfold tailWord_22472
  simp only [CollatzResearch.WordTrace]
  refine ⟨409810587297628378578835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 546414116396837838105113 409810587297628378578835)
  ·
    refine ⟨614715880946442567868253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 409810587297628378578835 614715880946442567868253)
    ·
      refine ⟨230518455354915962950595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 614715880946442567868253 230518455354915962950595)
      ·
        refine ⟨345777683032373944425893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230518455354915962950595 345777683032373944425893)
        ·
          refine ⟨64833315568570114579855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345777683032373944425893 64833315568570114579855)
          ·
            refine ⟨97249973352855171869783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64833315568570114579855 97249973352855171869783)
            ·
              refine ⟨145874960029282757804675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97249973352855171869783 145874960029282757804675)
              ·
                refine ⟨218812440043924136707013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145874960029282757804675 218812440043924136707013)
                ·
                  refine ⟨41027332508235775632565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218812440043924136707013 41027332508235775632565)
                  ·
                    refine ⟨3846312422647103965553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41027332508235775632565 3846312422647103965553)
                    ·
                      rfl

theorem cell23_22472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_22472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22472 prefixEnd_22472 := by exact prefixLift 22472
  have htrace : WordTrace (prefixWord ++ tailWord_22472) baseStart_22472 baseEnd_22472 := by
    simpa [prefixWord, tailWord_22472, baseEnd_22472] using wordTrace_append hprefix tailTrace_22472
  have hstable : (prefixWord ++ tailWord_22472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22472).length < 2 ^ (prefixWord ++ tailWord_22472).sum := by decide
  have hdescent : baseEnd_22472 < baseStart_22472 := by decide
  rcases family_descends (prefixWord ++ tailWord_22472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22476 : List Nat := [2, 2, 1, 4, 1, 3, 3, 2, 5]
def baseStart_22476 : Nat := 118140960795 + 22476 * 2 ^ 59
def prefixEnd_22476 : Nat := 4983230072969 + 3 ^ 40 * 22476 * 2
def baseEnd_22476 : Nat := 1282332354506588471849

theorem tailTrace_22476 : CollatzResearch.WordTrace tailWord_22476 prefixEnd_22476 1282332354506588471849 := by
  unfold tailWord_22476
  simp only [CollatzResearch.WordTrace]
  refine ⟨409883533290382720151641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 546511377720510293535521 409883533290382720151641)
  ·
    refine ⟨307412649967787040113731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 409883533290382720151641 307412649967787040113731)
    ·
      refine ⟨461118974951680560170597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307412649967787040113731 461118974951680560170597)
      ·
        refine ⟨86459807803440105031987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 461118974951680560170597 86459807803440105031987)
        ·
          refine ⟨129689711705160157547981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86459807803440105031987 129689711705160157547981)
          ·
            refine ⟨48633641889435059080493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129689711705160157547981 48633641889435059080493)
            ·
              refine ⟨18237615708538147155185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48633641889435059080493 18237615708538147155185)
              ·
                refine ⟨13678211781403610366389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18237615708538147155185 13678211781403610366389)
                ·
                  refine ⟨1282332354506588471849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13678211781403610366389 1282332354506588471849)
                  ·
                    rfl

theorem cell23_22476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_22476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22476 prefixEnd_22476 := by exact prefixLift 22476
  have htrace : WordTrace (prefixWord ++ tailWord_22476) baseStart_22476 baseEnd_22476 := by
    simpa [prefixWord, tailWord_22476, baseEnd_22476] using wordTrace_append hprefix tailTrace_22476
  have hstable : (prefixWord ++ tailWord_22476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22476).length < 2 ^ (prefixWord ++ tailWord_22476).sum := by decide
  have hdescent : baseEnd_22476 < baseStart_22476 := by decide
  rcases family_descends (prefixWord ++ tailWord_22476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22512 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 3]
def baseStart_22512 : Nat := 118140960795 + 22512 * 2 ^ 59
def prefixEnd_22512 : Nat := 4983230072969 + 3 ^ 40 * 22512 * 2
def baseEnd_22512 : Nat := 11559476494121155396475

theorem tailTrace_22512 : CollatzResearch.WordTrace tailWord_22512 prefixEnd_22512 11559476494121155396475 := by
  unfold tailWord_22512
  simp only [CollatzResearch.WordTrace]
  refine ⟨410540047225171794306895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 547386729633562392409193 410540047225171794306895)
  ·
    refine ⟨615810070837757691460343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 410540047225171794306895 615810070837757691460343)
    ·
      refine ⟨923715106256636537190515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615810070837757691460343 923715106256636537190515)
      ·
        refine ⟨1385572659384954805785773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923715106256636537190515 1385572659384954805785773)
        ·
          refine ⟨519589747269358052169665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1385572659384954805785773 519589747269358052169665)
          ·
            refine ⟨389692310452018539127249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519589747269358052169665 389692310452018539127249)
            ·
              refine ⟨292269232839013904345437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389692310452018539127249 292269232839013904345437)
              ·
                refine ⟨109600962314630214129539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292269232839013904345437 109600962314630214129539)
                ·
                  refine ⟨164401443471945321194309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109600962314630214129539 164401443471945321194309)
                  ·
                    refine ⟨30825270650989747723933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164401443471945321194309 30825270650989747723933)
                    ·
                      refine ⟨11559476494121155396475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 30825270650989747723933 11559476494121155396475)
                      ·
                        rfl

theorem cell23_22512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 3].length) (baseStart_22512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22512 prefixEnd_22512 := by exact prefixLift 22512
  have htrace : WordTrace (prefixWord ++ tailWord_22512) baseStart_22512 baseEnd_22512 := by
    simpa [prefixWord, tailWord_22512, baseEnd_22512] using wordTrace_append hprefix tailTrace_22512
  have hstable : (prefixWord ++ tailWord_22512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22512).length < 2 ^ (prefixWord ++ tailWord_22512).sum := by decide
  have hdescent : baseEnd_22512 < baseStart_22512 := by decide
  rcases family_descends (prefixWord ++ tailWord_22512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22515 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 10]
def baseStart_22515 : Nat := 118140960795 + 22515 * 2 ^ 59
def prefixEnd_22515 : Nat := 4983230072969 + 3 ^ 40 * 22515 * 2
def baseEnd_22515 : Nat := 1284557437342738184329

theorem tailTrace_22515 : CollatzResearch.WordTrace tailWord_22515 prefixEnd_22515 1284557437342738184329 := by
  unfold tailWord_22515
  simp only [CollatzResearch.WordTrace]
  refine ⟨821189513439475100972999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 547459675626316733981999 821189513439475100972999)
  ·
    refine ⟨1231784270159212651459499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 821189513439475100972999 1231784270159212651459499)
    ·
      refine ⟨1847676405238818977189249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1231784270159212651459499 1847676405238818977189249)
      ·
        refine ⟨1385757303929114232891937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1847676405238818977189249 1385757303929114232891937)
        ·
          refine ⟨1039317977946835674668953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1385757303929114232891937 1039317977946835674668953)
          ·
            refine ⟨779488483460126756001715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1039317977946835674668953 779488483460126756001715)
            ·
              refine ⟨1169232725190190134002573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779488483460126756001715 1169232725190190134002573)
              ·
                refine ⟨438462271946321300250965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1169232725190190134002573 438462271946321300250965)
                ·
                  refine ⟨1284557437342738184329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 438462271946321300250965 1284557437342738184329)
                  ·
                    rfl

theorem cell23_22515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 10].length) (baseStart_22515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22515 prefixEnd_22515 := by exact prefixLift 22515
  have htrace : WordTrace (prefixWord ++ tailWord_22515) baseStart_22515 baseEnd_22515 := by
    simpa [prefixWord, tailWord_22515, baseEnd_22515] using wordTrace_append hprefix tailTrace_22515
  have hstable : (prefixWord ++ tailWord_22515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22515).length < 2 ^ (prefixWord ++ tailWord_22515).sum := by decide
  have hdescent : baseEnd_22515 < baseStart_22515 := by decide
  rcases family_descends (prefixWord ++ tailWord_22515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22526 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_22526 : Nat := 118140960795 + 22526 * 2 ^ 59
def prefixEnd_22526 : Nat := 4983230072969 + 3 ^ 40 * 22526 * 2
def baseEnd_22526 : Nat := 11566665223284100621411

theorem tailTrace_22526 : CollatzResearch.WordTrace tailWord_22526 prefixEnd_22526 11566665223284100621411 := by
  unfold tailWord_22526
  simp only [CollatzResearch.WordTrace]
  refine ⟨102698839549952997452929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 547727144266415986415621 102698839549952997452929)
  ·
    refine ⟨77024129662464748089697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102698839549952997452929 77024129662464748089697)
    ·
      refine ⟨57768097246848561067273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77024129662464748089697 57768097246848561067273)
      ·
        refine ⟨43326072935136420800455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57768097246848561067273 43326072935136420800455)
        ·
          refine ⟨64989109402704631200683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43326072935136420800455 64989109402704631200683)
          ·
            refine ⟨97483664104056946801025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64989109402704631200683 97483664104056946801025)
            ·
              refine ⟨73112748078042710100769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97483664104056946801025 73112748078042710100769)
              ·
                refine ⟨54834561058532032575577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73112748078042710100769 54834561058532032575577)
                ·
                  refine ⟨41125920793899024431683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54834561058532032575577 41125920793899024431683)
                  ·
                    refine ⟨61688881190848536647525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41125920793899024431683 61688881190848536647525)
                    ·
                      refine ⟨11566665223284100621411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 61688881190848536647525 11566665223284100621411)
                      ·
                        rfl

theorem cell23_22526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_22526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22526 prefixEnd_22526 := by exact prefixLift 22526
  have htrace : WordTrace (prefixWord ++ tailWord_22526) baseStart_22526 baseEnd_22526 := by
    simpa [prefixWord, tailWord_22526, baseEnd_22526] using wordTrace_append hprefix tailTrace_22526
  have hstable : (prefixWord ++ tailWord_22526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22526).length < 2 ^ (prefixWord ++ tailWord_22526).sum := by decide
  have hdescent : baseEnd_22526 < baseStart_22526 := by decide
  rcases family_descends (prefixWord ++ tailWord_22526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22529 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_22529 : Nat := 118140960795 + 22529 * 2 ^ 59
def prefixEnd_22529 : Nat := 4983230072969 + 3 ^ 40 * 22529 * 2
def baseEnd_22529 : Nat := 11568205665247588883897

theorem tailTrace_22529 : CollatzResearch.WordTrace tailWord_22529 prefixEnd_22529 11568205665247588883897 := by
  unfold tailWord_22529
  simp only [CollatzResearch.WordTrace]
  refine ⟨821700135388755491982641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 547800090259170327988427 821700135388755491982641)
  ·
    refine ⟨616275101541566618986981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 821700135388755491982641 616275101541566618986981)
    ·
      refine ⟨115551581539043741060059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 616275101541566618986981 115551581539043741060059)
      ·
        refine ⟨173327372308565611590089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115551581539043741060059 173327372308565611590089)
        ·
          refine ⟨129995529231424208692567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173327372308565611590089 129995529231424208692567)
          ·
            refine ⟨194993293847136313038851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129995529231424208692567 194993293847136313038851)
            ·
              refine ⟨292489940770704469558277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194993293847136313038851 292489940770704469558277)
              ·
                refine ⟨54841863894507088042177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292489940770704469558277 54841863894507088042177)
                ·
                  refine ⟨41131397920880316031633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54841863894507088042177 41131397920880316031633)
                  ·
                    refine ⟨30848548440660237023725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41131397920880316031633 30848548440660237023725)
                    ·
                      refine ⟨11568205665247588883897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 30848548440660237023725 11568205665247588883897)
                      ·
                        rfl

theorem cell23_22529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_22529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22529 prefixEnd_22529 := by exact prefixLift 22529
  have htrace : WordTrace (prefixWord ++ tailWord_22529) baseStart_22529 baseEnd_22529 := by
    simpa [prefixWord, tailWord_22529, baseEnd_22529] using wordTrace_append hprefix tailTrace_22529
  have hstable : (prefixWord ++ tailWord_22529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22529).length < 2 ^ (prefixWord ++ tailWord_22529).sum := by decide
  have hdescent : baseEnd_22529 < baseStart_22529 := by decide
  rcases family_descends (prefixWord ++ tailWord_22529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22536 : List Nat := [2, 1, 3, 2, 1, 2, 3, 4, 1, 4]
def baseStart_22536 : Nat := 118140960795 + 22536 * 2 ^ 59
def prefixEnd_22536 : Nat := 4983230072969 + 3 ^ 40 * 22536 * 2
def baseEnd_22536 : Nat := 3857266676609687165455

theorem tailTrace_22536 : CollatzResearch.WordTrace tailWord_22536 prefixEnd_22536 3857266676609687165455 := by
  unfold tailWord_22536
  simp only [CollatzResearch.WordTrace]
  refine ⟨410977723181697843743731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 547970297575597124991641 410977723181697843743731)
  ·
    refine ⟨616466584772546765615597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 410977723181697843743731 616466584772546765615597)
    ·
      refine ⟨231174969289705037105849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 616466584772546765615597 231174969289705037105849)
      ·
        refine ⟨173381226967278777829387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231174969289705037105849 173381226967278777829387)
        ·
          refine ⟨260071840450918166744081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173381226967278777829387 260071840450918166744081)
          ·
            refine ⟨195053880338188625058061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260071840450918166744081 195053880338188625058061)
            ·
              refine ⟨73145205126820734396773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195053880338188625058061 73145205126820734396773)
              ·
                refine ⟨13714725961278887699395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73145205126820734396773 13714725961278887699395)
                ·
                  refine ⟨20572088941918331549093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13714725961278887699395 20572088941918331549093)
                  ·
                    refine ⟨3857266676609687165455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20572088941918331549093 3857266676609687165455)
                    ·
                      rfl

theorem cell23_22536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_22536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22536 prefixEnd_22536 := by exact prefixLift 22536
  have htrace : WordTrace (prefixWord ++ tailWord_22536) baseStart_22536 baseEnd_22536 := by
    simpa [prefixWord, tailWord_22536, baseEnd_22536] using wordTrace_append hprefix tailTrace_22536
  have hstable : (prefixWord ++ tailWord_22536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22536).length < 2 ^ (prefixWord ++ tailWord_22536).sum := by decide
  have hdescent : baseEnd_22536 < baseStart_22536 := by decide
  rcases family_descends (prefixWord ++ tailWord_22536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22593 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_22593 : Nat := 118140960795 + 22593 * 2 ^ 59
def prefixEnd_22593 : Nat := 4983230072969 + 3 ^ 40 * 22593 * 2
def baseEnd_22593 : Nat := 11601068427135338483603

theorem tailTrace_22593 : CollatzResearch.WordTrace tailWord_22593 prefixEnd_22593 11601068427135338483603 := by
  unfold tailWord_22593
  simp only [CollatzResearch.WordTrace]
  refine ⟨824034407156894422312433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 549356271437929614874955 824034407156894422312433)
  ·
    refine ⟨618025805367670816734325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 824034407156894422312433 618025805367670816734325)
    ·
      refine ⟨57939919253219139068843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 618025805367670816734325 57939919253219139068843)
      ·
        refine ⟨86909878879828708603265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57939919253219139068843 86909878879828708603265)
        ·
          refine ⟨65182409159871531452449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86909878879828708603265 65182409159871531452449)
          ·
            refine ⟨48886806869903648589337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65182409159871531452449 48886806869903648589337)
            ·
              refine ⟨36665105152427736442003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48886806869903648589337 36665105152427736442003)
              ·
                refine ⟨54997657728641604663005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36665105152427736442003 54997657728641604663005)
                ·
                  refine ⟨20624121648240601748627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54997657728641604663005 20624121648240601748627)
                  ·
                    refine ⟨30936182472360902622941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20624121648240601748627 30936182472360902622941)
                    ·
                      refine ⟨11601068427135338483603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 30936182472360902622941 11601068427135338483603)
                      ·
                        rfl

theorem cell23_22593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_22593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22593 prefixEnd_22593 := by exact prefixLift 22593
  have htrace : WordTrace (prefixWord ++ tailWord_22593) baseStart_22593 baseEnd_22593 := by
    simpa [prefixWord, tailWord_22593, baseEnd_22593] using wordTrace_append hprefix tailTrace_22593
  have hstable : (prefixWord ++ tailWord_22593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22593).length < 2 ^ (prefixWord ++ tailWord_22593).sum := by decide
  have hdescent : baseEnd_22593 < baseStart_22593 := by decide
  rcases family_descends (prefixWord ++ tailWord_22593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22616 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 1, 1, 4]
def baseStart_22616 : Nat := 118140960795 + 22616 * 2 ^ 59
def prefixEnd_22616 : Nat := 4983230072969 + 3 ^ 40 * 22616 * 2
def baseEnd_22616 : Nat := 11612878482188748495997

theorem tailTrace_22616 : CollatzResearch.WordTrace tailWord_22616 prefixEnd_22616 11612878482188748495997 := by
  unfold tailWord_22616
  simp only [CollatzResearch.WordTrace]
  refine ⟨412436643036784675199851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 549915524049046233599801 412436643036784675199851)
  ·
    refine ⟨618654964555177012799777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 412436643036784675199851 618654964555177012799777)
    ·
      refine ⟨463991223416382759599833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 618654964555177012799777 463991223416382759599833)
      ·
        refine ⟨347993417562287069699875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463991223416382759599833 347993417562287069699875)
        ·
          refine ⟨521990126343430604549813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347993417562287069699875 521990126343430604549813)
          ·
            refine ⟨48936574344696619176545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 521990126343430604549813 48936574344696619176545)
            ·
              refine ⟨36702430758522464382409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48936574344696619176545 36702430758522464382409)
              ·
                refine ⟨27526823068891848286807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36702430758522464382409 27526823068891848286807)
                ·
                  refine ⟨41290234603337772430211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27526823068891848286807 41290234603337772430211)
                  ·
                    refine ⟨61935351905006658645317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41290234603337772430211 61935351905006658645317)
                    ·
                      refine ⟨11612878482188748495997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 61935351905006658645317 11612878482188748495997)
                      ·
                        rfl

theorem cell23_22616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_22616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22616 prefixEnd_22616 := by exact prefixLift 22616
  have htrace : WordTrace (prefixWord ++ tailWord_22616) baseStart_22616 baseEnd_22616 := by
    simpa [prefixWord, tailWord_22616, baseEnd_22616] using wordTrace_append hprefix tailTrace_22616
  have hstable : (prefixWord ++ tailWord_22616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22616).length < 2 ^ (prefixWord ++ tailWord_22616).sum := by decide
  have hdescent : baseEnd_22616 < baseStart_22616 := by decide
  rcases family_descends (prefixWord ++ tailWord_22616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22636 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 3]
def baseStart_22636 : Nat := 118140960795 + 22636 * 2 ^ 59
def prefixEnd_22636 : Nat := 4983230072969 + 3 ^ 40 * 22636 * 2
def baseEnd_22636 : Nat := 11623148095278670245905

theorem tailTrace_22636 : CollatzResearch.WordTrace tailWord_22636 prefixEnd_22636 11623148095278670245905 := by
  unfold tailWord_22636
  simp only [CollatzResearch.WordTrace]
  refine ⟨412801373000556383063881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 550401830667408510751841 412801373000556383063881)
  ·
    refine ⟨309601029750417287297911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 412801373000556383063881 309601029750417287297911)
    ·
      refine ⟨464401544625625930946867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309601029750417287297911 464401544625625930946867)
      ·
        refine ⟨696602316938438896420301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464401544625625930946867 696602316938438896420301)
        ·
          refine ⟨261225868851914586157613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 696602316938438896420301 261225868851914586157613)
          ·
            refine ⟨97959700819467969809105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261225868851914586157613 97959700819467969809105)
            ·
              refine ⟨73469775614600977356829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97959700819467969809105 73469775614600977356829)
              ·
                refine ⟨27551165855475366508811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73469775614600977356829 27551165855475366508811)
                ·
                  refine ⟨41326748783213049763217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27551165855475366508811 41326748783213049763217)
                  ·
                    refine ⟨30995061587409787322413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41326748783213049763217 30995061587409787322413)
                    ·
                      refine ⟨11623148095278670245905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 30995061587409787322413 11623148095278670245905)
                      ·
                        rfl

theorem cell23_22636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_22636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22636 prefixEnd_22636 := by exact prefixLift 22636
  have htrace : WordTrace (prefixWord ++ tailWord_22636) baseStart_22636 baseEnd_22636 := by
    simpa [prefixWord, tailWord_22636, baseEnd_22636] using wordTrace_append hprefix tailTrace_22636
  have hstable : (prefixWord ++ tailWord_22636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22636).length < 2 ^ (prefixWord ++ tailWord_22636).sum := by decide
  have hdescent : baseEnd_22636 < baseStart_22636 := by decide
  rcases family_descends (prefixWord ++ tailWord_22636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22670 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_22670 : Nat := 118140960795 + 22670 * 2 ^ 59
def prefixEnd_22670 : Nat := 4983230072969 + 3 ^ 40 * 22670 * 2
def baseEnd_22670 : Nat := 11640606437531537220749

theorem tailTrace_22670 : CollatzResearch.WordTrace tailWord_22670 prefixEnd_22670 11640606437531537220749 := by
  unfold tailWord_22670
  simp only [CollatzResearch.WordTrace]
  refine ⟨103355353484742071608183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 551228551918624381910309 103355353484742071608183)
  ·
    refine ⟨155033030227113107412275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103355353484742071608183 155033030227113107412275)
    ·
      refine ⟨232549545340669661118413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155033030227113107412275 232549545340669661118413)
      ·
        refine ⟨87206079502751122919405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232549545340669661118413 87206079502751122919405)
        ·
          refine ⟨32702279813531671094777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87206079502751122919405 32702279813531671094777)
          ·
            refine ⟨24526709860148753321083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32702279813531671094777 24526709860148753321083)
            ·
              refine ⟨36790064790223129981625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24526709860148753321083 36790064790223129981625)
              ·
                refine ⟨27592548592667347486219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36790064790223129981625 27592548592667347486219)
                ·
                  refine ⟨41388822889001021229329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27592548592667347486219 41388822889001021229329)
                  ·
                    refine ⟨31041617166750765921997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41388822889001021229329 31041617166750765921997)
                    ·
                      refine ⟨11640606437531537220749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 31041617166750765921997 11640606437531537220749)
                      ·
                        rfl

theorem cell23_22670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_22670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22670 prefixEnd_22670 := by exact prefixLift 22670
  have htrace : WordTrace (prefixWord ++ tailWord_22670) baseStart_22670 baseEnd_22670 := by
    simpa [prefixWord, tailWord_22670, baseEnd_22670] using wordTrace_append hprefix tailTrace_22670
  have hstable : (prefixWord ++ tailWord_22670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22670).length < 2 ^ (prefixWord ++ tailWord_22670).sum := by decide
  have hdescent : baseEnd_22670 < baseStart_22670 := by decide
  rcases family_descends (prefixWord ++ tailWord_22670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22706 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2]
def baseStart_22706 : Nat := 118140960795 + 22706 * 2 ^ 59
def prefixEnd_22706 : Nat := 4983230072969 + 3 ^ 40 * 22706 * 2
def baseEnd_22706 : Nat := 11659091741093396370583

theorem tailTrace_22706 : CollatzResearch.WordTrace tailWord_22706 prefixEnd_22706 11659091741093396370583 := by
  unfold tailWord_22706
  simp only [CollatzResearch.WordTrace]
  refine ⟨207038963936878680293993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 552103903831676480783981 207038963936878680293993)
  ·
    refine ⟨155279222952659010220495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207038963936878680293993 155279222952659010220495)
    ·
      refine ⟨232918834428988515330743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155279222952659010220495 232918834428988515330743)
      ·
        refine ⟨349378251643482772996115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232918834428988515330743 349378251643482772996115)
        ·
          refine ⟨524067377465224159494173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349378251643482772996115 524067377465224159494173)
          ·
            refine ⟨196525266549459059810315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 524067377465224159494173 196525266549459059810315)
            ·
              refine ⟨294787899824188589715473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196525266549459059810315 294787899824188589715473)
              ·
                refine ⟨221090924868141442286605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294787899824188589715473 221090924868141442286605)
                ·
                  refine ⟨82909096825553040857477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221090924868141442286605 82909096825553040857477)
                  ·
                    refine ⟨15545455654791195160777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82909096825553040857477 15545455654791195160777)
                    ·
                      refine ⟨11659091741093396370583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 15545455654791195160777 11659091741093396370583)
                      ·
                        rfl

theorem cell23_22706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_22706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22706 prefixEnd_22706 := by exact prefixLift 22706
  have htrace : WordTrace (prefixWord ++ tailWord_22706) baseStart_22706 baseEnd_22706 := by
    simpa [prefixWord, tailWord_22706, baseEnd_22706] using wordTrace_append hprefix tailTrace_22706
  have hstable : (prefixWord ++ tailWord_22706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22706).length < 2 ^ (prefixWord ++ tailWord_22706).sum := by decide
  have hdescent : baseEnd_22706 < baseStart_22706 := by decide
  rcases family_descends (prefixWord ++ tailWord_22706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22716 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 2, 6]
def baseStart_22716 : Nat := 118140960795 + 22716 * 2 ^ 59
def prefixEnd_22716 : Nat := 4983230072969 + 3 ^ 40 * 22716 * 2
def baseEnd_22716 : Nat := 3888075515879452415179

theorem tailTrace_22716 : CollatzResearch.WordTrace tailWord_22716 prefixEnd_22716 3888075515879452415179 := by
  unfold tailWord_22716
  simp only [CollatzResearch.WordTrace]
  refine ⟨414260292855643214520001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 552347057140857619360001 414260292855643214520001)
  ·
    refine ⟨310695219641732410890001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 414260292855643214520001 310695219641732410890001)
    ·
      refine ⟨233021414731299308167501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310695219641732410890001 233021414731299308167501)
      ·
        refine ⟨87383030524237240562813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233021414731299308167501 87383030524237240562813)
        ·
          refine ⟨32768636446588965211055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87383030524237240562813 32768636446588965211055)
          ·
            refine ⟨49152954669883447816583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32768636446588965211055 49152954669883447816583)
            ·
              refine ⟨73729432004825171724875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49152954669883447816583 73729432004825171724875)
              ·
                refine ⟨110594148007237757587313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73729432004825171724875 110594148007237757587313)
                ·
                  refine ⟨82945611005428318190485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110594148007237757587313 82945611005428318190485)
                  ·
                    refine ⟨3888075515879452415179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82945611005428318190485 3888075515879452415179)
                    ·
                      rfl

theorem cell23_22716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_22716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22716 prefixEnd_22716 := by exact prefixLift 22716
  have htrace : WordTrace (prefixWord ++ tailWord_22716) baseStart_22716 baseEnd_22716 := by
    simpa [prefixWord, tailWord_22716, baseEnd_22716] using wordTrace_append hprefix tailTrace_22716
  have hstable : (prefixWord ++ tailWord_22716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22716).length < 2 ^ (prefixWord ++ tailWord_22716).sum := by decide
  have hdescent : baseEnd_22716 < baseStart_22716 := by decide
  rcases family_descends (prefixWord ++ tailWord_22716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22739 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 3]
def baseStart_22739 : Nat := 118140960795 + 22739 * 2 ^ 59
def prefixEnd_22739 : Nat := 4983230072969 + 3 ^ 40 * 22739 * 2
def baseEnd_22739 : Nat := 11676036602691767257931

theorem tailTrace_22739 : CollatzResearch.WordTrace tailWord_22739 prefixEnd_22739 11676036602691767257931 := by
  unfold tailWord_22739
  simp only [CollatzResearch.WordTrace]
  refine ⟨829359464627961357127271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 552906309751974238084847 829359464627961357127271)
  ·
    refine ⟨1244039196941942035690907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 829359464627961357127271 1244039196941942035690907)
    ·
      refine ⟨1866058795412913053536361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1244039196941942035690907 1866058795412913053536361)
      ·
        refine ⟨1399544096559684790152271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1866058795412913053536361 1399544096559684790152271)
        ·
          refine ⟨2099316144839527185228407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399544096559684790152271 2099316144839527185228407)
          ·
            refine ⟨3148974217259290777842611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099316144839527185228407 3148974217259290777842611)
            ·
              refine ⟨4723461325888936166763917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3148974217259290777842611 4723461325888936166763917)
              ·
                refine ⟨1771297997208351062536469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4723461325888936166763917 1771297997208351062536469)
                ·
                  refine ⟨83029593619141456056397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1771297997208351062536469 83029593619141456056397)
                  ·
                    refine ⟨31136097607178046021149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83029593619141456056397 31136097607178046021149)
                    ·
                      refine ⟨11676036602691767257931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 31136097607178046021149 11676036602691767257931)
                      ·
                        rfl

theorem cell23_22739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 3].length) (baseStart_22739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22739 prefixEnd_22739 := by exact prefixLift 22739
  have htrace : WordTrace (prefixWord ++ tailWord_22739) baseStart_22739 baseEnd_22739 := by
    simpa [prefixWord, tailWord_22739, baseEnd_22739] using wordTrace_append hprefix tailTrace_22739
  have hstable : (prefixWord ++ tailWord_22739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22739).length < 2 ^ (prefixWord ++ tailWord_22739).sum := by decide
  have hdescent : baseEnd_22739 < baseStart_22739 := by decide
  rcases family_descends (prefixWord ++ tailWord_22739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22746 : List Nat := [3, 1, 1, 2, 2, 1, 3, 5, 5]
def baseStart_22746 : Nat := 118140960795 + 22746 * 2 ^ 59
def prefixEnd_22746 : Nat := 4983230072969 + 3 ^ 40 * 22746 * 2
def baseEnd_22746 : Nat := 1297736774141471096711

theorem tailTrace_22746 : CollatzResearch.WordTrace tailWord_22746 prefixEnd_22746 1297736774141471096711 := by
  unfold tailWord_22746
  simp only [CollatzResearch.WordTrace]
  refine ⟨207403693900650388158023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 553076517068401035088061 207403693900650388158023)
  ·
    refine ⟨311105540850975582237035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207403693900650388158023 311105540850975582237035)
    ·
      refine ⟨466658311276463373355553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311105540850975582237035 466658311276463373355553)
      ·
        refine ⟨349993733457347530016665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466658311276463373355553 349993733457347530016665)
        ·
          refine ⟨262495300093010647512499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349993733457347530016665 262495300093010647512499)
          ·
            refine ⟨393742950139515971268749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262495300093010647512499 393742950139515971268749)
            ·
              refine ⟨147653606302318489225781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393742950139515971268749 147653606302318489225781)
              ·
                refine ⟨13842525590842358364917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147653606302318489225781 13842525590842358364917)
                ·
                  refine ⟨1297736774141471096711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13842525590842358364917 1297736774141471096711)
                  ·
                    rfl

theorem cell23_22746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_22746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_22746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_22746 prefixEnd_22746 := by exact prefixLift 22746
  have htrace : WordTrace (prefixWord ++ tailWord_22746) baseStart_22746 baseEnd_22746 := by
    simpa [prefixWord, tailWord_22746, baseEnd_22746] using wordTrace_append hprefix tailTrace_22746
  have hstable : (prefixWord ++ tailWord_22746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22746).length < 2 ^ (prefixWord ++ tailWord_22746).sum := by decide
  have hdescent : baseEnd_22746 < baseStart_22746 := by decide
  rcases family_descends (prefixWord ++ tailWord_22746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
