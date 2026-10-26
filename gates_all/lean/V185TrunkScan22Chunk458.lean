import V185TrunkScan22Chunk457

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4081678 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_4081678 : Nat := 118140960795 + 4081678 * 2 ^ 59
def prefixEnd_4081678 : Nat := 4983230072969 + 3 ^ 40 * 4081678 * 2
def baseEnd_4081678 : Nat := 1397241793921591099835807

theorem tailTrace_4081678 : CollatzResearch.WordTrace tailWord_4081678 prefixEnd_4081678 1397241793921591099835807 := by
  unfold tailWord_4081678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18608878363348146993616711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99247351271190117299289125 18608878363348146993616711)
  ·
    refine ⟨27913317545022220490425067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18608878363348146993616711 27913317545022220490425067)
    ·
      refine ⟨41869976317533330735637601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27913317545022220490425067 41869976317533330735637601)
      ·
        refine ⟨31402482238149998051728201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41869976317533330735637601 31402482238149998051728201)
        ·
          refine ⟨23551861678612498538796151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31402482238149998051728201 23551861678612498538796151)
          ·
            refine ⟨35327792517918747808194227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23551861678612498538796151 35327792517918747808194227)
            ·
              refine ⟨52991688776878121712291341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35327792517918747808194227 52991688776878121712291341)
              ·
                refine ⟨19871883291329295642109253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52991688776878121712291341 19871883291329295642109253)
                ·
                  refine ⟨3725978117124242932895485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19871883291329295642109253 3725978117124242932895485)
                  ·
                    refine ⟨1397241793921591099835807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3725978117124242932895485 1397241793921591099835807)
                    ·
                      rfl

theorem cell22_4081678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_4081678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081678 prefixEnd_4081678 := by exact prefixLift 4081678
  have htrace : WordTrace (prefixWord ++ tailWord_4081678) baseStart_4081678 baseEnd_4081678 := by
    simpa [prefixWord, tailWord_4081678, baseEnd_4081678] using wordTrace_append hprefix tailTrace_4081678
  have hstable : (prefixWord ++ tailWord_4081678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081678).length < 2 ^ (prefixWord ++ tailWord_4081678).sum := by decide
  have hdescent : baseEnd_4081678 < baseStart_4081678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081710 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4081710 : Nat := 118140960795 + 4081710 * 2 ^ 59
def prefixEnd_4081710 : Nat := 4983230072969 + 3 ^ 40 * 4081710 * 2
def baseEnd_4081710 : Nat := 1397252748175553683035709

theorem tailTrace_4081710 : CollatzResearch.WordTrace tailWord_4081710 prefixEnd_4081710 1397252748175553683035709 := by
  unfold tailWord_4081710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18609024255333655676762323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99248129361779496942732389 18609024255333655676762323)
  ·
    refine ⟨27913536383000483515143485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18609024255333655676762323 27913536383000483515143485)
    ·
      refine ⟨10467576143625181318178807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27913536383000483515143485 10467576143625181318178807)
      ·
        refine ⟨15701364215437771977268211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10467576143625181318178807 15701364215437771977268211)
        ·
          refine ⟨23552046323156657965902317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15701364215437771977268211 23552046323156657965902317)
          ·
            refine ⟨8832017371183746737213369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23552046323156657965902317 8832017371183746737213369)
            ·
              refine ⟨6624013028387810052910027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8832017371183746737213369 6624013028387810052910027)
              ·
                refine ⟨9936019542581715079365041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6624013028387810052910027 9936019542581715079365041)
                ·
                  refine ⟨7452014656936286309523781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9936019542581715079365041 7452014656936286309523781)
                  ·
                    refine ⟨1397252748175553683035709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7452014656936286309523781 1397252748175553683035709)
                    ·
                      rfl

theorem cell22_4081710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4081710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081710 prefixEnd_4081710 := by exact prefixLift 4081710
  have htrace : WordTrace (prefixWord ++ tailWord_4081710) baseStart_4081710 baseEnd_4081710 := by
    simpa [prefixWord, tailWord_4081710, baseEnd_4081710] using wordTrace_append hprefix tailTrace_4081710
  have hstable : (prefixWord ++ tailWord_4081710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081710).length < 2 ^ (prefixWord ++ tailWord_4081710).sum := by decide
  have hdescent : baseEnd_4081710 < baseStart_4081710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081751 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 1, 7]
def baseStart_4081751 : Nat := 118140960795 + 4081751 * 2 ^ 59
def prefixEnd_4081751 : Nat := 4983230072969 + 3 ^ 40 * 4081751 * 2
def baseEnd_4081751 : Nat := 1397266783313443242760583

theorem tailTrace_4081751 : CollatzResearch.WordTrace tailWord_4081751 prefixEnd_4081751 1397266783313443242760583 := by
  unfold tailWord_4081751
  simp only [CollatzResearch.WordTrace]
  refine ⟨148873689435520709416341107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99249126290347139610894071 148873689435520709416341107)
  ·
    refine ⟨223310534153281064124511661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148873689435520709416341107 223310534153281064124511661)
    ·
      refine ⟨83741450307480399046691873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223310534153281064124511661 83741450307480399046691873)
      ·
        refine ⟨62806087730610299285018905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83741450307480399046691873 62806087730610299285018905)
        ·
          refine ⟨47104565797957724463764179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62806087730610299285018905 47104565797957724463764179)
          ·
            refine ⟨70656848696936586695646269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47104565797957724463764179 70656848696936586695646269)
            ·
              refine ⟨26496318261351220010867351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70656848696936586695646269 26496318261351220010867351)
              ·
                refine ⟨39744477392026830016301027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26496318261351220010867351 39744477392026830016301027)
                ·
                  refine ⟨59616716088040245024451541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39744477392026830016301027 59616716088040245024451541)
                  ·
                    refine ⟨1397266783313443242760583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59616716088040245024451541 1397266783313443242760583)
                    ·
                      rfl

theorem cell22_4081751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_4081751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081751 prefixEnd_4081751 := by exact prefixLift 4081751
  have htrace : WordTrace (prefixWord ++ tailWord_4081751) baseStart_4081751 baseEnd_4081751 := by
    simpa [prefixWord, tailWord_4081751, baseEnd_4081751] using wordTrace_append hprefix tailTrace_4081751
  have hstable : (prefixWord ++ tailWord_4081751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081751).length < 2 ^ (prefixWord ++ tailWord_4081751).sum := by decide
  have hdescent : baseEnd_4081751 < baseStart_4081751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081757 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_4081757 : Nat := 118140960795 + 4081757 * 2 ^ 59
def prefixEnd_4081757 : Nat := 4983230072969 + 3 ^ 40 * 4081757 * 2
def baseEnd_4081757 : Nat := 1397268837236061227110565

theorem tailTrace_4081757 : CollatzResearch.WordTrace tailWord_4081757 prefixEnd_4081757 1397268837236061227110565 := by
  unfold tailWord_4081757
  simp only [CollatzResearch.WordTrace]
  refine ⟨148873908273498972441059525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99249272182332648294039683 148873908273498972441059525)
  ·
    refine ⟨27913857801281057332698661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148873908273498972441059525 27913857801281057332698661)
    ·
      refine ⟨5233848337740198249880999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27913857801281057332698661 5233848337740198249880999)
      ·
        refine ⟨7850772506610297374821499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5233848337740198249880999 7850772506610297374821499)
        ·
          refine ⟨11776158759915446062232249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7850772506610297374821499 11776158759915446062232249)
          ·
            refine ⟨8832119069936584546674187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11776158759915446062232249 8832119069936584546674187)
            ·
              refine ⟨13248178604904876820011281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8832119069936584546674187 13248178604904876820011281)
              ·
                refine ⟨9936133953678657615008461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13248178604904876820011281 9936133953678657615008461)
                ·
                  refine ⟨3726050232629496605628173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9936133953678657615008461 3726050232629496605628173)
                  ·
                    refine ⟨1397268837236061227110565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3726050232629496605628173 1397268837236061227110565)
                    ·
                      rfl

theorem cell22_4081757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_4081757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081757 prefixEnd_4081757 := by exact prefixLift 4081757
  have htrace : WordTrace (prefixWord ++ tailWord_4081757) baseStart_4081757 baseEnd_4081757 := by
    simpa [prefixWord, tailWord_4081757, baseEnd_4081757] using wordTrace_append hprefix tailTrace_4081757
  have hstable : (prefixWord ++ tailWord_4081757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081757).length < 2 ^ (prefixWord ++ tailWord_4081757).sum := by decide
  have hdescent : baseEnd_4081757 < baseStart_4081757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081860 : List Nat := [2, 3, 3, 1, 2, 2, 2, 7]
def baseStart_4081860 : Nat := 118140960795 + 4081860 * 2 ^ 59
def prefixEnd_4081860 : Nat := 4983230072969 + 3 ^ 40 * 4081860 * 2
def baseEnd_4081860 : Nat := 155256010693444810198361

theorem tailTrace_4081860 : CollatzResearch.WordTrace tailWord_4081860 prefixEnd_4081860 155256010693444810198361 := by
  unfold tailWord_4081860
  simp only [CollatzResearch.WordTrace]
  refine ⟨74438832496062910516029517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99251776661417214021372689 74438832496062910516029517)
  ·
    refine ⟨27914562186023591443511069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74438832496062910516029517 27914562186023591443511069)
    ·
      refine ⟨10467960819758846791316651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27914562186023591443511069 10467960819758846791316651)
      ·
        refine ⟨15701941229638270186974977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10467960819758846791316651 15701941229638270186974977)
        ·
          refine ⟨11776455922228702640231233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15701941229638270186974977 11776455922228702640231233)
          ·
            refine ⟨8832341941671526980173425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11776455922228702640231233 8832341941671526980173425)
            ·
              refine ⟨6624256456253645235130069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8832341941671526980173425 6624256456253645235130069)
              ·
                refine ⟨155256010693444810198361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6624256456253645235130069 155256010693444810198361)
                ·
                  rfl

theorem cell22_4081860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 7].length) (baseStart_4081860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081860 prefixEnd_4081860 := by exact prefixLift 4081860
  have htrace : WordTrace (prefixWord ++ tailWord_4081860) baseStart_4081860 baseEnd_4081860 := by
    simpa [prefixWord, tailWord_4081860, baseEnd_4081860] using wordTrace_append hprefix tailTrace_4081860
  have hstable : (prefixWord ++ tailWord_4081860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081860).length < 2 ^ (prefixWord ++ tailWord_4081860).sum := by decide
  have hdescent : baseEnd_4081860 < baseStart_4081860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081892 : List Nat := [2, 3, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_4081892 : Nat := 118140960795 + 4081892 * 2 ^ 59
def prefixEnd_4081892 : Nat := 4983230072969 + 3 ^ 40 * 4081892 * 2
def baseEnd_4081892 : Nat := 1397315050494965874985151

theorem tailTrace_4081892 : CollatzResearch.WordTrace tailWord_4081892 prefixEnd_4081892 1397315050494965874985151 := by
  unfold tailWord_4081892
  simp only [CollatzResearch.WordTrace]
  refine ⟨74439416064004945248611965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99252554752006593664815953 74439416064004945248611965)
  ·
    refine ⟨27914781024001854468229487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74439416064004945248611965 27914781024001854468229487)
    ·
      refine ⟨41872171536002781702344231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27914781024001854468229487 41872171536002781702344231)
      ·
        refine ⟨62808257304004172553516347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41872171536002781702344231 62808257304004172553516347)
        ·
          refine ⟨94212385956006258830274521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62808257304004172553516347 94212385956006258830274521)
          ·
            refine ⟨70659289467004694122705891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94212385956006258830274521 70659289467004694122705891)
            ·
              refine ⟨105988934200507041184058837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70659289467004694122705891 105988934200507041184058837)
              ·
                refine ⟨2484115645324383777751379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105988934200507041184058837 2484115645324383777751379)
                ·
                  refine ⟨3726173467986575666627069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484115645324383777751379 3726173467986575666627069)
                  ·
                    refine ⟨1397315050494965874985151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3726173467986575666627069 1397315050494965874985151)
                    ·
                      rfl

theorem cell22_4081892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_4081892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081892 prefixEnd_4081892 := by exact prefixLift 4081892
  have htrace : WordTrace (prefixWord ++ tailWord_4081892) baseStart_4081892 baseEnd_4081892 := by
    simpa [prefixWord, tailWord_4081892, baseEnd_4081892] using wordTrace_append hprefix tailTrace_4081892
  have hstable : (prefixWord ++ tailWord_4081892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081892).length < 2 ^ (prefixWord ++ tailWord_4081892).sum := by decide
  have hdescent : baseEnd_4081892 < baseStart_4081892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081922 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_4081922 : Nat := 118140960795 + 4081922 * 2 ^ 59
def prefixEnd_4081922 : Nat := 4983230072969 + 3 ^ 40 * 4081922 * 2
def baseEnd_4081922 : Nat := 465775106702685265578353

theorem tailTrace_4081922 : CollatzResearch.WordTrace tailWord_4081922 prefixEnd_4081922 465775106702685265578353 := by
  unfold tailWord_4081922
  simp only [CollatzResearch.WordTrace]
  refine ⟨37219981579475301405204005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99253284211934137080544013 37219981579475301405204005)
  ·
    refine ⟨6978746546151619013475751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37219981579475301405204005 6978746546151619013475751)
    ·
      refine ⟨10468119819227428520213627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978746546151619013475751 10468119819227428520213627)
      ·
        refine ⟨15702179728841142780320441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10468119819227428520213627 15702179728841142780320441)
        ·
          refine ⟨11776634796630857085240331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15702179728841142780320441 11776634796630857085240331)
          ·
            refine ⟨17664952194946285627860497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11776634796630857085240331 17664952194946285627860497)
            ·
              refine ⟨13248714146209714220895373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17664952194946285627860497 13248714146209714220895373)
              ·
                refine ⟨4968267804828642832835765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13248714146209714220895373 4968267804828642832835765)
                ·
                  refine ⟨465775106702685265578353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4968267804828642832835765 465775106702685265578353)
                  ·
                    rfl

theorem cell22_4081922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_4081922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081922 prefixEnd_4081922 := by exact prefixLift 4081922
  have htrace : WordTrace (prefixWord ++ tailWord_4081922) baseStart_4081922 baseEnd_4081922 := by
    simpa [prefixWord, tailWord_4081922, baseEnd_4081922] using wordTrace_append hprefix tailTrace_4081922
  have hstable : (prefixWord ++ tailWord_4081922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081922).length < 2 ^ (prefixWord ++ tailWord_4081922).sum := by decide
  have hdescent : baseEnd_4081922 < baseStart_4081922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081952 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 1, 4]
def baseStart_4081952 : Nat := 118140960795 + 4081952 * 2 ^ 59
def prefixEnd_4081952 : Nat := 4983230072969 + 3 ^ 40 * 4081952 * 2
def baseEnd_4081952 : Nat := 1397335589721145718484967

theorem tailTrace_4081952 : CollatzResearch.WordTrace tailWord_4081952 prefixEnd_4081952 1397335589721145718484967 := by
  unfold tailWord_4081952
  simp only [CollatzResearch.WordTrace]
  refine ⟨74440510253896260372204055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99254013671861680496272073 74440510253896260372204055)
  ·
    refine ⟨111660765380844390558306083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74440510253896260372204055 111660765380844390558306083)
    ·
      refine ⟨167491148071266585837459125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111660765380844390558306083 167491148071266585837459125)
      ·
        refine ⟨15702295131681242422261793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167491148071266585837459125 15702295131681242422261793)
        ·
          refine ⟨11776721348760931816696345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15702295131681242422261793 11776721348760931816696345)
          ·
            refine ⟨8832541011570698862522259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11776721348760931816696345 8832541011570698862522259)
            ·
              refine ⟨13248811517356048293783389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8832541011570698862522259 13248811517356048293783389)
              ·
                refine ⟨4968304319008518110168771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13248811517356048293783389 4968304319008518110168771)
                ·
                  refine ⟨7452456478512777165253157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968304319008518110168771 7452456478512777165253157)
                  ·
                    refine ⟨1397335589721145718484967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7452456478512777165253157 1397335589721145718484967)
                    ·
                      rfl

theorem cell22_4081952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_4081952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081952 prefixEnd_4081952 := by exact prefixLift 4081952
  have htrace : WordTrace (prefixWord ++ tailWord_4081952) baseStart_4081952 baseEnd_4081952 := by
    simpa [prefixWord, tailWord_4081952, baseEnd_4081952] using wordTrace_append hprefix tailTrace_4081952
  have hstable : (prefixWord ++ tailWord_4081952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081952).length < 2 ^ (prefixWord ++ tailWord_4081952).sum := by decide
  have hdescent : baseEnd_4081952 < baseStart_4081952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081982 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4081982 : Nat := 118140960795 + 4081982 * 2 ^ 59
def prefixEnd_4081982 : Nat := 4983230072969 + 3 ^ 40 * 4081982 * 2
def baseEnd_4081982 : Nat := 1397345859334235640234875

theorem tailTrace_4081982 : CollatzResearch.WordTrace tailWord_4081982 prefixEnd_4081982 1397345859334235640234875 := by
  unfold tailWord_4081982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18610264337210479483500025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99254743131789223912000133 18610264337210479483500025)
  ·
    refine ⟨13957698252907859612625019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18610264337210479483500025 13957698252907859612625019)
    ·
      refine ⟨20936547379361789418937529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13957698252907859612625019 20936547379361789418937529)
      ·
        refine ⟨15702410534521342064203147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20936547379361789418937529 15702410534521342064203147)
        ·
          refine ⟨23553615801782013096304721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15702410534521342064203147 23553615801782013096304721)
          ·
            refine ⟨17665211851336509822228541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23553615801782013096304721 17665211851336509822228541)
            ·
              refine ⟨6624454444251191183335703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17665211851336509822228541 6624454444251191183335703)
              ·
                refine ⟨9936681666376786775003555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6624454444251191183335703 9936681666376786775003555)
                ·
                  refine ⟨14905022499565180162505333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9936681666376786775003555 14905022499565180162505333)
                  ·
                    refine ⟨1397345859334235640234875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14905022499565180162505333 1397345859334235640234875)
                    ·
                      rfl

theorem cell22_4081982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4081982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081982 prefixEnd_4081982 := by exact prefixLift 4081982
  have htrace : WordTrace (prefixWord ++ tailWord_4081982) baseStart_4081982 baseEnd_4081982 := by
    simpa [prefixWord, tailWord_4081982, baseEnd_4081982] using wordTrace_append hprefix tailTrace_4081982
  have hstable : (prefixWord ++ tailWord_4081982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081982).length < 2 ^ (prefixWord ++ tailWord_4081982).sum := by decide
  have hdescent : baseEnd_4081982 < baseStart_4081982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081993 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_4081993 : Nat := 118140960795 + 4081993 * 2 ^ 59
def prefixEnd_4081993 : Nat := 4983230072969 + 3 ^ 40 * 4081993 * 2
def baseEnd_4081993 : Nat := 1397349624859035278209841

theorem tailTrace_4081993 : CollatzResearch.WordTrace tailWord_4081993 prefixEnd_4081993 1397349624859035278209841 := by
  unfold tailWord_4081993
  simp only [CollatzResearch.WordTrace]
  refine ⟨148882515900643984746650633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99255010600429323164433755 148882515900643984746650633)
  ·
    refine ⟨111661886925482988559987975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148882515900643984746650633 111661886925482988559987975)
    ·
      refine ⟨167492830388224482839981963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111661886925482988559987975 167492830388224482839981963)
      ·
        refine ⟨251239245582336724259972945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167492830388224482839981963 251239245582336724259972945)
        ·
          refine ⟨188429434186752543194979709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251239245582336724259972945 188429434186752543194979709)
          ·
            refine ⟨70661037820032203698117391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188429434186752543194979709 70661037820032203698117391)
            ·
              refine ⟨105991556730048305547176087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70661037820032203698117391 105991556730048305547176087)
              ·
                refine ⟨158987335095072458320764131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105991556730048305547176087 158987335095072458320764131)
                ·
                  refine ⟨238481002642608687481146197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158987335095072458320764131 238481002642608687481146197)
                  ·
                    refine ⟨1397349624859035278209841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 238481002642608687481146197 1397349624859035278209841)
                    ·
                      rfl

theorem cell22_4081993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_4081993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081993 prefixEnd_4081993 := by exact prefixLift 4081993
  have htrace : WordTrace (prefixWord ++ tailWord_4081993) baseStart_4081993 baseEnd_4081993 := by
    simpa [prefixWord, tailWord_4081993, baseEnd_4081993] using wordTrace_append hprefix tailTrace_4081993
  have hstable : (prefixWord ++ tailWord_4081993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081993).length < 2 ^ (prefixWord ++ tailWord_4081993).sum := by decide
  have hdescent : baseEnd_4081993 < baseStart_4081993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082078 : List Nat := [4, 3, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_4082078 : Nat := 118140960795 + 4082078 * 2 ^ 59
def prefixEnd_4082078 : Nat := 4983230072969 + 3 ^ 40 * 4082078 * 2
def baseEnd_4082078 : Nat := 1397378722096123389834581

theorem tailTrace_4082078 : CollatzResearch.WordTrace tailWord_4082078 prefixEnd_4082078 1397378722096123389834581 := by
  unfold tailWord_4082078
  simp only [CollatzResearch.WordTrace]
  refine ⟨18610702013167005532936861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99257077403557362842329925 18610702013167005532936861)
  ·
    refine ⟨6979013254937627074851323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18610702013167005532936861 6979013254937627074851323)
    ·
      refine ⟨10468519882406440612276985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6979013254937627074851323 10468519882406440612276985)
      ·
        refine ⟨7851389911804830459207739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10468519882406440612276985 7851389911804830459207739)
        ·
          refine ⟨11777084867707245688811609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7851389911804830459207739 11777084867707245688811609)
          ·
            refine ⟨8832813650780434266608707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11777084867707245688811609 8832813650780434266608707)
            ·
              refine ⟨13249220476170651399913061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8832813650780434266608707 13249220476170651399913061)
              ·
                refine ⟨2484228839281997137483699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13249220476170651399913061 2484228839281997137483699)
                ·
                  refine ⟨3726343258922995706225549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484228839281997137483699 3726343258922995706225549)
                  ·
                    refine ⟨1397378722096123389834581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3726343258922995706225549 1397378722096123389834581)
                    ·
                      rfl

theorem cell22_4082078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_4082078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082078 prefixEnd_4082078 := by exact prefixLift 4082078
  have htrace : WordTrace (prefixWord ++ tailWord_4082078) baseStart_4082078 baseEnd_4082078 := by
    simpa [prefixWord, tailWord_4082078, baseEnd_4082078] using wordTrace_append hprefix tailTrace_4082078
  have hstable : (prefixWord ++ tailWord_4082078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082078).length < 2 ^ (prefixWord ++ tailWord_4082078).sum := by decide
  have hdescent : baseEnd_4082078 < baseStart_4082078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082085 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 6]
def baseStart_4082085 : Nat := 118140960795 + 4082085 * 2 ^ 59
def prefixEnd_4082085 : Nat := 4983230072969 + 3 ^ 40 * 4082085 * 2
def baseEnd_4082085 : Nat := 465793706113059234969853

theorem tailTrace_4082085 : CollatzResearch.WordTrace tailWord_4082085 prefixEnd_4082085 465793706113059234969853 := by
  unfold tailWord_4082085
  simp only [CollatzResearch.WordTrace]
  refine ⟨148885871416310684458999709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99257247610873789639333139 148885871416310684458999709)
  ·
    refine ⟨55832201781116506672124891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148885871416310684458999709 55832201781116506672124891)
    ·
      refine ⟨83748302671674760008187337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55832201781116506672124891 83748302671674760008187337)
      ·
        refine ⟨62811227003756070006140503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83748302671674760008187337 62811227003756070006140503)
        ·
          refine ⟨94216840505634105009210755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62811227003756070006140503 94216840505634105009210755)
          ·
            refine ⟨141325260758451157513816133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94216840505634105009210755 141325260758451157513816133)
            ·
              refine ⟨26498486392209592033840525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141325260758451157513816133 26498486392209592033840525)
              ·
                refine ⟨9936932397078597012690197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26498486392209592033840525 9936932397078597012690197)
                ·
                  refine ⟨465793706113059234969853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9936932397078597012690197 465793706113059234969853)
                  ·
                    rfl

theorem cell22_4082085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_4082085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082085 prefixEnd_4082085 := by exact prefixLift 4082085
  have htrace : WordTrace (prefixWord ++ tailWord_4082085) baseStart_4082085 baseEnd_4082085 := by
    simpa [prefixWord, tailWord_4082085, baseEnd_4082085] using wordTrace_append hprefix tailTrace_4082085
  have hstable : (prefixWord ++ tailWord_4082085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082085).length < 2 ^ (prefixWord ++ tailWord_4082085).sum := by decide
  have hdescent : baseEnd_4082085 < baseStart_4082085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082087 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 3, 4]
def baseStart_4082087 : Nat := 118140960795 + 4082087 * 2 ^ 59
def prefixEnd_4082087 : Nat := 4983230072969 + 3 ^ 40 * 4082087 * 2
def baseEnd_4082087 : Nat := 1397381802980050366359553

theorem tailTrace_4082087 : CollatzResearch.WordTrace tailWord_4082087 prefixEnd_4082087 1397381802980050366359553 := by
  unfold tailWord_4082087
  simp only [CollatzResearch.WordTrace]
  refine ⟨148885944362303438800572515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99257296241535625867048343 148885944362303438800572515)
  ·
    refine ⟨223328916543455158200858773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148885944362303438800572515 223328916543455158200858773)
    ·
      refine ⟨10468542962974460540665255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 223328916543455158200858773 10468542962974460540665255)
      ·
        refine ⟨15702814444461690810997883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10468542962974460540665255 15702814444461690810997883)
        ·
          refine ⟨23554221666692536216496825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15702814444461690810997883 23554221666692536216496825)
          ·
            refine ⟨17665666250019402162372619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23554221666692536216496825 17665666250019402162372619)
            ·
              refine ⟨26498499375029103243558929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17665666250019402162372619 26498499375029103243558929)
              ·
                refine ⟨19873874531271827432669197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26498499375029103243558929 19873874531271827432669197)
                ·
                  refine ⟨7452702949226935287250949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19873874531271827432669197 7452702949226935287250949)
                  ·
                    refine ⟨1397381802980050366359553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7452702949226935287250949 1397381802980050366359553)
                    ·
                      rfl

theorem cell22_4082087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_4082087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082087 prefixEnd_4082087 := by exact prefixLift 4082087
  have htrace : WordTrace (prefixWord ++ tailWord_4082087) baseStart_4082087 baseEnd_4082087 := by
    simpa [prefixWord, tailWord_4082087, baseEnd_4082087] using wordTrace_append hprefix tailTrace_4082087
  have hstable : (prefixWord ++ tailWord_4082087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082087).length < 2 ^ (prefixWord ++ tailWord_4082087).sum := by decide
  have hdescent : baseEnd_4082087 < baseStart_4082087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082119 : List Nat := [1, 1, 4, 1, 1, 5, 2, 3, 4]
def baseStart_4082119 : Nat := 118140960795 + 4082119 * 2 ^ 59
def prefixEnd_4082119 : Nat := 4983230072969 + 3 ^ 40 * 4082119 * 2
def baseEnd_4082119 : Nat := 465797585744670983186485

theorem tailTrace_4082119 : CollatzResearch.WordTrace tailWord_4082119 prefixEnd_4082119 465797585744670983186485 := by
  unfold tailWord_4082119
  simp only [CollatzResearch.WordTrace]
  refine ⟨148887111498187508265737411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99258074332125005510491607 148887111498187508265737411)
  ·
    refine ⟨223330667247281262398606117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148887111498187508265737411 223330667247281262398606117)
    ·
      refine ⟨41874500108865236699738647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223330667247281262398606117 41874500108865236699738647)
      ·
        refine ⟨62811750163297855049607971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41874500108865236699738647 62811750163297855049607971)
        ·
          refine ⟨94217625244946782574411957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62811750163297855049607971 94217625244946782574411957)
          ·
            refine ⟨8832902366713760866351121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94217625244946782574411957 8832902366713760866351121)
            ·
              refine ⟨6624676775035320649763341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8832902366713760866351121 6624676775035320649763341)
              ·
                refine ⟨2484253790638245243661253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6624676775035320649763341 2484253790638245243661253)
                ·
                  refine ⟨465797585744670983186485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2484253790638245243661253 465797585744670983186485)
                  ·
                    rfl

theorem cell22_4082119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 4].length) (baseStart_4082119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082119 prefixEnd_4082119 := by exact prefixLift 4082119
  have htrace : WordTrace (prefixWord ++ tailWord_4082119) baseStart_4082119 baseEnd_4082119 := by
    simpa [prefixWord, tailWord_4082119, baseEnd_4082119] using wordTrace_append hprefix tailTrace_4082119
  have hstable : (prefixWord ++ tailWord_4082119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082119).length < 2 ^ (prefixWord ++ tailWord_4082119).sum := by decide
  have hdescent : baseEnd_4082119 < baseStart_4082119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082151 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 2, 3]
def baseStart_4082151 : Nat := 118140960795 + 4082151 * 2 ^ 59
def prefixEnd_4082151 : Nat := 4983230072969 + 3 ^ 40 * 4082151 * 2
def baseEnd_4082151 : Nat := 1397403711487975532759357

theorem tailTrace_4082151 : CollatzResearch.WordTrace tailWord_4082151 prefixEnd_4082151 1397403711487975532759357 := by
  unfold tailWord_4082151
  simp only [CollatzResearch.WordTrace]
  refine ⟨148888278634071577730902307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99258852422714385153934871 148888278634071577730902307)
  ·
    refine ⟨223332417951107366596353461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148888278634071577730902307 223332417951107366596353461)
    ·
      refine ⟨20937414182916315618408137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223332417951107366596353461 20937414182916315618408137)
      ·
        refine ⟨15703060637187236713806103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20937414182916315618408137 15703060637187236713806103)
        ·
          refine ⟨23554590955780855070709155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15703060637187236713806103 23554590955780855070709155)
          ·
            refine ⟨35331886433671282606063733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23554590955780855070709155 35331886433671282606063733)
            ·
              refine ⟨3312364353156682744318475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35331886433671282606063733 3312364353156682744318475)
              ·
                refine ⟨4968546529735024116477713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312364353156682744318475 4968546529735024116477713)
                ·
                  refine ⟨3726409897301268087358285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4968546529735024116477713 3726409897301268087358285)
                  ·
                    refine ⟨1397403711487975532759357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3726409897301268087358285 1397403711487975532759357)
                    ·
                      rfl

theorem cell22_4082151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_4082151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082151 prefixEnd_4082151 := by exact prefixLift 4082151
  have htrace : WordTrace (prefixWord ++ tailWord_4082151) baseStart_4082151 baseEnd_4082151 := by
    simpa [prefixWord, tailWord_4082151, baseEnd_4082151] using wordTrace_append hprefix tailTrace_4082151
  have hstable : (prefixWord ++ tailWord_4082151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082151).length < 2 ^ (prefixWord ++ tailWord_4082151).sum := by decide
  have hdescent : baseEnd_4082151 < baseStart_4082151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082175 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 9]
def baseStart_4082175 : Nat := 118140960795 + 4082175 * 2 ^ 59
def prefixEnd_4082175 : Nat := 4983230072969 + 3 ^ 40 * 4082175 * 2
def baseEnd_4082175 : Nat := 465803975726149156719761

theorem tailTrace_4082175 : CollatzResearch.WordTrace tailWord_4082175 prefixEnd_4082175 465803975726149156719761 := by
  unfold tailWord_4082175
  simp only [CollatzResearch.WordTrace]
  refine ⟨148889153985984629829775979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99259435990656419886517319 148889153985984629829775979)
  ·
    refine ⟨223333730978976944744663969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148889153985984629829775979 223333730978976944744663969)
    ·
      refine ⟨167500298234232708558497977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223333730978976944744663969 167500298234232708558497977)
      ·
        refine ⟨125625223675674531418873483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167500298234232708558497977 125625223675674531418873483)
        ·
          refine ⟨188437835513511797128310225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125625223675674531418873483 188437835513511797128310225)
          ·
            refine ⟨141328376635133847846232669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188437835513511797128310225 141328376635133847846232669)
            ·
              refine ⟨52998141238175192942337251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141328376635133847846232669 52998141238175192942337251)
              ·
                refine ⟨79497211857262789413505877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52998141238175192942337251 79497211857262789413505877)
                ·
                  refine ⟨465803975726149156719761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79497211857262789413505877 465803975726149156719761)
                  ·
                    rfl

theorem cell22_4082175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 9].length) (baseStart_4082175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082175 prefixEnd_4082175 := by exact prefixLift 4082175
  have htrace : WordTrace (prefixWord ++ tailWord_4082175) baseStart_4082175 baseEnd_4082175 := by
    simpa [prefixWord, tailWord_4082175, baseEnd_4082175] using wordTrace_append hprefix tailTrace_4082175
  have hstable : (prefixWord ++ tailWord_4082175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082175).length < 2 ^ (prefixWord ++ tailWord_4082175).sum := by decide
  have hdescent : baseEnd_4082175 < baseStart_4082175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082252 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_4082252 : Nat := 118140960795 + 4082252 * 2 ^ 59
def prefixEnd_4082252 : Nat := 4983230072969 + 3 ^ 40 * 4082252 * 2
def baseEnd_4082252 : Nat := 1397438285852044935984047

theorem tailTrace_4082252 : CollatzResearch.WordTrace tailWord_4082252 prefixEnd_4082252 1397438285852044935984047 := by
  unfold tailWord_4082252
  simp only [CollatzResearch.WordTrace]
  refine ⟨74445981203352835990164505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99261308271137114653552673 74445981203352835990164505)
  ·
    refine ⟨55834485902514626992623379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74445981203352835990164505 55834485902514626992623379)
    ·
      refine ⟨83751728853771940488935069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55834485902514626992623379 83751728853771940488935069)
      ·
        refine ⟨31406898320164477683350651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83751728853771940488935069 31406898320164477683350651)
        ·
          refine ⟨47110347480246716525025977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31406898320164477683350651 47110347480246716525025977)
          ·
            refine ⟨35332760610185037393769483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47110347480246716525025977 35332760610185037393769483)
            ·
              refine ⟨52999140915277556090654225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35332760610185037393769483 52999140915277556090654225)
              ·
                refine ⟨39749355686458167067990669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52999140915277556090654225 39749355686458167067990669)
                ·
                  refine ⟨14906008382421812650496501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39749355686458167067990669 14906008382421812650496501)
                  ·
                    refine ⟨1397438285852044935984047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14906008382421812650496501 1397438285852044935984047)
                    ·
                      rfl

theorem cell22_4082252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_4082252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082252 prefixEnd_4082252 := by exact prefixLift 4082252
  have htrace : WordTrace (prefixWord ++ tailWord_4082252) baseStart_4082252 baseEnd_4082252 := by
    simpa [prefixWord, tailWord_4082252, baseEnd_4082252] using wordTrace_append hprefix tailTrace_4082252
  have hstable : (prefixWord ++ tailWord_4082252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082252).length < 2 ^ (prefixWord ++ tailWord_4082252).sum := by decide
  have hdescent : baseEnd_4082252 < baseStart_4082252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082284 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_4082284 : Nat := 118140960795 + 4082284 * 2 ^ 59
def prefixEnd_4082284 : Nat := 4983230072969 + 3 ^ 40 * 4082284 * 2
def baseEnd_4082284 : Nat := 1397449240106007519183949

theorem tailTrace_4082284 : CollatzResearch.WordTrace tailWord_4082284 prefixEnd_4082284 1397449240106007519183949 := by
  unfold tailWord_4082284
  simp only [CollatzResearch.WordTrace]
  refine ⟨74446564771294870722746953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99262086361726494296995937 74446564771294870722746953)
  ·
    refine ⟨55834923578471153042060215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74446564771294870722746953 55834923578471153042060215)
    ·
      refine ⟨83752385367706729563090323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55834923578471153042060215 83752385367706729563090323)
      ·
        refine ⟨125628578051560094344635485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83752385367706729563090323 125628578051560094344635485)
        ·
          refine ⟨47110716769335035379238307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125628578051560094344635485 47110716769335035379238307)
          ·
            refine ⟨70666075154002553068857461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47110716769335035379238307 70666075154002553068857461)
            ·
              refine ⟨6624944545687739350205387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70666075154002553068857461 6624944545687739350205387)
              ·
                refine ⟨9937416818531609025308081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6624944545687739350205387 9937416818531609025308081)
                ·
                  refine ⟨7453062613898706768981061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9937416818531609025308081 7453062613898706768981061)
                  ·
                    refine ⟨1397449240106007519183949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7453062613898706768981061 1397449240106007519183949)
                    ·
                      rfl

theorem cell22_4082284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_4082284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082284 prefixEnd_4082284 := by exact prefixLift 4082284
  have htrace : WordTrace (prefixWord ++ tailWord_4082284) baseStart_4082284 baseEnd_4082284 := by
    simpa [prefixWord, tailWord_4082284, baseEnd_4082284] using wordTrace_append hprefix tailTrace_4082284
  have hstable : (prefixWord ++ tailWord_4082284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082284).length < 2 ^ (prefixWord ++ tailWord_4082284).sum := by decide
  have hdescent : baseEnd_4082284 < baseStart_4082284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082290 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_4082290 : Nat := 118140960795 + 4082290 * 2 ^ 59
def prefixEnd_4082290 : Nat := 4983230072969 + 3 ^ 40 * 4082290 * 2
def baseEnd_4082290 : Nat := 1397451294028625503533931

theorem tailTrace_4082290 : CollatzResearch.WordTrace tailWord_4082290 prefixEnd_4082290 1397451294028625503533931 := by
  unfold tailWord_4082290
  simp only [CollatzResearch.WordTrace]
  refine ⟨37223337095142001117553081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99262232253712002980141549 37223337095142001117553081)
  ·
    refine ⟨27917502821356500838164811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37223337095142001117553081 27917502821356500838164811)
    ·
      refine ⟨41876254232034751257247217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27917502821356500838164811 41876254232034751257247217)
      ·
        refine ⟨31407190674026063442935413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41876254232034751257247217 31407190674026063442935413)
        ·
          refine ⟨2944424125689943447775195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31407190674026063442935413 2944424125689943447775195)
          ·
            refine ⟨4416636188534915171662793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944424125689943447775195 4416636188534915171662793)
            ·
              refine ⟨3312477141401186378747095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416636188534915171662793 3312477141401186378747095)
              ·
                refine ⟨4968715712101779568120643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312477141401186378747095 4968715712101779568120643)
                ·
                  refine ⟨7453073568152669352180965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968715712101779568120643 7453073568152669352180965)
                  ·
                    refine ⟨1397451294028625503533931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7453073568152669352180965 1397451294028625503533931)
                    ·
                      rfl

theorem cell22_4082290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_4082290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082290 prefixEnd_4082290 := by exact prefixLift 4082290
  have htrace : WordTrace (prefixWord ++ tailWord_4082290) baseStart_4082290 baseEnd_4082290 := by
    simpa [prefixWord, tailWord_4082290, baseEnd_4082290] using wordTrace_append hprefix tailTrace_4082290
  have hstable : (prefixWord ++ tailWord_4082290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082290).length < 2 ^ (prefixWord ++ tailWord_4082290).sum := by decide
  have hdescent : baseEnd_4082290 < baseStart_4082290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082365 : List Nat := [1, 4, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_4082365 : Nat := 118140960795 + 4082365 * 2 ^ 59
def prefixEnd_4082365 : Nat := 4983230072969 + 3 ^ 40 * 4082365 * 2
def baseEnd_4082365 : Nat := 1397476968061350307908701

theorem tailTrace_4082365 : CollatzResearch.WordTrace tailWord_4082365 prefixEnd_4082365 1397476968061350307908701 := by
  unfold tailWord_4082365
  simp only [CollatzResearch.WordTrace]
  refine ⟨148896083855296292279192549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99264055903530861519461699 148896083855296292279192549)
  ·
    refine ⟨27918015722868054802348603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148896083855296292279192549 27918015722868054802348603)
    ·
      refine ⟨41877023584302082203522905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27918015722868054802348603 41877023584302082203522905)
      ·
        refine ⟨31407767688226561652642179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41877023584302082203522905 31407767688226561652642179)
        ·
          refine ⟨47111651532339842478963269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31407767688226561652642179 47111651532339842478963269)
          ·
            refine ⟨8833434662313720464805613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47111651532339842478963269 8833434662313720464805613)
            ·
              refine ⟨3312537998367645174302105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8833434662313720464805613 3312537998367645174302105)
              ·
                refine ⟨2484403498775733880726579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312537998367645174302105 2484403498775733880726579)
                ·
                  refine ⟨3726605248163600821089869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484403498775733880726579 3726605248163600821089869)
                  ·
                    refine ⟨1397476968061350307908701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3726605248163600821089869 1397476968061350307908701)
                    ·
                      rfl

theorem cell22_4082365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_4082365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082365 prefixEnd_4082365 := by exact prefixLift 4082365
  have htrace : WordTrace (prefixWord ++ tailWord_4082365) baseStart_4082365 baseEnd_4082365 := by
    simpa [prefixWord, tailWord_4082365, baseEnd_4082365] using wordTrace_append hprefix tailTrace_4082365
  have hstable : (prefixWord ++ tailWord_4082365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082365).length < 2 ^ (prefixWord ++ tailWord_4082365).sum := by decide
  have hdescent : baseEnd_4082365 < baseStart_4082365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082378 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 5]
def baseStart_4082378 : Nat := 118140960795 + 4082378 * 2 ^ 59
def prefixEnd_4082378 : Nat := 4983230072969 + 3 ^ 40 * 4082378 * 2
def baseEnd_4082378 : Nat := 465827139409007535777887

theorem tailTrace_4082378 : CollatzResearch.WordTrace tailWord_4082378 prefixEnd_4082378 465827139409007535777887 := by
  unfold tailWord_4082378
  simp only [CollatzResearch.WordTrace]
  refine ⟨37224139501062298874853947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99264372002832796999610525 37224139501062298874853947)
  ·
    refine ⟨55836209251593448312280921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37224139501062298874853947 55836209251593448312280921)
    ·
      refine ⟨41877156938695086234210691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55836209251593448312280921 41877156938695086234210691)
      ·
        refine ⟨62815735408042629351316037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41877156938695086234210691 62815735408042629351316037)
        ·
          refine ⟨11777950389007993003371757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62815735408042629351316037 11777950389007993003371757)
          ·
            refine ⟨4416731395877997376264409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11777950389007993003371757 4416731395877997376264409)
            ·
              refine ⟨3312548546908498032198307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416731395877997376264409 3312548546908498032198307)
              ·
                refine ⟨4968822820362747048297461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312548546908498032198307 4968822820362747048297461)
                ·
                  refine ⟨465827139409007535777887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4968822820362747048297461 465827139409007535777887)
                  ·
                    rfl

theorem cell22_4082378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_4082378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082378 prefixEnd_4082378 := by exact prefixLift 4082378
  have htrace : WordTrace (prefixWord ++ tailWord_4082378) baseStart_4082378 baseEnd_4082378 := by
    simpa [prefixWord, tailWord_4082378, baseEnd_4082378] using wordTrace_append hprefix tailTrace_4082378
  have hstable : (prefixWord ++ tailWord_4082378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082378).length < 2 ^ (prefixWord ++ tailWord_4082378).sum := by decide
  have hdescent : baseEnd_4082378 < baseStart_4082378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082387 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 1, 11]
def baseStart_4082387 : Nat := 118140960795 + 4082387 * 2 ^ 59
def prefixEnd_4082387 : Nat := 4983230072969 + 3 ^ 40 * 4082387 * 2
def baseEnd_4082387 : Nat := 1397484499110949583858633

theorem tailTrace_4082387 : CollatzResearch.WordTrace tailWord_4082387 prefixEnd_4082387 1397484499110949583858633 := by
  unfold tailWord_4082387
  simp only [CollatzResearch.WordTrace]
  refine ⟨148896886261216590036493415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99264590840811060024328943 148896886261216590036493415)
  ·
    refine ⟨223345329391824885054740123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148896886261216590036493415 223345329391824885054740123)
    ·
      refine ⟨335017994087737327582110185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223345329391824885054740123 335017994087737327582110185)
      ·
        refine ⟨251263495565802995686582639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335017994087737327582110185 251263495565802995686582639)
        ·
          refine ⟨376895243348704493529873959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251263495565802995686582639 376895243348704493529873959)
          ·
            refine ⟨565342865023056740294810939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376895243348704493529873959 565342865023056740294810939)
            ·
              refine ⟨848014297534585110442216409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565342865023056740294810939 848014297534585110442216409)
              ·
                refine ⟨636010723150938832831662307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848014297534585110442216409 636010723150938832831662307)
                ·
                  refine ⟨954016084726408249247493461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636010723150938832831662307 954016084726408249247493461)
                  ·
                    refine ⟨1397484499110949583858633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 954016084726408249247493461 1397484499110949583858633)
                    ·
                      rfl

theorem cell22_4082387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_4082387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082387 prefixEnd_4082387 := by exact prefixLift 4082387
  have htrace : WordTrace (prefixWord ++ tailWord_4082387) baseStart_4082387 baseEnd_4082387 := by
    simpa [prefixWord, tailWord_4082387, baseEnd_4082387] using wordTrace_append hprefix tailTrace_4082387
  have hstable : (prefixWord ++ tailWord_4082387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082387).length < 2 ^ (prefixWord ++ tailWord_4082387).sum := by decide
  have hdescent : baseEnd_4082387 < baseStart_4082387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082391 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 1, 4]
def baseStart_4082391 : Nat := 118140960795 + 4082391 * 2 ^ 59
def prefixEnd_4082391 : Nat := 4983230072969 + 3 ^ 40 * 4082391 * 2
def baseEnd_4082391 : Nat := 1397485868392694906758621

theorem tailTrace_4082391 : CollatzResearch.WordTrace tailWord_4082391 prefixEnd_4082391 1397485868392694906758621 := by
  unfold tailWord_4082391
  simp only [CollatzResearch.WordTrace]
  refine ⟨148897032153202098719639027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99264688102134732479759351 148897032153202098719639027)
  ·
    refine ⟨223345548229803148079458541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148897032153202098719639027 223345548229803148079458541)
    ·
      refine ⟨83754580586176180529796953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223345548229803148079458541 83754580586176180529796953)
      ·
        refine ⟨62815935439632135397347715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83754580586176180529796953 62815935439632135397347715)
        ·
          refine ⟨94223903159448203096021573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62815935439632135397347715 94223903159448203096021573)
          ·
            refine ⟨17666981842396538080504045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94223903159448203096021573 17666981842396538080504045)
            ·
              refine ⟨6625118190898701780189017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17666981842396538080504045 6625118190898701780189017)
              ·
                refine ⟨4968838643174026335141763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6625118190898701780189017 4968838643174026335141763)
                ·
                  refine ⟨7453257964761039502712645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968838643174026335141763 7453257964761039502712645)
                  ·
                    refine ⟨1397485868392694906758621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7453257964761039502712645 1397485868392694906758621)
                    ·
                      rfl

theorem cell22_4082391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_4082391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082391 prefixEnd_4082391 := by exact prefixLift 4082391
  have htrace : WordTrace (prefixWord ++ tailWord_4082391) baseStart_4082391 baseEnd_4082391 := by
    simpa [prefixWord, tailWord_4082391, baseEnd_4082391] using wordTrace_append hprefix tailTrace_4082391
  have hstable : (prefixWord ++ tailWord_4082391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082391).length < 2 ^ (prefixWord ++ tailWord_4082391).sum := by decide
  have hdescent : baseEnd_4082391 < baseStart_4082391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082404 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_4082404 : Nat := 118140960795 + 4082404 * 2 ^ 59
def prefixEnd_4082404 : Nat := 4983230072969 + 3 ^ 40 * 4082404 * 2
def baseEnd_4082404 : Nat := 1397490318558367206183581

theorem tailTrace_4082404 : CollatzResearch.WordTrace tailWord_4082404 prefixEnd_4082404 1397490318558367206183581 := by
  unfold tailWord_4082404
  simp only [CollatzResearch.WordTrace]
  refine ⟨74448753151077500969931133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99265004201436667959908177 74448753151077500969931133)
  ·
    refine ⟨27918282431654062863724175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74448753151077500969931133 27918282431654062863724175)
    ·
      refine ⟨41877423647481094295586263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27918282431654062863724175 41877423647481094295586263)
      ·
        refine ⟨62816135471221641443379395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41877423647481094295586263 62816135471221641443379395)
        ·
          refine ⟨94224203206832462165069093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62816135471221641443379395 94224203206832462165069093)
          ·
            refine ⟨17667038101281086655950455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94224203206832462165069093 17667038101281086655950455)
            ·
              refine ⟨26500557151921629983925683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17667038101281086655950455 26500557151921629983925683)
              ·
                refine ⟨39750835727882444975888525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26500557151921629983925683 39750835727882444975888525)
                ·
                  refine ⟨14906563397955916865958197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39750835727882444975888525 14906563397955916865958197)
                  ·
                    refine ⟨1397490318558367206183581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14906563397955916865958197 1397490318558367206183581)
                    ·
                      rfl

theorem cell22_4082404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_4082404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082404 prefixEnd_4082404 := by exact prefixLift 4082404
  have htrace : WordTrace (prefixWord ++ tailWord_4082404) baseStart_4082404 baseEnd_4082404 := by
    simpa [prefixWord, tailWord_4082404, baseEnd_4082404] using wordTrace_append hprefix tailTrace_4082404
  have hstable : (prefixWord ++ tailWord_4082404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082404).length < 2 ^ (prefixWord ++ tailWord_4082404).sum := by decide
  have hdescent : baseEnd_4082404 < baseStart_4082404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082483 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 3, 3]
def baseStart_4082483 : Nat := 118140960795 + 4082483 * 2 ^ 59
def prefixEnd_4082483 : Nat := 4983230072969 + 3 ^ 40 * 4082483 * 2
def baseEnd_4082483 : Nat := 1397517361872837333458339

theorem tailTrace_4082483 : CollatzResearch.WordTrace tailWord_4082483 prefixEnd_4082483 1397517361872837333458339 := by
  unfold tailWord_4082483
  simp only [CollatzResearch.WordTrace]
  refine ⟨148900387668868798431988103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99266925112579198954658735 148900387668868798431988103)
  ·
    refine ⟨223350581503303197647982155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148900387668868798431988103 223350581503303197647982155)
    ·
      refine ⟨335025872254954796471973233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223350581503303197647982155 335025872254954796471973233)
      ·
        refine ⟨251269404191216097353979925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335025872254954796471973233 251269404191216097353979925)
        ·
          refine ⟨11778253321463254563467809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251269404191216097353979925 11778253321463254563467809)
          ·
            refine ⟨8833689991097440922600857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11778253321463254563467809 8833689991097440922600857)
            ·
              refine ⟨6625267493323080691950643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8833689991097440922600857 6625267493323080691950643)
              ·
                refine ⟨9937901239984621037925965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6625267493323080691950643 9937901239984621037925965)
                ·
                  refine ⟨3726712964994232889222237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9937901239984621037925965 3726712964994232889222237)
                  ·
                    refine ⟨1397517361872837333458339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3726712964994232889222237 1397517361872837333458339)
                    ·
                      rfl

theorem cell22_4082483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 3].length) (baseStart_4082483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082483 prefixEnd_4082483 := by exact prefixLift 4082483
  have htrace : WordTrace (prefixWord ++ tailWord_4082483) baseStart_4082483 baseEnd_4082483 := by
    simpa [prefixWord, tailWord_4082483, baseEnd_4082483] using wordTrace_append hprefix tailTrace_4082483
  have hstable : (prefixWord ++ tailWord_4082483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082483).length < 2 ^ (prefixWord ++ tailWord_4082483).sum := by decide
  have hdescent : baseEnd_4082483 < baseStart_4082483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082502 : List Nat := [6, 1, 1, 2, 2, 2, 2, 6]
def baseStart_4082502 : Nat := 118140960795 + 4082502 * 2 ^ 59
def prefixEnd_4082502 : Nat := 4983230072969 + 3 ^ 40 * 4082502 * 2
def baseEnd_4082502 : Nat := 155280429551236401914809

theorem tailTrace_4082502 : CollatzResearch.WordTrace tailWord_4082502 prefixEnd_4082502 155280429551236401914809 := by
  unfold tailWord_4082502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4653158770493748896154055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99267387103866643117953173 4653158770493748896154055)
  ·
    refine ⟨6979738155740623344231083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4653158770493748896154055 6979738155740623344231083)
    ·
      refine ⟨10469607233610935016346625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6979738155740623344231083 10469607233610935016346625)
      ·
        refine ⟨7852205425208201262259969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10469607233610935016346625 7852205425208201262259969)
        ·
          refine ⟨5889154068906150946694977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7852205425208201262259969 5889154068906150946694977)
          ·
            refine ⟨4416865551679613210021233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5889154068906150946694977 4416865551679613210021233)
            ·
              refine ⟨3312649163759709907515925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416865551679613210021233 3312649163759709907515925)
              ·
                refine ⟨155280429551236401914809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3312649163759709907515925 155280429551236401914809)
                ·
                  rfl

theorem cell22_4082502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_4082502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082502 prefixEnd_4082502 := by exact prefixLift 4082502
  have htrace : WordTrace (prefixWord ++ tailWord_4082502) baseStart_4082502 baseEnd_4082502 := by
    simpa [prefixWord, tailWord_4082502, baseEnd_4082502] using wordTrace_append hprefix tailTrace_4082502
  have hstable : (prefixWord ++ tailWord_4082502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082502).length < 2 ^ (prefixWord ++ tailWord_4082502).sum := by decide
  have hdescent : baseEnd_4082502 < baseStart_4082502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082571 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 2, 4]
def baseStart_4082571 : Nat := 118140960795 + 4082571 * 2 ^ 59
def prefixEnd_4082571 : Nat := 4983230072969 + 3 ^ 40 * 4082571 * 2
def baseEnd_4082571 : Nat := 1397547486071234437258069

theorem tailTrace_4082571 : CollatzResearch.WordTrace tailWord_4082571 prefixEnd_4082571 1397547486071234437258069 := by
  unfold tailWord_4082571
  simp only [CollatzResearch.WordTrace]
  refine ⟨148903597292549989461191567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99269064861699992974127711 148903597292549989461191567)
  ·
    refine ⟨223355395938824984191787351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148903597292549989461191567 223355395938824984191787351)
    ·
      refine ⟨335033093908237476287681027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223355395938824984191787351 335033093908237476287681027)
      ·
        refine ⟨502549640862356214431521541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335033093908237476287681027 502549640862356214431521541)
        ·
          refine ⟨94228057661691790205910289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 502549640862356214431521541 94228057661691790205910289)
          ·
            refine ⟨70671043246268842654432717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94228057661691790205910289 70671043246268842654432717)
            ·
              refine ⟨26501641217350815995412269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70671043246268842654432717 26501641217350815995412269)
              ·
                refine ⟨9938115456506555998279601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26501641217350815995412269 9938115456506555998279601)
                ·
                  refine ⟨7453586592379916998709701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9938115456506555998279601 7453586592379916998709701)
                  ·
                    refine ⟨1397547486071234437258069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7453586592379916998709701 1397547486071234437258069)
                    ·
                      rfl

theorem cell22_4082571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 4].length) (baseStart_4082571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082571 prefixEnd_4082571 := by exact prefixLift 4082571
  have htrace : WordTrace (prefixWord ++ tailWord_4082571) baseStart_4082571 baseEnd_4082571 := by
    simpa [prefixWord, tailWord_4082571, baseEnd_4082571] using wordTrace_append hprefix tailTrace_4082571
  have hstable : (prefixWord ++ tailWord_4082571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082571).length < 2 ^ (prefixWord ++ tailWord_4082571).sum := by decide
  have hdescent : baseEnd_4082571 < baseStart_4082571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082586 : List Nat := [3, 1, 1, 4, 3, 10]
def baseStart_4082586 : Nat := 118140960795 + 4082586 * 2 ^ 59
def prefixEnd_4082586 : Nat := 4983230072969 + 3 ^ 40 * 4082586 * 2
def baseEnd_4082586 : Nat := 17253736060219498742383

theorem tailTrace_4082586 : CollatzResearch.WordTrace tailWord_4082586 prefixEnd_4082586 17253736060219498742383 := by
  unfold tailWord_4082586
  simp only [CollatzResearch.WordTrace]
  refine ⟨37226036096873911755746903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99269429591663764681991741 37226036096873911755746903)
  ·
    refine ⟨55839054145310867633620355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37226036096873911755746903 55839054145310867633620355)
    ·
      refine ⟨83758581217966301450430533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55839054145310867633620355 83758581217966301450430533)
      ·
        refine ⟨15704733978368681521955725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83758581217966301450430533 15704733978368681521955725)
        ·
          refine ⟨5889275241888255570733397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15704733978368681521955725 5889275241888255570733397)
          ·
            refine ⟨17253736060219498742383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5889275241888255570733397 17253736060219498742383)
            ·
              rfl

theorem cell22_4082586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 10].length) (baseStart_4082586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082586 prefixEnd_4082586 := by exact prefixLift 4082586
  have htrace : WordTrace (prefixWord ++ tailWord_4082586) baseStart_4082586 baseEnd_4082586 := by
    simpa [prefixWord, tailWord_4082586, baseEnd_4082586] using wordTrace_append hprefix tailTrace_4082586
  have hstable : (prefixWord ++ tailWord_4082586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082586).length < 2 ^ (prefixWord ++ tailWord_4082586).sum := by decide
  have hdescent : baseEnd_4082586 < baseStart_4082586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082618 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 3, 3]
def baseStart_4082618 : Nat := 118140960795 + 4082618 * 2 ^ 59
def prefixEnd_4082618 : Nat := 4983230072969 + 3 ^ 40 * 4082618 * 2
def baseEnd_4082618 : Nat := 1397563575131741981332925

theorem tailTrace_4082618 : CollatzResearch.WordTrace tailWord_4082618 prefixEnd_4082618 1397563575131741981332925 := by
  unfold tailWord_4082618
  simp only [CollatzResearch.WordTrace]
  refine ⟨37226327880844929122038127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99270207682253144325435005 37226327880844929122038127)
  ·
    refine ⟨55839491821267393683057191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37226327880844929122038127 55839491821267393683057191)
    ·
      refine ⟨83759237731901090524585787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55839491821267393683057191 83759237731901090524585787)
      ·
        refine ⟨125638856597851635786878681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83759237731901090524585787 125638856597851635786878681)
        ·
          refine ⟨94229142448388726840159011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125638856597851635786878681 94229142448388726840159011)
          ·
            refine ⟨141343713672583090260238517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94229142448388726840159011 141343713672583090260238517)
            ·
              refine ⟨13250973156804664711897361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141343713672583090260238517 13250973156804664711897361)
              ·
                refine ⟨9938229867603498533923021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13250973156804664711897361 9938229867603498533923021)
                ·
                  refine ⟨3726836200351311950221133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9938229867603498533923021 3726836200351311950221133)
                  ·
                    refine ⟨1397563575131741981332925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3726836200351311950221133 1397563575131741981332925)
                    ·
                      rfl

theorem cell22_4082618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_4082618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082618 prefixEnd_4082618 := by exact prefixLift 4082618
  have htrace : WordTrace (prefixWord ++ tailWord_4082618) baseStart_4082618 baseEnd_4082618 := by
    simpa [prefixWord, tailWord_4082618, baseEnd_4082618] using wordTrace_append hprefix tailTrace_4082618
  have hstable : (prefixWord ++ tailWord_4082618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082618).length < 2 ^ (prefixWord ++ tailWord_4082618).sum := by decide
  have hdescent : baseEnd_4082618 < baseStart_4082618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082635 : List Nat := [1, 1, 1, 1, 3, 5, 1, 5, 1, 3]
def baseStart_4082635 : Nat := 118140960795 + 4082635 * 2 ^ 59
def prefixEnd_4082635 : Nat := 4983230072969 + 3 ^ 40 * 4082635 * 2
def baseEnd_4082635 : Nat := 1397569394579159603657873

theorem tailTrace_4082635 : CollatzResearch.WordTrace tailWord_4082635 prefixEnd_4082635 1397569394579159603657873 := by
  unfold tailWord_4082635
  simp only [CollatzResearch.WordTrace]
  refine ⟨148905931564318128391521359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99270621042878752261014239 148905931564318128391521359)
  ·
    refine ⟨223358897346477192587282039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148905931564318128391521359 223358897346477192587282039)
    ·
      refine ⟨335038346019715788880923059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223358897346477192587282039 335038346019715788880923059)
      ·
        refine ⟨502557519029573683321384589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335038346019715788880923059 502557519029573683321384589)
        ·
          refine ⟨188459069636090131245519221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502557519029573683321384589 188459069636090131245519221)
          ·
            refine ⟨17668037778383449804267427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188459069636090131245519221 17668037778383449804267427)
            ·
              refine ⟨26502056667575174706401141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17668037778383449804267427 26502056667575174706401141)
              ·
                refine ⟨2484567812585172628725107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26502056667575174706401141 2484567812585172628725107)
                ·
                  refine ⟨3726851718877758943087661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484567812585172628725107 3726851718877758943087661)
                  ·
                    refine ⟨1397569394579159603657873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3726851718877758943087661 1397569394579159603657873)
                    ·
                      rfl

theorem cell22_4082635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 1, 3].length) (baseStart_4082635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082635 prefixEnd_4082635 := by exact prefixLift 4082635
  have htrace : WordTrace (prefixWord ++ tailWord_4082635) baseStart_4082635 baseEnd_4082635 := by
    simpa [prefixWord, tailWord_4082635, baseEnd_4082635] using wordTrace_append hprefix tailTrace_4082635
  have hstable : (prefixWord ++ tailWord_4082635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082635).length < 2 ^ (prefixWord ++ tailWord_4082635).sum := by decide
  have hdescent : baseEnd_4082635 < baseStart_4082635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082637 : List Nat := [1, 6, 3, 1, 1, 1, 9]
def baseStart_4082637 : Nat := 118140960795 + 4082637 * 2 ^ 59
def prefixEnd_4082637 : Nat := 4983230072969 + 3 ^ 40 * 4082637 * 2
def baseEnd_4082637 : Nat := 51761854785927120929921

theorem tailTrace_4082637 : CollatzResearch.WordTrace tailWord_4082637 prefixEnd_4082637 51761854785927120929921 := by
  unfold tailWord_4082637
  simp only [CollatzResearch.WordTrace]
  refine ⟨148906004510310882733094165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99270669673540588488729443 148906004510310882733094165)
  ·
    refine ⟨6979968961420822628113789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148906004510310882733094165 6979968961420822628113789)
    ·
      refine ⟨2617488360532808485542671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6979968961420822628113789 2617488360532808485542671)
      ·
        refine ⟨3926232540799212728314007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2617488360532808485542671 3926232540799212728314007)
        ·
          refine ⟨5889348811198819092471011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3926232540799212728314007 5889348811198819092471011)
          ·
            refine ⟨8834023216798228638706517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5889348811198819092471011 8834023216798228638706517)
            ·
              refine ⟨51761854785927120929921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8834023216798228638706517 51761854785927120929921)
              ·
                rfl

theorem cell22_4082637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 9].length) (baseStart_4082637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082637 prefixEnd_4082637 := by exact prefixLift 4082637
  have htrace : WordTrace (prefixWord ++ tailWord_4082637) baseStart_4082637 baseEnd_4082637 := by
    simpa [prefixWord, tailWord_4082637, baseEnd_4082637] using wordTrace_append hprefix tailTrace_4082637
  have hstable : (prefixWord ++ tailWord_4082637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082637).length < 2 ^ (prefixWord ++ tailWord_4082637).sum := by decide
  have hdescent : baseEnd_4082637 < baseStart_4082637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082648 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 5]
def baseStart_4082648 : Nat := 118140960795 + 4082648 * 2 ^ 59
def prefixEnd_4082648 : Nat := 4983230072969 + 3 ^ 40 * 4082648 * 2
def baseEnd_4082648 : Nat := 465857948248277301027611

theorem tailTrace_4082648 : CollatzResearch.WordTrace tailWord_4082648 prefixEnd_4082648 465857948248277301027611 := by
  unfold tailWord_4082648
  simp only [CollatzResearch.WordTrace]
  refine ⟨74453202856635515805872299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99270937142180687741163065 74453202856635515805872299)
  ·
    refine ⟨111679804284953273708808449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74453202856635515805872299 111679804284953273708808449)
    ·
      refine ⟨83759853213714955281606337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111679804284953273708808449 83759853213714955281606337)
      ·
        refine ⟨62819889910286216461204753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83759853213714955281606337 62819889910286216461204753)
        ·
          refine ⟨47114917432714662345903565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62819889910286216461204753 47114917432714662345903565)
          ·
            refine ⟨17668094037267998379713837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47114917432714662345903565 17668094037267998379713837)
            ·
              refine ⟨6625535263975499392392689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17668094037267998379713837 6625535263975499392392689)
              ·
                refine ⟨4969151447981624544294517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6625535263975499392392689 4969151447981624544294517)
                ·
                  refine ⟨465857948248277301027611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4969151447981624544294517 465857948248277301027611)
                  ·
                    rfl

theorem cell22_4082648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_4082648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082648 prefixEnd_4082648 := by exact prefixLift 4082648
  have htrace : WordTrace (prefixWord ++ tailWord_4082648) baseStart_4082648 baseEnd_4082648 := by
    simpa [prefixWord, tailWord_4082648, baseEnd_4082648] using wordTrace_append hprefix tailTrace_4082648
  have hstable : (prefixWord ++ tailWord_4082648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082648).length < 2 ^ (prefixWord ++ tailWord_4082648).sum := by decide
  have hdescent : baseEnd_4082648 < baseStart_4082648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082663 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 2, 5]
def baseStart_4082663 : Nat := 118140960795 + 4082663 * 2 ^ 59
def prefixEnd_4082663 : Nat := 4983230072969 + 3 ^ 40 * 4082663 * 2
def baseEnd_4082663 : Nat := 1397578979551376863957787

theorem tailTrace_4082663 : CollatzResearch.WordTrace tailWord_4082663 prefixEnd_4082663 1397578979551376863957787 := by
  unfold tailWord_4082663
  simp only [CollatzResearch.WordTrace]
  refine ⟨148906952808216689173540643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99271301872144459449027095 148906952808216689173540643)
  ·
    refine ⟨223360429212325033760310965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148906952808216689173540643 223360429212325033760310965)
    ·
      refine ⟨20940040238655471915029153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223360429212325033760310965 20940040238655471915029153)
      ·
        refine ⟨15705030178991603936271865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20940040238655471915029153 15705030178991603936271865)
        ·
          refine ⟨11778772634243702952203899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15705030178991603936271865 11778772634243702952203899)
          ·
            refine ⟨17668158951365554428305849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11778772634243702952203899 17668158951365554428305849)
            ·
              refine ⟨13251119213524165821229387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17668158951365554428305849 13251119213524165821229387)
              ·
                refine ⟨19876678820286248731844081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13251119213524165821229387 19876678820286248731844081)
                ·
                  refine ⟨14907509115214686548883061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19876678820286248731844081 14907509115214686548883061)
                  ·
                    refine ⟨1397578979551376863957787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14907509115214686548883061 1397578979551376863957787)
                    ·
                      rfl

theorem cell22_4082663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_4082663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082663 prefixEnd_4082663 := by exact prefixLift 4082663
  have htrace : WordTrace (prefixWord ++ tailWord_4082663) baseStart_4082663 baseEnd_4082663 := by
    simpa [prefixWord, tailWord_4082663, baseEnd_4082663] using wordTrace_append hprefix tailTrace_4082663
  have hstable : (prefixWord ++ tailWord_4082663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082663).length < 2 ^ (prefixWord ++ tailWord_4082663).sum := by decide
  have hdescent : baseEnd_4082663 < baseStart_4082663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082686 : List Nat := [4, 2, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_4082686 : Nat := 118140960795 + 4082686 * 2 ^ 59
def prefixEnd_4082686 : Nat := 4983230072969 + 3 ^ 40 * 4082686 * 2
def baseEnd_4082686 : Nat := 1397586852921412470632717

theorem tailTrace_4082686 : CollatzResearch.WordTrace tailWord_4082686 prefixEnd_4082686 1397586852921412470632717 := by
  unfold tailWord_4082686
  simp only [CollatzResearch.WordTrace]
  refine ⟨18613473960891670512703489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99271861124755576067751941 18613473960891670512703489)
  ·
    refine ⟨13960105470668752884527617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18613473960891670512703489 13960105470668752884527617)
    ·
      refine ⟨10470079103001564663395713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13960105470668752884527617 10470079103001564663395713)
      ·
        refine ⟨7852559327251173497546785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10470079103001564663395713 7852559327251173497546785)
        ·
          refine ⟨5889419495438380123160089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7852559327251173497546785 5889419495438380123160089)
          ·
            refine ⟨4417064621578785092370067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5889419495438380123160089 4417064621578785092370067)
            ·
              refine ⟨6625596932368177638555101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417064621578785092370067 6625596932368177638555101)
              ·
                refine ⟨2484598849638066614458163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6625596932368177638555101 2484598849638066614458163)
                ·
                  refine ⟨3726898274457099921687245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484598849638066614458163 3726898274457099921687245)
                  ·
                    refine ⟨1397586852921412470632717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3726898274457099921687245 1397586852921412470632717)
                    ·
                      rfl

theorem cell22_4082686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_4082686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082686 prefixEnd_4082686 := by exact prefixLift 4082686
  have htrace : WordTrace (prefixWord ++ tailWord_4082686) baseStart_4082686 baseEnd_4082686 := by
    simpa [prefixWord, tailWord_4082686, baseEnd_4082686] using wordTrace_append hprefix tailTrace_4082686
  have hstable : (prefixWord ++ tailWord_4082686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082686).length < 2 ^ (prefixWord ++ tailWord_4082686).sum := by decide
  have hdescent : baseEnd_4082686 < baseStart_4082686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082725 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 2, 3]
def baseStart_4082725 : Nat := 118140960795 + 4082725 * 2 ^ 59
def prefixEnd_4082725 : Nat := 4983230072969 + 3 ^ 40 * 4082725 * 2
def baseEnd_4082725 : Nat := 1397600203418429368907597

theorem tailTrace_4082725 : CollatzResearch.WordTrace tailWord_4082725 prefixEnd_4082725 1397600203418429368907597 := by
  unfold tailWord_4082725
  simp only [CollatzResearch.WordTrace]
  refine ⟨148909214133992073762297629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99272809422661382508198419 148909214133992073762297629)
  ·
    refine ⟨55840955300247027660861611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148909214133992073762297629 55840955300247027660861611)
    ·
      refine ⟨83761432950370541491292417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55840955300247027660861611 83761432950370541491292417)
      ·
        refine ⟨62821074712777906118469313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83761432950370541491292417 62821074712777906118469313)
        ·
          refine ⟨47115806034583429588851985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62821074712777906118469313 47115806034583429588851985)
          ·
            refine ⟨35336854525937572191638989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47115806034583429588851985 35336854525937572191638989)
            ·
              refine ⟨13251320447226589571864621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35336854525937572191638989 13251320447226589571864621)
              ·
                refine ⟨4969245167709971089449233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13251320447226589571864621 4969245167709971089449233)
                ·
                  refine ⟨3726933875782478317086925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4969245167709971089449233 3726933875782478317086925)
                  ·
                    refine ⟨1397600203418429368907597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3726933875782478317086925 1397600203418429368907597)
                    ·
                      rfl

theorem cell22_4082725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_4082725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082725 prefixEnd_4082725 := by exact prefixLift 4082725
  have htrace : WordTrace (prefixWord ++ tailWord_4082725) baseStart_4082725 baseEnd_4082725 := by
    simpa [prefixWord, tailWord_4082725, baseEnd_4082725] using wordTrace_append hprefix tailTrace_4082725
  have hstable : (prefixWord ++ tailWord_4082725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082725).length < 2 ^ (prefixWord ++ tailWord_4082725).sum := by decide
  have hdescent : baseEnd_4082725 < baseStart_4082725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082783 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 5]
def baseStart_4082783 : Nat := 118140960795 + 4082783 * 2 ^ 59
def prefixEnd_4082783 : Nat := 4983230072969 + 3 ^ 40 * 4082783 * 2
def baseEnd_4082783 : Nat := 465873352667912183652473

theorem tailTrace_4082783 : CollatzResearch.WordTrace tailWord_4082783 prefixEnd_4082783 465873352667912183652473 := by
  unfold tailWord_4082783
  simp only [CollatzResearch.WordTrace]
  refine ⟨148911329567781949667909003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99274219711854633111939335 148911329567781949667909003)
  ·
    refine ⟨223366994351672924501863505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148911329567781949667909003 223366994351672924501863505)
    ·
      refine ⟨167525245763754693376397629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223366994351672924501863505 167525245763754693376397629)
      ·
        refine ⟨62821967161408010016149111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167525245763754693376397629 62821967161408010016149111)
        ·
          refine ⟨94232950742112015024223667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62821967161408010016149111 94232950742112015024223667)
          ·
            refine ⟨141349426113168022536335501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94232950742112015024223667 141349426113168022536335501)
            ·
              refine ⟨53006034792438008451125813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141349426113168022536335501 53006034792438008451125813)
              ·
                refine ⟨4969315761791063292293045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53006034792438008451125813 4969315761791063292293045)
                ·
                  refine ⟨465873352667912183652473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4969315761791063292293045 465873352667912183652473)
                  ·
                    rfl

theorem cell22_4082783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 5].length) (baseStart_4082783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082783 prefixEnd_4082783 := by exact prefixLift 4082783
  have htrace : WordTrace (prefixWord ++ tailWord_4082783) baseStart_4082783 baseEnd_4082783 := by
    simpa [prefixWord, tailWord_4082783, baseEnd_4082783] using wordTrace_append hprefix tailTrace_4082783
  have hstable : (prefixWord ++ tailWord_4082783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082783).length < 2 ^ (prefixWord ++ tailWord_4082783).sum := by decide
  have hdescent : baseEnd_4082783 < baseStart_4082783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082817 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 5]
def baseStart_4082817 : Nat := 118140960795 + 4082817 * 2 ^ 59
def prefixEnd_4082817 : Nat := 4983230072969 + 3 ^ 40 * 4082817 * 2
def baseEnd_4082817 : Nat := 465877232299523931869105

theorem tailTrace_4082817 : CollatzResearch.WordTrace tailWord_4082817 prefixEnd_4082817 465877232299523931869105 := by
  unfold tailWord_4082817
  simp only [CollatzResearch.WordTrace]
  refine ⟨148912569649658773474646705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99275046433105848983097803 148912569649658773474646705)
  ·
    refine ⟨111684427237244080105985029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148912569649658773474646705 111684427237244080105985029)
    ·
      refine ⟨20940830106983265019872193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111684427237244080105985029 20940830106983265019872193)
      ·
        refine ⟨15705622580237448764904145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20940830106983265019872193 15705622580237448764904145)
        ·
          refine ⟨11779216935178086573678109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15705622580237448764904145 11779216935178086573678109)
          ·
            refine ⟨4417206350691782465129291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11779216935178086573678109 4417206350691782465129291)
            ·
              refine ⟨6625809526037673697693937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417206350691782465129291 6625809526037673697693937)
              ·
                refine ⟨4969357144528255273270453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6625809526037673697693937 4969357144528255273270453)
                ·
                  refine ⟨465877232299523931869105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4969357144528255273270453 465877232299523931869105)
                  ·
                    rfl

theorem cell22_4082817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 5].length) (baseStart_4082817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082817 prefixEnd_4082817 := by exact prefixLift 4082817
  have htrace : WordTrace (prefixWord ++ tailWord_4082817) baseStart_4082817 baseEnd_4082817 := by
    simpa [prefixWord, tailWord_4082817, baseEnd_4082817] using wordTrace_append hprefix tailTrace_4082817
  have hstable : (prefixWord ++ tailWord_4082817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082817).length < 2 ^ (prefixWord ++ tailWord_4082817).sum := by decide
  have hdescent : baseEnd_4082817 < baseStart_4082817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082873 : List Nat := [1, 2, 1, 4, 1, 3, 10]
def baseStart_4082873 : Nat := 118140960795 + 4082873 * 2 ^ 59
def prefixEnd_4082873 : Nat := 4983230072969 + 3 ^ 40 * 4082873 * 2
def baseEnd_4082873 : Nat := 51764846920111345044709

theorem tailTrace_4082873 : CollatzResearch.WordTrace tailWord_4082873 prefixEnd_4082873 51764846920111345044709 := by
  unfold tailWord_4082873
  simp only [CollatzResearch.WordTrace]
  refine ⟨148914612137455895038685273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99276408091637263359123515 148914612137455895038685273)
  ·
    refine ⟨111685959103091921279013955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148914612137455895038685273 111685959103091921279013955)
    ·
      refine ⟨167528938654637881918520933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111685959103091921279013955 167528938654637881918520933)
      ·
        refine ⟨31411675997744602859722675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167528938654637881918520933 31411675997744602859722675)
        ·
          refine ⟨47117513996616904289584013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31411675997744602859722675 47117513996616904289584013)
          ·
            refine ⟨17669067748731339108594005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47117513996616904289584013 17669067748731339108594005)
            ·
              refine ⟨51764846920111345044709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17669067748731339108594005 51764846920111345044709)
              ·
                rfl

theorem cell22_4082873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 10].length) (baseStart_4082873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082873 prefixEnd_4082873 := by exact prefixLift 4082873
  have htrace : WordTrace (prefixWord ++ tailWord_4082873) baseStart_4082873 baseEnd_4082873 := by
    simpa [prefixWord, tailWord_4082873, baseEnd_4082873] using wordTrace_append hprefix tailTrace_4082873
  have hstable : (prefixWord ++ tailWord_4082873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082873).length < 2 ^ (prefixWord ++ tailWord_4082873).sum := by decide
  have hdescent : baseEnd_4082873 < baseStart_4082873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082890 : List Nat := [3, 1, 2, 1, 3, 3, 2, 7]
def baseStart_4082890 : Nat := 118140960795 + 4082890 * 2 ^ 59
def prefixEnd_4082890 : Nat := 4983230072969 + 3 ^ 40 * 4082890 * 2
def baseEnd_4082890 : Nat := 155295187365602659836899

theorem tailTrace_4082890 : CollatzResearch.WordTrace tailWord_4082890 prefixEnd_4082890 155295187365602659836899 := by
  unfold tailWord_4082890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37228808044598576735513531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99276821452262871294702749 37228808044598576735513531)
  ·
    refine ⟨55843212066897865103270297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37228808044598576735513531 55843212066897865103270297)
    ·
      refine ⟨41882409050173398827452723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55843212066897865103270297 41882409050173398827452723)
      ·
        refine ⟨62823613575260098241179085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41882409050173398827452723 62823613575260098241179085)
        ·
          refine ⟨23558855090722536840442157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62823613575260098241179085 23558855090722536840442157)
          ·
            refine ⟨8834570659020951315165809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23558855090722536840442157 8834570659020951315165809)
            ·
              refine ⟨6625927994265713486374357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8834570659020951315165809 6625927994265713486374357)
              ·
                refine ⟨155295187365602659836899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6625927994265713486374357 155295187365602659836899)
                ·
                  rfl

theorem cell22_4082890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_4082890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082890 prefixEnd_4082890 := by exact prefixLift 4082890
  have htrace : WordTrace (prefixWord ++ tailWord_4082890) baseStart_4082890 baseEnd_4082890 := by
    simpa [prefixWord, tailWord_4082890, baseEnd_4082890] using wordTrace_append hprefix tailTrace_4082890
  have hstable : (prefixWord ++ tailWord_4082890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082890).length < 2 ^ (prefixWord ++ tailWord_4082890).sum := by decide
  have hdescent : baseEnd_4082890 < baseStart_4082890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082894 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_4082894 : Nat := 118140960795 + 4082894 * 2 ^ 59
def prefixEnd_4082894 : Nat := 4983230072969 + 3 ^ 40 * 4082894 * 2
def baseEnd_4082894 : Nat := 1397658055572169261432079

theorem tailTrace_4082894 : CollatzResearch.WordTrace tailWord_4082894 prefixEnd_4082894 1397658055572169261432079 := by
  unfold tailWord_4082894
  simp only [CollatzResearch.WordTrace]
  refine ⟨18614422258797476953149967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99276918713586543750133157 18614422258797476953149967)
  ·
    refine ⟨27921633388196215429724951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18614422258797476953149967 27921633388196215429724951)
    ·
      refine ⟨41882450082294323144587427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27921633388196215429724951 41882450082294323144587427)
      ·
        refine ⟨62823675123441484716881141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41882450082294323144587427 62823675123441484716881141)
        ·
          refine ⟨5889719542822639192207607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62823675123441484716881141 5889719542822639192207607)
          ·
            refine ⟨8834579314233958788311411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5889719542822639192207607 8834579314233958788311411)
            ·
              refine ⟨13251868971350938182467117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834579314233958788311411 13251868971350938182467117)
              ·
                refine ⟨4969450864256601818425169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13251868971350938182467117 4969450864256601818425169)
                ·
                  refine ⟨3727088148192451363818877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4969450864256601818425169 3727088148192451363818877)
                  ·
                    refine ⟨1397658055572169261432079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3727088148192451363818877 1397658055572169261432079)
                    ·
                      rfl

theorem cell22_4082894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_4082894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082894 prefixEnd_4082894 := by exact prefixLift 4082894
  have htrace : WordTrace (prefixWord ++ tailWord_4082894) baseStart_4082894 baseEnd_4082894 := by
    simpa [prefixWord, tailWord_4082894, baseEnd_4082894] using wordTrace_append hprefix tailTrace_4082894
  have hstable : (prefixWord ++ tailWord_4082894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082894).length < 2 ^ (prefixWord ++ tailWord_4082894).sum := by decide
  have hdescent : baseEnd_4082894 < baseStart_4082894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082905 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 5, 3]
def baseStart_4082905 : Nat := 118140960795 + 4082905 * 2 ^ 59
def prefixEnd_4082905 : Nat := 4983230072969 + 3 ^ 40 * 4082905 * 2
def baseEnd_4082905 : Nat := 1397661821096968899407045

theorem tailTrace_4082905 : CollatzResearch.WordTrace tailWord_4082905 prefixEnd_4082905 1397661821096968899407045 := by
  unfold tailWord_4082905
  simp only [CollatzResearch.WordTrace]
  refine ⟨148915779273339964503850169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99277186182226643002566779 148915779273339964503850169)
  ·
    refine ⟨111686834455004973377887627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148915779273339964503850169 111686834455004973377887627)
    ·
      refine ⟨167530251682507460066831441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111686834455004973377887627 167530251682507460066831441)
      ·
        refine ⟨125647688761880595050123581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167530251682507460066831441 125647688761880595050123581)
        ·
          refine ⟨47117883285705223143796343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125647688761880595050123581 47117883285705223143796343)
          ·
            refine ⟨70676824928557834715694515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47117883285705223143796343 70676824928557834715694515)
            ·
              refine ⟨106015237392836752073541773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70676824928557834715694515 106015237392836752073541773)
              ·
                refine ⟨39755714022313782027578165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106015237392836752073541773 39755714022313782027578165)
                ·
                  refine ⟨3727098189591917065085453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39755714022313782027578165 3727098189591917065085453)
                  ·
                    refine ⟨1397661821096968899407045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3727098189591917065085453 1397661821096968899407045)
                    ·
                      rfl

theorem cell22_4082905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 3].length) (baseStart_4082905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082905 prefixEnd_4082905 := by exact prefixLift 4082905
  have htrace : WordTrace (prefixWord ++ tailWord_4082905) baseStart_4082905 baseEnd_4082905 := by
    simpa [prefixWord, tailWord_4082905, baseEnd_4082905] using wordTrace_append hprefix tailTrace_4082905
  have hstable : (prefixWord ++ tailWord_4082905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082905).length < 2 ^ (prefixWord ++ tailWord_4082905).sum := by decide
  have hdescent : baseEnd_4082905 < baseStart_4082905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082909 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_4082909 : Nat := 118140960795 + 4082909 * 2 ^ 59
def prefixEnd_4082909 : Nat := 4983230072969 + 3 ^ 40 * 4082909 * 2
def baseEnd_4082909 : Nat := 1397663190378714222307033

theorem tailTrace_4082909 : CollatzResearch.WordTrace tailWord_4082909 prefixEnd_4082909 1397663190378714222307033 := by
  unfold tailWord_4082909
  simp only [CollatzResearch.WordTrace]
  refine ⟨148915925165325473186995781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99277283443550315457997187 148915925165325473186995781)
  ·
    refine ⟨27921735968498526222561709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148915925165325473186995781 27921735968498526222561709)
    ·
      refine ⟨10470650988186947333460641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27921735968498526222561709 10470650988186947333460641)
      ·
        refine ⟨7852988241140210500095481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10470650988186947333460641 7852988241140210500095481)
        ·
          refine ⟨5889741180855157875071611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7852988241140210500095481 5889741180855157875071611)
          ·
            refine ⟨8834611771282736812607417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5889741180855157875071611 8834611771282736812607417)
            ·
              refine ⟨6625958828462052609455563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8834611771282736812607417 6625958828462052609455563)
              ·
                refine ⟨9938938242693078914183345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6625958828462052609455563 9938938242693078914183345)
                ·
                  refine ⟨7454203682019809185637509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9938938242693078914183345 7454203682019809185637509)
                  ·
                    refine ⟨1397663190378714222307033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7454203682019809185637509 1397663190378714222307033)
                    ·
                      rfl

theorem cell22_4082909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_4082909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082909 prefixEnd_4082909 := by exact prefixLift 4082909
  have htrace : WordTrace (prefixWord ++ tailWord_4082909) baseStart_4082909 baseEnd_4082909 := by
    simpa [prefixWord, tailWord_4082909, baseEnd_4082909] using wordTrace_append hprefix tailTrace_4082909
  have hstable : (prefixWord ++ tailWord_4082909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082909).length < 2 ^ (prefixWord ++ tailWord_4082909).sum := by decide
  have hdescent : baseEnd_4082909 < baseStart_4082909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082980 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 8]
def baseStart_4082980 : Nat := 118140960795 + 4082980 * 2 ^ 59
def prefixEnd_4082980 : Nat := 4983230072969 + 3 ^ 40 * 4082980 * 2
def baseEnd_4082980 : Nat := 465895831709897901260605

theorem tailTrace_4082980 : CollatzResearch.WordTrace tailWord_4082980 prefixEnd_4082980 465895831709897901260605 := by
  unfold tailWord_4082980
  simp only [CollatzResearch.WordTrace]
  refine ⟨74459257374034126156415197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99279009832045501541886929 74459257374034126156415197)
  ·
    refine ⟨27922221515262797308655699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74459257374034126156415197 27922221515262797308655699)
    ·
      refine ⟨41883332272894195962983549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27922221515262797308655699 41883332272894195962983549)
      ·
        refine ⟨15706249602335323486118831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41883332272894195962983549 15706249602335323486118831)
        ·
          refine ⟨23559374403502985229178247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15706249602335323486118831 23559374403502985229178247)
          ·
            refine ⟨35339061605254477843767371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23559374403502985229178247 35339061605254477843767371)
            ·
              refine ⟨53008592407881716765651057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35339061605254477843767371 53008592407881716765651057)
              ·
                refine ⟨39756444305911287574238293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53008592407881716765651057 39756444305911287574238293)
                ·
                  refine ⟨465895831709897901260605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39756444305911287574238293 465895831709897901260605)
                  ·
                    rfl

theorem cell22_4082980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_4082980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082980 prefixEnd_4082980 := by exact prefixLift 4082980
  have htrace : WordTrace (prefixWord ++ tailWord_4082980) baseStart_4082980 baseEnd_4082980 := by
    simpa [prefixWord, tailWord_4082980, baseEnd_4082980] using wordTrace_append hprefix tailTrace_4082980
  have hstable : (prefixWord ++ tailWord_4082980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082980).length < 2 ^ (prefixWord ++ tailWord_4082980).sum := by decide
  have hdescent : baseEnd_4082980 < baseStart_4082980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082997 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 6]
def baseStart_4082997 : Nat := 118140960795 + 4082997 * 2 ^ 59
def prefixEnd_4082997 : Nat := 4983230072969 + 3 ^ 40 * 4082997 * 2
def baseEnd_4082997 : Nat := 465897771525703775368921

theorem tailTrace_4082997 : CollatzResearch.WordTrace tailWord_4082997 prefixEnd_4082997 465897771525703775368921 := by
  unfold tailWord_4082997
  simp only [CollatzResearch.WordTrace]
  refine ⟨148919134789006664216199245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99279423192671109477466163 148919134789006664216199245)
  ·
    refine ⟨55844675545877499081074717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148919134789006664216199245 55844675545877499081074717)
    ·
      refine ⟨20941753329704062155403019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55844675545877499081074717 20941753329704062155403019)
      ·
        refine ⟨31412629994556093233104529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20941753329704062155403019 31412629994556093233104529)
        ·
          refine ⟨23559472495917069924828397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31412629994556093233104529 23559472495917069924828397)
          ·
            refine ⟨8834802185968901221810649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23559472495917069924828397 8834802185968901221810649)
            ·
              refine ⟨6626101639476675916357987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8834802185968901221810649 6626101639476675916357987)
              ·
                refine ⟨9939152459215013874536981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6626101639476675916357987 9939152459215013874536981)
                ·
                  refine ⟨465897771525703775368921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9939152459215013874536981 465897771525703775368921)
                  ·
                    rfl

theorem cell22_4082997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_4082997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4082997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4082997 prefixEnd_4082997 := by exact prefixLift 4082997
  have htrace : WordTrace (prefixWord ++ tailWord_4082997) baseStart_4082997 baseEnd_4082997 := by
    simpa [prefixWord, tailWord_4082997, baseEnd_4082997] using wordTrace_append hprefix tailTrace_4082997
  have hstable : (prefixWord ++ tailWord_4082997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082997).length < 2 ^ (prefixWord ++ tailWord_4082997).sum := by decide
  have hdescent : baseEnd_4082997 < baseStart_4082997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083025 : List Nat := [1, 2, 2, 1, 4, 1, 3, 8]
def baseStart_4083025 : Nat := 118140960795 + 4083025 * 2 ^ 59
def prefixEnd_4083025 : Nat := 4983230072969 + 3 ^ 40 * 4083025 * 2
def baseEnd_4083025 : Nat := 155300322172147620711853

theorem tailTrace_4083025 : CollatzResearch.WordTrace tailWord_4083025 prefixEnd_4083025 155300322172147620711853 := by
  unfold tailWord_4083025
  simp only [CollatzResearch.WordTrace]
  refine ⟨148920156032905224998218529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99280104021936816665479019 148920156032905224998218529)
  ·
    refine ⟨111690117024678918748663897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148920156032905224998218529 111690117024678918748663897)
    ·
      refine ⟨83767587768509189061497923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111690117024678918748663897 83767587768509189061497923)
      ·
        refine ⟨125651381652763783592246885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83767587768509189061497923 125651381652763783592246885)
        ·
          refine ⟨23559634059893209423546291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125651381652763783592246885 23559634059893209423546291)
          ·
            refine ⟨35339451089839814135319437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23559634059893209423546291 35339451089839814135319437)
            ·
              refine ⟨13252294158689930300744789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35339451089839814135319437 13252294158689930300744789)
              ·
                refine ⟨155300322172147620711853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13252294158689930300744789 155300322172147620711853)
                ·
                  rfl

theorem cell22_4083025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 8].length) (baseStart_4083025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083025 prefixEnd_4083025 := by exact prefixLift 4083025
  have htrace : WordTrace (prefixWord ++ tailWord_4083025) baseStart_4083025 baseEnd_4083025 := by
    simpa [prefixWord, tailWord_4083025, baseEnd_4083025] using wordTrace_append hprefix tailTrace_4083025
  have hstable : (prefixWord ++ tailWord_4083025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083025).length < 2 ^ (prefixWord ++ tailWord_4083025).sum := by decide
  have hdescent : baseEnd_4083025 < baseStart_4083025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083055 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 2, 6]
def baseStart_4083055 : Nat := 118140960795 + 4083055 * 2 ^ 59
def prefixEnd_4083055 : Nat := 4983230072969 + 3 ^ 40 * 4083055 * 2
def baseEnd_4083055 : Nat := 1397713169162418508156585

theorem tailTrace_4083055 : CollatzResearch.WordTrace tailWord_4083055 prefixEnd_4083055 1397713169162418508156585 := by
  unfold tailWord_4083055
  simp only [CollatzResearch.WordTrace]
  refine ⟨148921250222796540121810619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99280833481864360081207079 148921250222796540121810619)
  ·
    refine ⟨223381875334194810182715929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148921250222796540121810619 223381875334194810182715929)
    ·
      refine ⟨167536406500646107637036947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223381875334194810182715929 167536406500646107637036947)
      ·
        refine ⟨251304609750969161455555421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167536406500646107637036947 251304609750969161455555421)
        ·
          refine ⟨94239228656613435545833283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251304609750969161455555421 94239228656613435545833283)
          ·
            refine ⟨141358842984920153318749925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94239228656613435545833283 141358842984920153318749925)
            ·
              refine ⟨26504783059672528747265611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141358842984920153318749925 26504783059672528747265611)
              ·
                refine ⟨39757174589508793120898417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26504783059672528747265611 39757174589508793120898417)
                ·
                  refine ⟨29817880942131594840673813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39757174589508793120898417 29817880942131594840673813)
                  ·
                    refine ⟨1397713169162418508156585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29817880942131594840673813 1397713169162418508156585)
                    ·
                      rfl

theorem cell22_4083055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_4083055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083055 prefixEnd_4083055 := by exact prefixLift 4083055
  have htrace : WordTrace (prefixWord ++ tailWord_4083055) baseStart_4083055 baseEnd_4083055 := by
    simpa [prefixWord, tailWord_4083055, baseEnd_4083055] using wordTrace_append hprefix tailTrace_4083055
  have hstable : (prefixWord ++ tailWord_4083055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083055).length < 2 ^ (prefixWord ++ tailWord_4083055).sum := by decide
  have hdescent : baseEnd_4083055 < baseStart_4083055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083134 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4083134 : Nat := 118140960795 + 4083134 * 2 ^ 59
def prefixEnd_4083134 : Nat := 4983230072969 + 3 ^ 40 * 4083134 * 2
def baseEnd_4083134 : Nat := 1397740212476888635431343

theorem tailTrace_4083134 : CollatzResearch.WordTrace tailWord_4083134 prefixEnd_4083134 1397740212476888635431343 := by
  unfold tailWord_4083134
  simp only [CollatzResearch.WordTrace]
  refine ⟨18615516448688792076742057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99282754393006891075957637 18615516448688792076742057)
  ·
    refine ⟨13961637336516594057556543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18615516448688792076742057 13961637336516594057556543)
    ·
      refine ⟨20942456004774891086334815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13961637336516594057556543 20942456004774891086334815)
      ·
        refine ⟨31413684007162336629502223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20942456004774891086334815 31413684007162336629502223)
        ·
          refine ⟨47120526010743504944253335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31413684007162336629502223 47120526010743504944253335)
          ·
            refine ⟨70680789016115257416380003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47120526010743504944253335 70680789016115257416380003)
            ·
              refine ⟨106021183524172886124570005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70680789016115257416380003 106021183524172886124570005)
              ·
                refine ⟨4969742977695604037089219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106021183524172886124570005 4969742977695604037089219)
                ·
                  refine ⟨7454614466543406055633829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969742977695604037089219 7454614466543406055633829)
                  ·
                    refine ⟨1397740212476888635431343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7454614466543406055633829 1397740212476888635431343)
                    ·
                      rfl

theorem cell22_4083134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4083134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083134 prefixEnd_4083134 := by exact prefixLift 4083134
  have htrace : WordTrace (prefixWord ++ tailWord_4083134) baseStart_4083134 baseEnd_4083134 := by
    simpa [prefixWord, tailWord_4083134, baseEnd_4083134] using wordTrace_append hprefix tailTrace_4083134
  have hstable : (prefixWord ++ tailWord_4083134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083134).length < 2 ^ (prefixWord ++ tailWord_4083134).sum := by decide
  have hdescent : baseEnd_4083134 < baseStart_4083134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083147 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 1, 5]
def baseStart_4083147 : Nat := 118140960795 + 4083147 * 2 ^ 59
def prefixEnd_4083147 : Nat := 4983230072969 + 3 ^ 40 * 4083147 * 2
def baseEnd_4083147 : Nat := 1397744662642560934856303

theorem tailTrace_4083147 : CollatzResearch.WordTrace tailWord_4083147 prefixEnd_4083147 1397744662642560934856303 := by
  unfold tailWord_4083147
  simp only [CollatzResearch.WordTrace]
  refine ⟨148924605738463239834159695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99283070492308826556106463 148924605738463239834159695)
  ·
    refine ⟨223386908607694859751239543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148924605738463239834159695 223386908607694859751239543)
    ·
      refine ⟨335080362911542289626859315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223386908607694859751239543 335080362911542289626859315)
      ·
        refine ⟨502620544367313434440288973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335080362911542289626859315 502620544367313434440288973)
        ·
          refine ⟨188482704137742537915108365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502620544367313434440288973 188482704137742537915108365)
          ·
            refine ⟨70681014051653451718165637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188482704137742537915108365 70681014051653451718165637)
            ·
              refine ⟨13252690134685022197156057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70681014051653451718165637 13252690134685022197156057)
              ·
                refine ⟨9939517601013766647867043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13252690134685022197156057 9939517601013766647867043)
                ·
                  refine ⟨14909276401520649971800565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9939517601013766647867043 14909276401520649971800565)
                  ·
                    refine ⟨1397744662642560934856303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14909276401520649971800565 1397744662642560934856303)
                    ·
                      rfl

theorem cell22_4083147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 5].length) (baseStart_4083147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083147 prefixEnd_4083147 := by exact prefixLift 4083147
  have htrace : WordTrace (prefixWord ++ tailWord_4083147) baseStart_4083147 baseEnd_4083147 := by
    simpa [prefixWord, tailWord_4083147, baseEnd_4083147] using wordTrace_append hprefix tailTrace_4083147
  have hstable : (prefixWord ++ tailWord_4083147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083147).length < 2 ^ (prefixWord ++ tailWord_4083147).sum := by decide
  have hdescent : baseEnd_4083147 < baseStart_4083147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083237 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_4083237 : Nat := 118140960795 + 4083237 * 2 ^ 59
def prefixEnd_4083237 : Nat := 4983230072969 + 3 ^ 40 * 4083237 * 2
def baseEnd_4083237 : Nat := 1397775471481830700106027

theorem tailTrace_4083237 : CollatzResearch.WordTrace tailWord_4083237 prefixEnd_4083237 1397775471481830700106027 := by
  unfold tailWord_4083237
  simp only [CollatzResearch.WordTrace]
  refine ⟨148927888308137185204935965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99285258872091456803290643 148927888308137185204935965)
  ·
    refine ⟨55847958115551444451850987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148927888308137185204935965 55847958115551444451850987)
    ·
      refine ⟨83771937173327166677776481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55847958115551444451850987 83771937173327166677776481)
      ·
        refine ⟨62828952879995375008332361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83771937173327166677776481 62828952879995375008332361)
        ·
          refine ⟨47121714659996531256249271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62828952879995375008332361 47121714659996531256249271)
          ·
            refine ⟨70682571989994796884373907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47121714659996531256249271 70682571989994796884373907)
            ·
              refine ⟨106023857984992195326560861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70682571989994796884373907 106023857984992195326560861)
              ·
                refine ⟨39758946744372073247460323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106023857984992195326560861 39758946744372073247460323)
                ·
                  refine ⟨59638420116558109871190485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39758946744372073247460323 59638420116558109871190485)
                  ·
                    refine ⟨1397775471481830700106027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59638420116558109871190485 1397775471481830700106027)
                    ·
                      rfl

theorem cell22_4083237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_4083237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083237 prefixEnd_4083237 := by exact prefixLift 4083237
  have htrace : WordTrace (prefixWord ++ tailWord_4083237) baseStart_4083237 baseEnd_4083237 := by
    simpa [prefixWord, tailWord_4083237, baseEnd_4083237] using wordTrace_append hprefix tailTrace_4083237
  have hstable : (prefixWord ++ tailWord_4083237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083237).length < 2 ^ (prefixWord ++ tailWord_4083237).sum := by decide
  have hdescent : baseEnd_4083237 < baseStart_4083237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083284 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 6]
def baseStart_4083284 : Nat := 118140960795 + 4083284 * 2 ^ 59
def prefixEnd_4083284 : Nat := 4983230072969 + 3 ^ 40 * 4083284 * 2
def baseEnd_4083284 : Nat := 465930520180779414726961

theorem tailTrace_4083284 : CollatzResearch.WordTrace tailWord_4083284 prefixEnd_4083284 465930520180779414726961 := by
  unfold tailWord_4083284
  simp only [CollatzResearch.WordTrace]
  refine ⟨74464801269483456115948453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99286401692644608154597937 74464801269483456115948453)
  ·
    refine ⟨13962150238028148021740335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74464801269483456115948453 13962150238028148021740335)
    ·
      refine ⟨20943225357042222032610503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13962150238028148021740335 20943225357042222032610503)
      ·
        refine ⟨31414838035563333048915755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20943225357042222032610503 31414838035563333048915755)
        ·
          refine ⟨47122257053344999573373633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31414838035563333048915755 47122257053344999573373633)
          ·
            refine ⟨35341692790008749680030225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47122257053344999573373633 35341692790008749680030225)
            ·
              refine ⟨26506269592506562260022669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35341692790008749680030225 26506269592506562260022669)
              ·
                refine ⟨9939851097189960847508501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26506269592506562260022669 9939851097189960847508501)
                ·
                  refine ⟨465930520180779414726961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9939851097189960847508501 465930520180779414726961)
                  ·
                    rfl

theorem cell22_4083284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_4083284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083284 prefixEnd_4083284 := by exact prefixLift 4083284
  have htrace : WordTrace (prefixWord ++ tailWord_4083284) baseStart_4083284 baseEnd_4083284 := by
    simpa [prefixWord, tailWord_4083284, baseEnd_4083284] using wordTrace_append hprefix tailTrace_4083284
  have hstable : (prefixWord ++ tailWord_4083284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083284).length < 2 ^ (prefixWord ++ tailWord_4083284).sum := by decide
  have hdescent : baseEnd_4083284 < baseStart_4083284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083299 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 1, 5]
def baseStart_4083299 : Nat := 118140960795 + 4083299 * 2 ^ 59
def prefixEnd_4083299 : Nat := 4983230072969 + 3 ^ 40 * 4083299 * 2
def baseEnd_4083299 : Nat := 1397796695348883205055837

theorem tailTrace_4083299 : CollatzResearch.WordTrace tailWord_4083299 prefixEnd_4083299 1397796695348883205055837 := by
  unfold tailWord_4083299
  simp only [CollatzResearch.WordTrace]
  refine ⟨148930149633912569793692951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99286766422608379862461967 148930149633912569793692951)
  ·
    refine ⟨223395224450868854690539427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148930149633912569793692951 223395224450868854690539427)
    ·
      refine ⟨335092836676303282035809141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223395224450868854690539427 335092836676303282035809141)
      ·
        refine ⟨31414953438403432690857107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335092836676303282035809141 31414953438403432690857107)
        ·
          refine ⟨47122430157605149036285661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31414953438403432690857107 47122430157605149036285661)
          ·
            refine ⟨17670911309101930888607123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47122430157605149036285661 17670911309101930888607123)
            ·
              refine ⟨26506366963652896332910685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17670911309101930888607123 26506366963652896332910685)
              ·
                refine ⟨9939887611369836124841507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26506366963652896332910685 9939887611369836124841507)
                ·
                  refine ⟨14909831417054754187262261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9939887611369836124841507 14909831417054754187262261)
                  ·
                    refine ⟨1397796695348883205055837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14909831417054754187262261 1397796695348883205055837)
                    ·
                      rfl

theorem cell22_4083299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 5].length) (baseStart_4083299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083299 prefixEnd_4083299 := by exact prefixLift 4083299
  have htrace : WordTrace (prefixWord ++ tailWord_4083299) baseStart_4083299 baseEnd_4083299 := by
    simpa [prefixWord, tailWord_4083299, baseEnd_4083299] using wordTrace_append hprefix tailTrace_4083299
  have hstable : (prefixWord ++ tailWord_4083299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083299).length < 2 ^ (prefixWord ++ tailWord_4083299).sum := by decide
  have hdescent : baseEnd_4083299 < baseStart_4083299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083318 : List Nat := [5, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_4083318 : Nat := 118140960795 + 4083318 * 2 ^ 59
def prefixEnd_4083318 : Nat := 4983230072969 + 3 ^ 40 * 4083318 * 2
def baseEnd_4083318 : Nat := 465934399812391162943593

theorem tailTrace_4083318 : CollatzResearch.WordTrace tailWord_4083318 prefixEnd_4083318 465934399812391162943593 := by
  unfold tailWord_4083318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9308177663802733502414663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99287228413895824025756405 9308177663802733502414663)
  ·
    refine ⟨13962266495704100253621995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9308177663802733502414663 13962266495704100253621995)
    ·
      refine ⟨20943399743556150380432993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13962266495704100253621995 20943399743556150380432993)
      ·
        refine ⟨15707549807667112785324745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20943399743556150380432993 15707549807667112785324745)
        ·
          refine ⟨11780662355750334588993559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15707549807667112785324745 11780662355750334588993559)
          ·
            refine ⟨17670993533625501883490339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11780662355750334588993559 17670993533625501883490339)
            ·
              refine ⟨26506490300438252825235509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17670993533625501883490339 26506490300438252825235509)
              ·
                refine ⟨2484983465666086202365829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26506490300438252825235509 2484983465666086202365829)
                ·
                  refine ⟨465934399812391162943593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2484983465666086202365829 465934399812391162943593)
                  ·
                    rfl

theorem cell22_4083318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_4083318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083318 prefixEnd_4083318 := by exact prefixLift 4083318
  have htrace : WordTrace (prefixWord ++ tailWord_4083318) baseStart_4083318 baseEnd_4083318 := by
    simpa [prefixWord, tailWord_4083318, baseEnd_4083318] using wordTrace_append hprefix tailTrace_4083318
  have hstable : (prefixWord ++ tailWord_4083318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083318).length < 2 ^ (prefixWord ++ tailWord_4083318).sum := by decide
  have hdescent : baseEnd_4083318 < baseStart_4083318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083329 : List Nat := [1, 2, 4, 2, 1, 3, 9]
def baseStart_4083329 : Nat := 118140960795 + 4083329 * 2 ^ 59
def prefixEnd_4083329 : Nat := 4983230072969 + 3 ^ 40 * 4083329 * 2
def baseEnd_4083329 : Nat := 51770628331924930622435

theorem tailTrace_4083329 : CollatzResearch.WordTrace tailWord_4083329 prefixEnd_4083329 51770628331924930622435 := by
  unfold tailWord_4083329
  simp only [CollatzResearch.WordTrace]
  refine ⟨148931243823803884917285041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99287495882535923278190027 148931243823803884917285041)
  ·
    refine ⟨111698432867852913687963781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148931243823803884917285041 111698432867852913687963781)
    ·
      refine ⟨20943456162722421316493209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111698432867852913687963781 20943456162722421316493209)
      ·
        refine ⟨15707592122041815987369907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20943456162722421316493209 15707592122041815987369907)
        ·
          refine ⟨23561388183062723981054861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15707592122041815987369907 23561388183062723981054861)
          ·
            refine ⟨8835520568648521492895573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23561388183062723981054861 8835520568648521492895573)
            ·
              refine ⟨51770628331924930622435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8835520568648521492895573 51770628331924930622435)
              ·
                rfl

theorem cell22_4083329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 9].length) (baseStart_4083329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083329 prefixEnd_4083329 := by exact prefixLift 4083329
  have htrace : WordTrace (prefixWord ++ tailWord_4083329) baseStart_4083329 baseEnd_4083329 := by
    simpa [prefixWord, tailWord_4083329, baseEnd_4083329] using wordTrace_append hprefix tailTrace_4083329
  have hstable : (prefixWord ++ tailWord_4083329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083329).length < 2 ^ (prefixWord ++ tailWord_4083329).sum := by decide
  have hdescent : baseEnd_4083329 < baseStart_4083329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083449 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_4083449 : Nat := 118140960795 + 4083449 * 2 ^ 59
def prefixEnd_4083449 : Nat := 4983230072969 + 3 ^ 40 * 4083449 * 2
def baseEnd_4083449 : Nat := 1397848043414332813805377

theorem tailTrace_4083449 : CollatzResearch.WordTrace tailWord_4083449 prefixEnd_4083449 1397848043414332813805377 := by
  unfold tailWord_4083449
  simp only [CollatzResearch.WordTrace]
  refine ⟨148935620583369145411653401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99290413722246096941102267 148935620583369145411653401)
  ·
    refine ⟨111701715437526859058740051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148935620583369145411653401 111701715437526859058740051)
    ·
      refine ⟨167552573156290288588110077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111701715437526859058740051 167552573156290288588110077)
      ·
        refine ⟨62832214933608858220541279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167552573156290288588110077 62832214933608858220541279)
        ·
          refine ⟨94248322400413287330811919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62832214933608858220541279 94248322400413287330811919)
          ·
            refine ⟨141372483600619930996217879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94248322400413287330811919 141372483600619930996217879)
            ·
              refine ⟨212058725400929896494326819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141372483600619930996217879 212058725400929896494326819)
              ·
                refine ⟨318088088101394844741490229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212058725400929896494326819 318088088101394844741490229)
                ·
                  refine ⟨29820758259505766694514709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318088088101394844741490229 29820758259505766694514709)
                  ·
                    refine ⟨1397848043414332813805377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29820758259505766694514709 1397848043414332813805377)
                    ·
                      rfl

theorem cell22_4083449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_4083449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083449 prefixEnd_4083449 := by exact prefixLift 4083449
  have htrace : WordTrace (prefixWord ++ tailWord_4083449) baseStart_4083449 baseEnd_4083449 := by
    simpa [prefixWord, tailWord_4083449, baseEnd_4083449] using wordTrace_append hprefix tailTrace_4083449
  have hstable : (prefixWord ++ tailWord_4083449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083449).length < 2 ^ (prefixWord ++ tailWord_4083449).sum := by decide
  have hdescent : baseEnd_4083449 < baseStart_4083449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083468 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 2, 3]
def baseStart_4083468 : Nat := 118140960795 + 4083468 * 2 ^ 59
def prefixEnd_4083468 : Nat := 4983230072969 + 3 ^ 40 * 4083468 * 2
def baseEnd_4083468 : Nat := 1397854547502623097580319

theorem tailTrace_4083468 : CollatzResearch.WordTrace tailWord_4083468 prefixEnd_4083468 1397854547502623097580319 := by
  unfold tailWord_4083468
  simp only [CollatzResearch.WordTrace]
  refine ⟨74468156785150155828297529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99290875713533541104396705 74468156785150155828297529)
  ·
    refine ⟨55851117588862616871223147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74468156785150155828297529 55851117588862616871223147)
    ·
      refine ⟨83776676383293925306834721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55851117588862616871223147 83776676383293925306834721)
      ·
        refine ⟨62832507287470443980126041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83776676383293925306834721 62832507287470443980126041)
        ·
          refine ⟨47124380465602832985094531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62832507287470443980126041 47124380465602832985094531)
          ·
            refine ⟨70686570698404249477641797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47124380465602832985094531 70686570698404249477641797)
            ·
              refine ⟨13253732005950796777057837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70686570698404249477641797 13253732005950796777057837)
              ·
                refine ⟨4970149502231548791396689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13253732005950796777057837 4970149502231548791396689)
                ·
                  refine ⟨3727612126673661593547517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970149502231548791396689 3727612126673661593547517)
                  ·
                    refine ⟨1397854547502623097580319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3727612126673661593547517 1397854547502623097580319)
                    ·
                      rfl

theorem cell22_4083468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_4083468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083468 prefixEnd_4083468 := by exact prefixLift 4083468
  have htrace : WordTrace (prefixWord ++ tailWord_4083468) baseStart_4083468 baseEnd_4083468 := by
    simpa [prefixWord, tailWord_4083468, baseEnd_4083468] using wordTrace_append hprefix tailTrace_4083468
  have hstable : (prefixWord ++ tailWord_4083468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083468).length < 2 ^ (prefixWord ++ tailWord_4083468).sum := by decide
  have hdescent : baseEnd_4083468 < baseStart_4083468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083573 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_4083573 : Nat := 118140960795 + 4083573 * 2 ^ 59
def prefixEnd_4083573 : Nat := 4983230072969 + 3 ^ 40 * 4083573 * 2
def baseEnd_4083573 : Nat := 1397890491148437823704997

theorem tailTrace_4083573 : CollatzResearch.WordTrace tailWord_4083573 prefixEnd_4083573 1397890491148437823704997 := by
  unfold tailWord_4083573
  simp only [CollatzResearch.WordTrace]
  refine ⟨148940143234919914589167373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99293428823279943059444915 148940143234919914589167373)
  ·
    refine ⟨55852553713094967970937765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148940143234919914589167373 55852553713094967970937765)
    ·
      refine ⟨10472353821205306494550831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55852553713094967970937765 10472353821205306494550831)
      ·
        refine ⟨15708530731807959741826247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10472353821205306494550831 15708530731807959741826247)
        ·
          refine ⟨23562796097711939612739371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15708530731807959741826247 23562796097711939612739371)
          ·
            refine ⟨35344194146567909419109057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23562796097711939612739371 35344194146567909419109057)
            ·
              refine ⟨26508145609925932064331793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35344194146567909419109057 26508145609925932064331793)
              ·
                refine ⟨19881109207444449048248845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26508145609925932064331793 19881109207444449048248845)
                ·
                  refine ⟨7455415952791668393093317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19881109207444449048248845 7455415952791668393093317)
                  ·
                    refine ⟨1397890491148437823704997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7455415952791668393093317 1397890491148437823704997)
                    ·
                      rfl

theorem cell22_4083573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_4083573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083573 prefixEnd_4083573 := by exact prefixLift 4083573
  have htrace : WordTrace (prefixWord ++ tailWord_4083573) baseStart_4083573 baseEnd_4083573 := by
    simpa [prefixWord, tailWord_4083573, baseEnd_4083573] using wordTrace_append hprefix tailTrace_4083573
  have hstable : (prefixWord ++ tailWord_4083573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083573).length < 2 ^ (prefixWord ++ tailWord_4083573).sum := by decide
  have hdescent : baseEnd_4083573 < baseStart_4083573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083601 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_4083601 : Nat := 118140960795 + 4083601 * 2 ^ 59
def prefixEnd_4083601 : Nat := 4983230072969 + 3 ^ 40 * 4083601 * 2
def baseEnd_4083601 : Nat := 1397900076120655084004911

theorem tailTrace_4083601 : CollatzResearch.WordTrace tailWord_4083601 prefixEnd_4083601 1397900076120655084004911 := by
  unfold tailWord_4083601
  simp only [CollatzResearch.WordTrace]
  refine ⟨148941164478818475371186657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99294109652545650247457771 148941164478818475371186657)
  ·
    refine ⟨111705873359113856528389993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148941164478818475371186657 111705873359113856528389993)
    ·
      refine ⟨83779405019335392396292495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111705873359113856528389993 83779405019335392396292495)
      ·
        refine ⟨125669107529003088594438743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83779405019335392396292495 125669107529003088594438743)
        ·
          refine ⟨188503661293504632891658115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125669107529003088594438743 188503661293504632891658115)
          ·
            refine ⟨282755491940256949337487173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188503661293504632891658115 282755491940256949337487173)
            ·
              refine ⟨53016654738798178000778845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282755491940256949337487173 53016654738798178000778845)
              ·
                refine ⟨19881245527049316750292067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53016654738798178000778845 19881245527049316750292067)
                ·
                  refine ⟨29821868290573975125438101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19881245527049316750292067 29821868290573975125438101)
                  ·
                    refine ⟨1397900076120655084004911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29821868290573975125438101 1397900076120655084004911)
                    ·
                      rfl

theorem cell22_4083601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_4083601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083601 prefixEnd_4083601 := by exact prefixLift 4083601
  have htrace : WordTrace (prefixWord ++ tailWord_4083601) baseStart_4083601 baseEnd_4083601 := by
    simpa [prefixWord, tailWord_4083601, baseEnd_4083601] using wordTrace_append hprefix tailTrace_4083601
  have hstable : (prefixWord ++ tailWord_4083601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083601).length < 2 ^ (prefixWord ++ tailWord_4083601).sum := by decide
  have hdescent : baseEnd_4083601 < baseStart_4083601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083620 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_4083620 : Nat := 118140960795 + 4083620 * 2 ^ 59
def prefixEnd_4083620 : Nat := 4983230072969 + 3 ^ 40 * 4083620 * 2
def baseEnd_4083620 : Nat := 1397906580208945367779853

theorem tailTrace_4083620 : CollatzResearch.WordTrace tailWord_4083620 prefixEnd_4083620 1397906580208945367779853 := by
  unfold tailWord_4083620
  simp only [CollatzResearch.WordTrace]
  refine ⟨74470928732874820808064157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99294571643833094410752209 74470928732874820808064157)
  ·
    refine ⟨27926598274828057803024059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74470928732874820808064157 27926598274828057803024059)
    ·
      refine ⟨41889897412242086704536089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27926598274828057803024059 41889897412242086704536089)
      ·
        refine ⟨31417423059181565028402067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41889897412242086704536089 31417423059181565028402067)
        ·
          refine ⟨47126134588772347542603101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31417423059181565028402067 47126134588772347542603101)
          ·
            refine ⟨17672300470789630328476163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47126134588772347542603101 17672300470789630328476163)
            ·
              refine ⟨26508450706184445492714245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17672300470789630328476163 26508450706184445492714245)
              ·
                refine ⟨4970334507409583529883921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26508450706184445492714245 4970334507409583529883921)
                ·
                  refine ⟨3727750880557187647412941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970334507409583529883921 3727750880557187647412941)
                  ·
                    refine ⟨1397906580208945367779853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3727750880557187647412941 1397906580208945367779853)
                    ·
                      rfl

theorem cell22_4083620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_4083620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083620 prefixEnd_4083620 := by exact prefixLift 4083620
  have htrace : WordTrace (prefixWord ++ tailWord_4083620) baseStart_4083620 baseEnd_4083620 := by
    simpa [prefixWord, tailWord_4083620, baseEnd_4083620] using wordTrace_append hprefix tailTrace_4083620
  have hstable : (prefixWord ++ tailWord_4083620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083620).length < 2 ^ (prefixWord ++ tailWord_4083620).sum := by decide
  have hdescent : baseEnd_4083620 < baseStart_4083620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083633 : List Nat := [1, 2, 2, 4, 2, 1, 3, 7]
def baseStart_4083633 : Nat := 118140960795 + 4083633 * 2 ^ 59
def prefixEnd_4083633 : Nat := 4983230072969 + 3 ^ 40 * 4083633 * 2
def baseEnd_4083633 : Nat := 155323447819401963022757

theorem tailTrace_4083633 : CollatzResearch.WordTrace tailWord_4083633 prefixEnd_4083633 155323447819401963022757 := by
  unfold tailWord_4083633
  simp only [CollatzResearch.WordTrace]
  refine ⟨148942331614702544836351553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99294887743135029890901035 148942331614702544836351553)
  ·
    refine ⟨111706748711026908627263665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148942331614702544836351553 111706748711026908627263665)
    ·
      refine ⟨83780061533270181470447749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111706748711026908627263665 83780061533270181470447749)
      ·
        refine ⟨15708761537488159025708953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83780061533270181470447749 15708761537488159025708953)
        ·
          refine ⟨11781571153116119269281715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15708761537488159025708953 11781571153116119269281715)
          ·
            refine ⟨17672356729674178903922573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11781571153116119269281715 17672356729674178903922573)
            ·
              refine ⟨6627133773627817088970965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17672356729674178903922573 6627133773627817088970965)
              ·
                refine ⟨155323447819401963022757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6627133773627817088970965 155323447819401963022757)
                ·
                  rfl

theorem cell22_4083633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 7].length) (baseStart_4083633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083633 prefixEnd_4083633 := by exact prefixLift 4083633
  have htrace : WordTrace (prefixWord ++ tailWord_4083633) baseStart_4083633 baseEnd_4083633 := by
    simpa [prefixWord, tailWord_4083633, baseEnd_4083633] using wordTrace_append hprefix tailTrace_4083633
  have hstable : (prefixWord ++ tailWord_4083633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083633).length < 2 ^ (prefixWord ++ tailWord_4083633).sum := by decide
  have hdescent : baseEnd_4083633 < baseStart_4083633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083695 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 5]
def baseStart_4083695 : Nat := 118140960795 + 4083695 * 2 ^ 59
def prefixEnd_4083695 : Nat := 4983230072969 + 3 ^ 40 * 4083695 * 2
def baseEnd_4083695 : Nat := 465977418080556724051541

theorem tailTrace_4083695 : CollatzResearch.WordTrace tailWord_4083695 prefixEnd_4083695 465977418080556724051541 := by
  unfold tailWord_4083695
  simp only [CollatzResearch.WordTrace]
  refine ⟨148944592940477929425108539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99296395293651952950072359 148944592940477929425108539)
  ·
    refine ⟨223416889410716894137662809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148944592940477929425108539 223416889410716894137662809)
    ·
      refine ⟨167562667058037670603247107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223416889410716894137662809 167562667058037670603247107)
      ·
        refine ⟨251344000587056505904870661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167562667058037670603247107 251344000587056505904870661)
        ·
          refine ⟨47127000110073094857163249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251344000587056505904870661 47127000110073094857163249)
          ·
            refine ⟨35345250082554821142872437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47127000110073094857163249 35345250082554821142872437)
            ·
              refine ⟨3313617195239514482144291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35345250082554821142872437 3313617195239514482144291)
              ·
                refine ⟨4970425792859271723216437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313617195239514482144291 4970425792859271723216437)
                ·
                  refine ⟨465977418080556724051541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4970425792859271723216437 465977418080556724051541)
                  ·
                    rfl

theorem cell22_4083695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 5].length) (baseStart_4083695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083695 prefixEnd_4083695 := by exact prefixLift 4083695
  have htrace : WordTrace (prefixWord ++ tailWord_4083695) baseStart_4083695 baseEnd_4083695 := by
    simpa [prefixWord, tailWord_4083695, baseEnd_4083695] using wordTrace_append hprefix tailTrace_4083695
  have hstable : (prefixWord ++ tailWord_4083695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083695).length < 2 ^ (prefixWord ++ tailWord_4083695).sum := by decide
  have hdescent : baseEnd_4083695 < baseStart_4083695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083740 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 6]
def baseStart_4083740 : Nat := 118140960795 + 4083740 * 2 ^ 59
def prefixEnd_4083740 : Nat := 4983230072969 + 3 ^ 40 * 4083740 * 2
def baseEnd_4083740 : Nat := 465982552887101684926495

theorem tailTrace_4083740 : CollatzResearch.WordTrace tailWord_4083740 prefixEnd_4083740 465982552887101684926495 := by
  unfold tailWord_4083740
  simp only [CollatzResearch.WordTrace]
  refine ⟨74473117112657451055248337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99297489483543268073664449 74473117112657451055248337)
  ·
    refine ⟨55854837834493088291436253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74473117112657451055248337 55854837834493088291436253)
    ·
      refine ⟨20945564187934908109288595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55854837834493088291436253 20945564187934908109288595)
      ·
        refine ⟨31418346281902362163932893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20945564187934908109288595 31418346281902362163932893)
        ·
          refine ⟨11781879855713385811474835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31418346281902362163932893 11781879855713385811474835)
          ·
            refine ⟨17672819783570078717212253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11781879855713385811474835 17672819783570078717212253)
            ·
              refine ⟨6627307418838779518954595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17672819783570078717212253 6627307418838779518954595)
              ·
                refine ⟨9940961128258169278431893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627307418838779518954595 9940961128258169278431893)
                ·
                  refine ⟨465982552887101684926495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9940961128258169278431893 465982552887101684926495)
                  ·
                    rfl

theorem cell22_4083740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_4083740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083740 prefixEnd_4083740 := by exact prefixLift 4083740
  have htrace : WordTrace (prefixWord ++ tailWord_4083740) baseStart_4083740 baseEnd_4083740 := by
    simpa [prefixWord, tailWord_4083740, baseEnd_4083740] using wordTrace_append hprefix tailTrace_4083740
  have hstable : (prefixWord ++ tailWord_4083740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083740).length < 2 ^ (prefixWord ++ tailWord_4083740).sum := by decide
  have hdescent : baseEnd_4083740 < baseStart_4083740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083789 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_4083789 : Nat := 118140960795 + 4083789 * 2 ^ 59
def prefixEnd_4083789 : Nat := 4983230072969 + 3 ^ 40 * 4083789 * 2
def baseEnd_4083789 : Nat := 1397964432362685260304335

theorem tailTrace_4083789 : CollatzResearch.WordTrace tailWord_4083789 prefixEnd_4083789 1397964432362685260304335 := by
  unfold tailWord_4083789
  simp only [CollatzResearch.WordTrace]
  refine ⟨148948021402137383479030421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99298680934758255652686947 148948021402137383479030421)
  ·
    refine ⟨6981938503225189850579551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148948021402137383479030421 6981938503225189850579551)
    ·
      refine ⟨10472907754837784775869327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6981938503225189850579551 10472907754837784775869327)
      ·
        refine ⟨15709361632256677163803991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10472907754837784775869327 15709361632256677163803991)
        ·
          refine ⟨23564042448385015745705987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15709361632256677163803991 23564042448385015745705987)
          ·
            refine ⟨35346063672577523618558981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23564042448385015745705987 35346063672577523618558981)
            ·
              refine ⟨6627386938608285678479809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35346063672577523618558981 6627386938608285678479809)
              ·
                refine ⟨4970540203956214258859857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6627386938608285678479809 4970540203956214258859857)
                ·
                  refine ⟨3727905152967160694144893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970540203956214258859857 3727905152967160694144893)
                  ·
                    refine ⟨1397964432362685260304335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3727905152967160694144893 1397964432362685260304335)
                    ·
                      rfl

theorem cell22_4083789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_4083789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083789 prefixEnd_4083789 := by exact prefixLift 4083789
  have htrace : WordTrace (prefixWord ++ tailWord_4083789) baseStart_4083789 baseEnd_4083789 := by
    simpa [prefixWord, tailWord_4083789, baseEnd_4083789] using wordTrace_append hprefix tailTrace_4083789
  have hstable : (prefixWord ++ tailWord_4083789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083789).length < 2 ^ (prefixWord ++ tailWord_4083789).sum := by decide
  have hdescent : baseEnd_4083789 < baseStart_4083789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083806 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4083806 : Nat := 118140960795 + 4083806 * 2 ^ 59
def prefixEnd_4083806 : Nat := 4983230072969 + 3 ^ 40 * 4083806 * 2
def baseEnd_4083806 : Nat := 1397970251810102882629283

theorem tailTrace_4083806 : CollatzResearch.WordTrace tailWord_4083806 prefixEnd_4083806 1397970251810102882629283 := by
  unfold tailWord_4083806
  simp only [CollatzResearch.WordTrace]
  refine ⟨18618580180384474422799909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99299094295383863588266181 18618580180384474422799909)
  ·
    refine ⟨3490983783822088954274983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18618580180384474422799909 3490983783822088954274983)
    ·
      refine ⟨5236475675733133431412475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3490983783822088954274983 5236475675733133431412475)
      ·
        refine ⟨7854713513599700147118713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236475675733133431412475 7854713513599700147118713)
        ·
          refine ⟨5891035135199775110339035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7854713513599700147118713 5891035135199775110339035)
          ·
            refine ⟨8836552702799662665508553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891035135199775110339035 8836552702799662665508553)
            ·
              refine ⟨6627414527099746999131415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8836552702799662665508553 6627414527099746999131415)
              ·
                refine ⟨9941121790649620498697123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627414527099746999131415 9941121790649620498697123)
                ·
                  refine ⟨14911682685974430748045685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9941121790649620498697123 14911682685974430748045685)
                  ·
                    refine ⟨1397970251810102882629283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14911682685974430748045685 1397970251810102882629283)
                    ·
                      rfl

theorem cell22_4083806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4083806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083806 prefixEnd_4083806 := by exact prefixLift 4083806
  have htrace : WordTrace (prefixWord ++ tailWord_4083806) baseStart_4083806 baseEnd_4083806 := by
    simpa [prefixWord, tailWord_4083806, baseEnd_4083806] using wordTrace_append hprefix tailTrace_4083806
  have hstable : (prefixWord ++ tailWord_4083806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083806).length < 2 ^ (prefixWord ++ tailWord_4083806).sum := by decide
  have hdescent : baseEnd_4083806 < baseStart_4083806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083845 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_4083845 : Nat := 118140960795 + 4083845 * 2 ^ 59
def prefixEnd_4083845 : Nat := 4983230072969 + 3 ^ 40 * 4083845 * 2
def baseEnd_4083845 : Nat := 1397983602307119780904163

theorem tailTrace_4083845 : CollatzResearch.WordTrace tailWord_4083845 prefixEnd_4083845 1397983602307119780904163 := by
  unfold tailWord_4083845
  simp only [CollatzResearch.WordTrace]
  refine ⟨148950063889934505043068989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99300042593289670028712659 148950063889934505043068989)
  ·
    refine ⟨55856273958725439391150871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148950063889934505043068989 55856273958725439391150871)
    ·
      refine ⟨83784410938088159086726307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55856273958725439391150871 83784410938088159086726307)
      ·
        refine ⟨125676616407132238630089461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83784410938088159086726307 125676616407132238630089461)
        ·
          refine ⟨11782182788168647371570887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125676616407132238630089461 11782182788168647371570887)
          ·
            refine ⟨17673274182252971057356331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11782182788168647371570887 17673274182252971057356331)
            ·
              refine ⟨26509911273379456586034497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17673274182252971057356331 26509911273379456586034497)
              ·
                refine ⟨19882433455034592439525873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26509911273379456586034497 19882433455034592439525873)
                ·
                  refine ⟨14911825091275944329644405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19882433455034592439525873 14911825091275944329644405)
                  ·
                    refine ⟨1397983602307119780904163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14911825091275944329644405 1397983602307119780904163)
                    ·
                      rfl

theorem cell22_4083845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_4083845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083845 prefixEnd_4083845 := by exact prefixLift 4083845
  have htrace : WordTrace (prefixWord ++ tailWord_4083845) baseStart_4083845 baseEnd_4083845 := by
    simpa [prefixWord, tailWord_4083845, baseEnd_4083845] using wordTrace_append hprefix tailTrace_4083845
  have hstable : (prefixWord ++ tailWord_4083845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083845).length < 2 ^ (prefixWord ++ tailWord_4083845).sum := by decide
  have hdescent : baseEnd_4083845 < baseStart_4083845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083864 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 5]
def baseStart_4083864 : Nat := 118140960795 + 4083864 * 2 ^ 59
def prefixEnd_4083864 : Nat := 4983230072969 + 3 ^ 40 * 4083864 * 2
def baseEnd_4083864 : Nat := 465996702131803354893035

theorem tailTrace_4083864 : CollatzResearch.WordTrace tailWord_4083864 prefixEnd_4083864 465996702131803354893035 := by
  unfold tailWord_4083864
  simp only [CollatzResearch.WordTrace]
  refine ⟨74475378438432835644005323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99300504584577114192007097 74475378438432835644005323)
  ·
    refine ⟨111713067657649253466007985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74475378438432835644005323 111713067657649253466007985)
    ·
      refine ⟨83784800743236940099505989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111713067657649253466007985 83784800743236940099505989)
      ·
        refine ⟨15709650139356926268657373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83784800743236940099505989 15709650139356926268657373)
        ·
          refine ⟨5891118802258847350746515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15709650139356926268657373 5891118802258847350746515)
          ·
            refine ⟨8836678203388271026119773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891118802258847350746515 8836678203388271026119773)
            ·
              refine ⟨3313754326270601634794915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8836678203388271026119773 3313754326270601634794915)
              ·
                refine ⟨4970631489405902452192373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313754326270601634794915 4970631489405902452192373)
                ·
                  refine ⟨465996702131803354893035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4970631489405902452192373 465996702131803354893035)
                  ·
                    rfl

theorem cell22_4083864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 5].length) (baseStart_4083864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083864 prefixEnd_4083864 := by exact prefixLift 4083864
  have htrace : WordTrace (prefixWord ++ tailWord_4083864) baseStart_4083864 baseEnd_4083864 := by
    simpa [prefixWord, tailWord_4083864, baseEnd_4083864] using wordTrace_append hprefix tailTrace_4083864
  have hstable : (prefixWord ++ tailWord_4083864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083864).length < 2 ^ (prefixWord ++ tailWord_4083864).sum := by decide
  have hdescent : baseEnd_4083864 < baseStart_4083864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083877 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_4083877 : Nat := 118140960795 + 4083877 * 2 ^ 59
def prefixEnd_4083877 : Nat := 4983230072969 + 3 ^ 40 * 4083877 * 2
def baseEnd_4083877 : Nat := 1397994556561082364104065

theorem tailTrace_4083877 : CollatzResearch.WordTrace tailWord_4083877 prefixEnd_4083877 1397994556561082364104065 := by
  unfold tailWord_4083877
  simp only [CollatzResearch.WordTrace]
  refine ⟨148951231025818574508233885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99300820683879049672155923 148951231025818574508233885)
  ·
    refine ⟨55856711634681965440587707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148951231025818574508233885 55856711634681965440587707)
    ·
      refine ⟨83785067452022948160881561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55856711634681965440587707 83785067452022948160881561)
      ·
        refine ⟨62838800589017211120661171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83785067452022948160881561 62838800589017211120661171)
        ·
          refine ⟨94258200883525816680991757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62838800589017211120661171 94258200883525816680991757)
          ·
            refine ⟨35346825331322181255371909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94258200883525816680991757 35346825331322181255371909)
            ·
              refine ⟨6627529749622908985382233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35346825331322181255371909 6627529749622908985382233)
              ·
                refine ⟨4970647312217181739036675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6627529749622908985382233 4970647312217181739036675)
                ·
                  refine ⟨7455970968325772608555013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970647312217181739036675 7455970968325772608555013)
                  ·
                    refine ⟨1397994556561082364104065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7455970968325772608555013 1397994556561082364104065)
                    ·
                      rfl

theorem cell22_4083877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_4083877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083877 prefixEnd_4083877 := by exact prefixLift 4083877
  have htrace : WordTrace (prefixWord ++ tailWord_4083877) baseStart_4083877 baseEnd_4083877 := by
    simpa [prefixWord, tailWord_4083877, baseEnd_4083877] using wordTrace_append hprefix tailTrace_4083877
  have hstable : (prefixWord ++ tailWord_4083877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083877).length < 2 ^ (prefixWord ++ tailWord_4083877).sum := by decide
  have hdescent : baseEnd_4083877 < baseStart_4083877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083890 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_4083890 : Nat := 118140960795 + 4083890 * 2 ^ 59
def prefixEnd_4083890 : Nat := 4983230072969 + 3 ^ 40 * 4083890 * 2
def baseEnd_4083890 : Nat := 1397999006726754663529025

theorem tailTrace_4083890 : CollatzResearch.WordTrace tailWord_4083890 prefixEnd_4083890 1397999006726754663529025 := by
  unfold tailWord_4083890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37237926293692869432114281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99301136783180985152304749 37237926293692869432114281)
  ·
    refine ⟨27928444720269652074085711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37237926293692869432114281 27928444720269652074085711)
    ·
      refine ⟨41892667080404478111128567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27928444720269652074085711 41892667080404478111128567)
      ·
        refine ⟨62839000620606717166692851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41892667080404478111128567 62839000620606717166692851)
        ·
          refine ⟨94258500930910075750039277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62839000620606717166692851 94258500930910075750039277)
          ·
            refine ⟨35346937849091278406264729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94258500930910075750039277 35346937849091278406264729)
            ·
              refine ⟨26510203386818458804698547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35346937849091278406264729 26510203386818458804698547)
              ·
                refine ⟨39765305080227688207047821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26510203386818458804698547 39765305080227688207047821)
                ·
                  refine ⟨14911989405085383077642933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39765305080227688207047821 14911989405085383077642933)
                  ·
                    refine ⟨1397999006726754663529025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14911989405085383077642933 1397999006726754663529025)
                    ·
                      rfl

theorem cell22_4083890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_4083890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083890 prefixEnd_4083890 := by exact prefixLift 4083890
  have htrace : WordTrace (prefixWord ++ tailWord_4083890) baseStart_4083890 baseEnd_4083890 := by
    simpa [prefixWord, tailWord_4083890, baseEnd_4083890] using wordTrace_append hprefix tailTrace_4083890
  have hstable : (prefixWord ++ tailWord_4083890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083890).length < 2 ^ (prefixWord ++ tailWord_4083890).sum := by decide
  have hdescent : baseEnd_4083890 < baseStart_4083890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083965 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 7]
def baseStart_4083965 : Nat := 118140960795 + 4083965 * 2 ^ 59
def prefixEnd_4083965 : Nat := 4983230072969 + 3 ^ 40 * 4083965 * 2
def baseEnd_4083965 : Nat := 466008226919826489301265

theorem tailTrace_4083965 : CollatzResearch.WordTrace tailWord_4083965 prefixEnd_4083965 466008226919826489301265 := by
  unfold tailWord_4083965
  simp only [CollatzResearch.WordTrace]
  refine ⟨148954440649499765537437349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99302960432999843691624899 148954440649499765537437349)
  ·
    refine ⟨27928957621781206038269503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148954440649499765537437349 27928957621781206038269503)
    ·
      refine ⟨41893436432671809057404255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27928957621781206038269503 41893436432671809057404255)
      ·
        refine ⟨62840154649007713586106383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41893436432671809057404255 62840154649007713586106383)
        ·
          refine ⟨94260231973511570379159575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62840154649007713586106383 94260231973511570379159575)
          ·
            refine ⟨141390347960267355568739363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94260231973511570379159575 141390347960267355568739363)
            ·
              refine ⟨212085521940401033353109045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141390347960267355568739363 212085521940401033353109045)
              ·
                refine ⟨19883017681912596876853973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212085521940401033353109045 19883017681912596876853973)
                ·
                  refine ⟨466008226919826489301265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19883017681912596876853973 466008226919826489301265)
                  ·
                    rfl

theorem cell22_4083965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_4083965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083965 prefixEnd_4083965 := by exact prefixLift 4083965
  have htrace : WordTrace (prefixWord ++ tailWord_4083965) baseStart_4083965 baseEnd_4083965 := by
    simpa [prefixWord, tailWord_4083965, baseEnd_4083965] using wordTrace_append hprefix tailTrace_4083965
  have hstable : (prefixWord ++ tailWord_4083965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083965).length < 2 ^ (prefixWord ++ tailWord_4083965).sum := by decide
  have hdescent : baseEnd_4083965 < baseStart_4083965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083982 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_4083982 : Nat := 118140960795 + 4083982 * 2 ^ 59
def prefixEnd_4083982 : Nat := 4983230072969 + 3 ^ 40 * 4083982 * 2
def baseEnd_4083982 : Nat := 466010166735632363409581

theorem tailTrace_4083982 : CollatzResearch.WordTrace tailWord_4083982 prefixEnd_4083982 466010166735632363409581 := by
  unfold tailWord_4083982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18619382586304772180100775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99303373793625451627204133 18619382586304772180100775)
  ·
    refine ⟨27929073879457158270151163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18619382586304772180100775 27929073879457158270151163)
    ·
      refine ⟨41893610819185737405226745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27929073879457158270151163 41893610819185737405226745)
      ·
        refine ⟨31420208114389303053920059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41893610819185737405226745 31420208114389303053920059)
        ·
          refine ⟨47130312171583954580880089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31420208114389303053920059 47130312171583954580880089)
          ·
            refine ⟨35347734128687965935660067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47130312171583954580880089 35347734128687965935660067)
            ·
              refine ⟨53021601193031948903490101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35347734128687965935660067 53021601193031948903490101)
              ·
                refine ⟨4970775111846745209702197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53021601193031948903490101 4970775111846745209702197)
                ·
                  refine ⟨466010166735632363409581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4970775111846745209702197 466010166735632363409581)
                  ·
                    rfl

theorem cell22_4083982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_4083982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4083982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4083982 prefixEnd_4083982 := by exact prefixLift 4083982
  have htrace : WordTrace (prefixWord ++ tailWord_4083982) baseStart_4083982 baseEnd_4083982 := by
    simpa [prefixWord, tailWord_4083982, baseEnd_4083982] using wordTrace_append hprefix tailTrace_4083982
  have hstable : (prefixWord ++ tailWord_4083982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083982).length < 2 ^ (prefixWord ++ tailWord_4083982).sum := by decide
  have hdescent : baseEnd_4083982 < baseStart_4083982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084057 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 2, 4]
def baseStart_4084057 : Nat := 118140960795 + 4084057 * 2 ^ 59
def prefixEnd_4084057 : Nat := 4983230072969 + 3 ^ 40 * 4084057 * 2
def baseEnd_4084057 : Nat := 1398056174239621894603513

theorem tailTrace_4084057 : CollatzResearch.WordTrace tailWord_4084057 prefixEnd_4084057 1398056174239621894603513 := by
  unfold tailWord_4084057
  simp only [CollatzResearch.WordTrace]
  refine ⟨148957796165166465249786425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99305197443444310166524283 148957796165166465249786425)
  ·
    refine ⟨111718347123874848937339819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148957796165166465249786425 111718347123874848937339819)
    ·
      refine ⟨167577520685812273406009729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111718347123874848937339819 167577520685812273406009729)
      ·
        refine ⟨125683140514359205054507297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167577520685812273406009729 125683140514359205054507297)
        ·
          refine ⟨94262355385769403790880473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125683140514359205054507297 94262355385769403790880473)
          ·
            refine ⟨70696766539327052843160355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94262355385769403790880473 70696766539327052843160355)
            ·
              refine ⟨106045149808990579264740533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70696766539327052843160355 106045149808990579264740533)
              ·
                refine ⟨9941732794592866806069425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106045149808990579264740533 9941732794592866806069425)
                ·
                  refine ⟨7456299595944650104552069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9941732794592866806069425 7456299595944650104552069)
                  ·
                    refine ⟨1398056174239621894603513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7456299595944650104552069 1398056174239621894603513)
                    ·
                      rfl

theorem cell22_4084057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_4084057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084057 prefixEnd_4084057 := by exact prefixLift 4084057
  have htrace : WordTrace (prefixWord ++ tailWord_4084057) baseStart_4084057 baseEnd_4084057 := by
    simpa [prefixWord, tailWord_4084057, baseEnd_4084057] using wordTrace_append hprefix tailTrace_4084057
  have hstable : (prefixWord ++ tailWord_4084057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084057).length < 2 ^ (prefixWord ++ tailWord_4084057).sum := by decide
  have hdescent : baseEnd_4084057 < baseStart_4084057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084072 : List Nat := [2, 1, 4, 2, 2, 1, 10]
def baseStart_4084072 : Nat := 118140960795 + 4084072 * 2 ^ 59
def prefixEnd_4084072 : Nat := 4983230072969 + 3 ^ 40 * 4084072 * 2
def baseEnd_4084072 : Nat := 51780048483191365017721

theorem tailTrace_4084072 : CollatzResearch.WordTrace tailWord_4084072 prefixEnd_4084072 51780048483191365017721 := by
  unfold tailWord_4084072
  simp only [CollatzResearch.WordTrace]
  refine ⟨74479171630056061405791235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99305562173408081874388313 74479171630056061405791235)
  ·
    refine ⟨111718757445084092108686853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74479171630056061405791235 111718757445084092108686853)
    ·
      refine ⟨20947267020953267270378785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111718757445084092108686853 20947267020953267270378785)
      ·
        refine ⟨15710450265714950452784089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20947267020953267270378785 15710450265714950452784089)
        ·
          refine ⟨11782837699286212839588067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15710450265714950452784089 11782837699286212839588067)
          ·
            refine ⟨17674256548929319259382101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11782837699286212839588067 17674256548929319259382101)
            ·
              refine ⟨51780048483191365017721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17674256548929319259382101 51780048483191365017721)
              ·
                rfl

theorem cell22_4084072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 10].length) (baseStart_4084072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084072 prefixEnd_4084072 := by exact prefixLift 4084072
  have htrace : WordTrace (prefixWord ++ tailWord_4084072) baseStart_4084072 baseEnd_4084072 := by
    simpa [prefixWord, tailWord_4084072, baseEnd_4084072] using wordTrace_append hprefix tailTrace_4084072
  have hstable : (prefixWord ++ tailWord_4084072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084072).length < 2 ^ (prefixWord ++ tailWord_4084072).sum := by decide
  have hdescent : baseEnd_4084072 < baseStart_4084072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084074 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_4084074 : Nat := 118140960795 + 4084074 * 2 ^ 59
def prefixEnd_4084074 : Nat := 4983230072969 + 3 ^ 40 * 4084074 * 2
def baseEnd_4084074 : Nat := 1398061993687039516928461

theorem tailTrace_4084074 : CollatzResearch.WordTrace tailWord_4084074 prefixEnd_4084074 1398061993687039516928461 := by
  unfold tailWord_4084074
  simp only [CollatzResearch.WordTrace]
  refine ⟨37239604051526219288288819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99305610804069918102103517 37239604051526219288288819)
  ·
    refine ⟨55859406077289328932433229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37239604051526219288288819 55859406077289328932433229)
    ·
      refine ⟨20947277278983498349662461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55859406077289328932433229 20947277278983498349662461)
      ·
        refine ⟨7855228979618811881123423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20947277278983498349662461 7855228979618811881123423)
        ·
          refine ⟨11782843469428217821685135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7855228979618811881123423 11782843469428217821685135)
          ·
            refine ⟨17674265204142326732527703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11782843469428217821685135 17674265204142326732527703)
            ·
              refine ⟨26511397806213490098791555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17674265204142326732527703 26511397806213490098791555)
              ·
                refine ⟨39767096709320235148187333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26511397806213490098791555 39767096709320235148187333)
                ·
                  refine ⟨7456330632997544090285125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39767096709320235148187333 7456330632997544090285125)
                  ·
                    refine ⟨1398061993687039516928461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7456330632997544090285125 1398061993687039516928461)
                    ·
                      rfl

theorem cell22_4084074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_4084074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084074 prefixEnd_4084074 := by exact prefixLift 4084074
  have htrace : WordTrace (prefixWord ++ tailWord_4084074) baseStart_4084074 baseEnd_4084074 := by
    simpa [prefixWord, tailWord_4084074, baseEnd_4084074] using wordTrace_append hprefix tailTrace_4084074
  have hstable : (prefixWord ++ tailWord_4084074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084074).length < 2 ^ (prefixWord ++ tailWord_4084074).sum := by decide
  have hdescent : baseEnd_4084074 < baseStart_4084074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084093 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_4084093 : Nat := 118140960795 + 4084093 * 2 ^ 59
def prefixEnd_4084093 : Nat := 4983230072969 + 3 ^ 40 * 4084093 * 2
def baseEnd_4084093 : Nat := 1398068497775329800703403

theorem tailTrace_4084093 : CollatzResearch.WordTrace tailWord_4084093 prefixEnd_4084093 1398068497775329800703403 := by
  unfold tailWord_4084093
  simp only [CollatzResearch.WordTrace]
  refine ⟨148959109193036043398096933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99306072795357362265397955 148959109193036043398096933)
  ·
    refine ⟨27929832973694258137143175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148959109193036043398096933 27929832973694258137143175)
    ·
      refine ⟨41894749460541387205714763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27929832973694258137143175 41894749460541387205714763)
      ·
        refine ⟨62842124190812080808572145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41894749460541387205714763 62842124190812080808572145)
        ·
          refine ⟨47131593143109060606429109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62842124190812080808572145 47131593143109060606429109)
          ·
            refine ⟨4418586857166474431852729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47131593143109060606429109 4418586857166474431852729)
            ·
              refine ⟨3313940142874855823889547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4418586857166474431852729 3313940142874855823889547)
              ·
                refine ⟨4970910214312283735834321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313940142874855823889547 4970910214312283735834321)
                ·
                  refine ⟨3728182660734212801875741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970910214312283735834321 3728182660734212801875741)
                  ·
                    refine ⟨1398068497775329800703403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3728182660734212801875741 1398068497775329800703403)
                    ·
                      rfl

theorem cell22_4084093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_4084093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084093 prefixEnd_4084093 := by exact prefixLift 4084093
  have htrace : WordTrace (prefixWord ++ tailWord_4084093) baseStart_4084093 baseEnd_4084093 := by
    simpa [prefixWord, tailWord_4084093, baseEnd_4084093] using wordTrace_append hprefix tailTrace_4084093
  have hstable : (prefixWord ++ tailWord_4084093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084093).length < 2 ^ (prefixWord ++ tailWord_4084093).sum := by decide
  have hdescent : baseEnd_4084093 < baseStart_4084093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084104 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 5, 3]
def baseStart_4084104 : Nat := 118140960795 + 4084104 * 2 ^ 59
def prefixEnd_4084104 : Nat := 4983230072969 + 3 ^ 40 * 4084104 * 2
def baseEnd_4084104 : Nat := 1398072263300129438678369

theorem tailTrace_4084104 : CollatzResearch.WordTrace tailWord_4084104 prefixEnd_4084104 1398072263300129438678369 := by
  unfold tailWord_4084104
  simp only [CollatzResearch.WordTrace]
  refine ⟨74479755197998096138373683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99306340263997461517831577 74479755197998096138373683)
  ·
    refine ⟨111719632796997144207560525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74479755197998096138373683 111719632796997144207560525)
    ·
      refine ⟨41894862298873929077835197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111719632796997144207560525 41894862298873929077835197)
      ·
        refine ⟨15710573362077723404188199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41894862298873929077835197 15710573362077723404188199)
        ·
          refine ⟨23565860043116585106282299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15710573362077723404188199 23565860043116585106282299)
          ·
            refine ⟨35348790064674877659423449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23565860043116585106282299 35348790064674877659423449)
            ·
              refine ⟨26511592548506158244567587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35348790064674877659423449 26511592548506158244567587)
              ·
                refine ⟨39767388822759237366851381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26511592548506158244567587 39767388822759237366851381)
                ·
                  refine ⟨3728192702133678503142317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39767388822759237366851381 3728192702133678503142317)
                  ·
                    refine ⟨1398072263300129438678369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3728192702133678503142317 1398072263300129438678369)
                    ·
                      rfl

theorem cell22_4084104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_4084104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084104 prefixEnd_4084104 := by exact prefixLift 4084104
  have htrace : WordTrace (prefixWord ++ tailWord_4084104) baseStart_4084104 baseEnd_4084104 := by
    simpa [prefixWord, tailWord_4084104, baseEnd_4084104] using wordTrace_append hprefix tailTrace_4084104
  have hstable : (prefixWord ++ tailWord_4084104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084104).length < 2 ^ (prefixWord ++ tailWord_4084104).sum := by decide
  have hdescent : baseEnd_4084104 < baseStart_4084104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084121 : List Nat := [1, 2, 1, 2, 1, 4, 2, 5, 1, 3]
def baseStart_4084121 : Nat := 118140960795 + 4084121 * 2 ^ 59
def prefixEnd_4084121 : Nat := 4983230072969 + 3 ^ 40 * 4084121 * 2
def baseEnd_4084121 : Nat := 1398078082747547061003317

theorem tailTrace_4084121 : CollatzResearch.WordTrace tailWord_4084121 prefixEnd_4084121 1398078082747547061003317 := by
  unfold tailWord_4084121
  simp only [CollatzResearch.WordTrace]
  refine ⟨148960130436934604180116217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99306753624623069453410811 148960130436934604180116217)
  ·
    refine ⟨111720097827700953135087163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148960130436934604180116217 111720097827700953135087163)
    ·
      refine ⟨167580146741551429702630745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111720097827700953135087163 167580146741551429702630745)
      ·
        refine ⟨125685110056163572276973059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167580146741551429702630745 125685110056163572276973059)
        ·
          refine ⟨188527665084245358415459589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125685110056163572276973059 188527665084245358415459589)
          ·
            refine ⟨35348937203296004702898673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188527665084245358415459589 35348937203296004702898673)
            ·
              refine ⟨26511702902472003527174005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35348937203296004702898673 26511702902472003527174005)
              ·
                refine ⟨2485472147106750330672563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26511702902472003527174005 2485472147106750330672563)
                ·
                  refine ⟨3728208220660125496008845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2485472147106750330672563 3728208220660125496008845)
                  ·
                    refine ⟨1398078082747547061003317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3728208220660125496008845 1398078082747547061003317)
                    ·
                      rfl

theorem cell22_4084121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 1, 3].length) (baseStart_4084121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084121 prefixEnd_4084121 := by exact prefixLift 4084121
  have htrace : WordTrace (prefixWord ++ tailWord_4084121) baseStart_4084121 baseEnd_4084121 := by
    simpa [prefixWord, tailWord_4084121, baseEnd_4084121] using wordTrace_append hprefix tailTrace_4084121
  have hstable : (prefixWord ++ tailWord_4084121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084121).length < 2 ^ (prefixWord ++ tailWord_4084121).sum := by decide
  have hdescent : baseEnd_4084121 < baseStart_4084121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084181 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_4084181 : Nat := 118140960795 + 4084181 * 2 ^ 59
def prefixEnd_4084181 : Nat := 4983230072969 + 3 ^ 40 * 4084181 * 2
def baseEnd_4084181 : Nat := 1398098621973726904503133

theorem tailTrace_4084181 : CollatzResearch.WordTrace tailWord_4084181 prefixEnd_4084181 1398098621973726904503133 := by
  unfold tailWord_4084181
  simp only [CollatzResearch.WordTrace]
  refine ⟨148962318816717234427300397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99308212544478156284866931 148962318816717234427300397)
  ·
    refine ⟨55860869556268962910237649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148962318816717234427300397 55860869556268962910237649)
    ·
      refine ⟨41895652167201722182678237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55860869556268962910237649 41895652167201722182678237)
      ·
        refine ⟨15710869562700645818504339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41895652167201722182678237 15710869562700645818504339)
        ·
          refine ⟨23566304344050968727756509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15710869562700645818504339 23566304344050968727756509)
          ·
            refine ⟨8837364129019113272908691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23566304344050968727756509 8837364129019113272908691)
            ·
              refine ⟨13256046193528669909363037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8837364129019113272908691 13256046193528669909363037)
              ·
                refine ⟨4971017322573251216011139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13256046193528669909363037 4971017322573251216011139)
                ·
                  refine ⟨7456525983859876824016709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4971017322573251216011139 7456525983859876824016709)
                  ·
                    refine ⟨1398098621973726904503133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7456525983859876824016709 1398098621973726904503133)
                    ·
                      rfl

theorem cell22_4084181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_4084181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084181 prefixEnd_4084181 := by exact prefixLift 4084181
  have htrace : WordTrace (prefixWord ++ tailWord_4084181) baseStart_4084181 baseEnd_4084181 := by
    simpa [prefixWord, tailWord_4084181, baseEnd_4084181] using wordTrace_append hprefix tailTrace_4084181
  have hstable : (prefixWord ++ tailWord_4084181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084181).length < 2 ^ (prefixWord ++ tailWord_4084181).sum := by decide
  have hdescent : baseEnd_4084181 < baseStart_4084181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084207 : List Nat := [1, 1, 2, 1, 4, 1, 1, 11]
def baseStart_4084207 : Nat := 118140960795 + 4084207 * 2 ^ 59
def prefixEnd_4084207 : Nat := 4983230072969 + 3 ^ 40 * 4084207 * 2
def baseEnd_4084207 : Nat := 155345280256119055928117

theorem tailTrace_4084207 : CollatzResearch.WordTrace tailWord_4084207 prefixEnd_4084207 155345280256119055928117 := by
  unfold tailWord_4084207
  simp only [CollatzResearch.WordTrace]
  refine ⟨148963267114623040867746875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99308844743082027245164583 148963267114623040867746875)
  ·
    refine ⟨223444900671934561301620313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148963267114623040867746875 223444900671934561301620313)
    ·
      refine ⟨167583675503950920976215235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223444900671934561301620313 167583675503950920976215235)
      ·
        refine ⟨251375513255926381464322853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167583675503950920976215235 251375513255926381464322853)
        ·
          refine ⟨47132908735486196524560535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251375513255926381464322853 47132908735486196524560535)
          ·
            refine ⟨70699363103229294786840803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47132908735486196524560535 70699363103229294786840803)
            ·
              refine ⟨106049044654843942180261205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70699363103229294786840803 106049044654843942180261205)
              ·
                refine ⟨155345280256119055928117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 106049044654843942180261205 155345280256119055928117)
                ·
                  rfl

theorem cell22_4084207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 11].length) (baseStart_4084207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084207 prefixEnd_4084207 := by exact prefixLift 4084207
  have htrace : WordTrace (prefixWord ++ tailWord_4084207) baseStart_4084207 baseEnd_4084207 := by
    simpa [prefixWord, tailWord_4084207, baseEnd_4084207] using wordTrace_append hprefix tailTrace_4084207
  have hstable : (prefixWord ++ tailWord_4084207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084207).length < 2 ^ (prefixWord ++ tailWord_4084207).sum := by decide
  have hdescent : baseEnd_4084207 < baseStart_4084207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084239 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 7, 3]
def baseStart_4084239 : Nat := 118140960795 + 4084239 * 2 ^ 59
def prefixEnd_4084239 : Nat := 4983230072969 + 3 ^ 40 * 4084239 * 2
def baseEnd_4084239 : Nat := 1398118476559034086552955

theorem tailTrace_4084239 : CollatzResearch.WordTrace tailWord_4084239 prefixEnd_4084239 1398118476559034086552955 := by
  unfold tailWord_4084239
  simp only [CollatzResearch.WordTrace]
  refine ⟨148964434250507110332911771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99309622833671406888607847 148964434250507110332911771)
  ·
    refine ⟨223446651375760665499367657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148964434250507110332911771 223446651375760665499367657)
    ·
      refine ⟨167584988531820499124525743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223446651375760665499367657 167584988531820499124525743)
      ·
        refine ⟨251377482797730748686788615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167584988531820499124525743 251377482797730748686788615)
        ·
          refine ⟨377066224196596123030182923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251377482797730748686788615 377066224196596123030182923)
          ·
            refine ⟨565599336294894184545274385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377066224196596123030182923 565599336294894184545274385)
            ·
              refine ⟨424199502221170638408955789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565599336294894184545274385 424199502221170638408955789)
              ·
                refine ⟨159074813332938989403358421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424199502221170638408955789 159074813332938989403358421)
                ·
                  refine ⟨3728315937490757564141213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 159074813332938989403358421 3728315937490757564141213)
                  ·
                    refine ⟨1398118476559034086552955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3728315937490757564141213 1398118476559034086552955)
                    ·
                      rfl

theorem cell22_4084239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 3].length) (baseStart_4084239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084239 prefixEnd_4084239 := by exact prefixLift 4084239
  have htrace : WordTrace (prefixWord ++ tailWord_4084239) baseStart_4084239 baseEnd_4084239 := by
    simpa [prefixWord, tailWord_4084239, baseEnd_4084239] using wordTrace_append hprefix tailTrace_4084239
  have hstable : (prefixWord ++ tailWord_4084239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084239).length < 2 ^ (prefixWord ++ tailWord_4084239).sum := by decide
  have hdescent : baseEnd_4084239 < baseStart_4084239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084344 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_4084344 : Nat := 118140960795 + 4084344 * 2 ^ 59
def prefixEnd_4084344 : Nat := 4983230072969 + 3 ^ 40 * 4084344 * 2
def baseEnd_4084344 : Nat := 1398154420204848812677633

theorem tailTrace_4084344 : CollatzResearch.WordTrace tailWord_4084344 prefixEnd_4084344 1398154420204848812677633 := by
  unfold tailWord_4084344
  simp only [CollatzResearch.WordTrace]
  refine ⟨74484131957563356632742043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99312175943417808843656057 74484131957563356632742043)
  ·
    refine ⟨111726197936345034949113065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74484131957563356632742043 111726197936345034949113065)
    ·
      refine ⟨83794648452258776211834799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111726197936345034949113065 83794648452258776211834799)
      ·
        refine ⟨125691972678388164317752199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83794648452258776211834799 125691972678388164317752199)
        ·
          refine ⟨188537959017582246476628299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125691972678388164317752199 188537959017582246476628299)
          ·
            refine ⟨282806938526373369714942449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188537959017582246476628299 282806938526373369714942449)
            ·
              refine ⟨212105203894780027286206837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282806938526373369714942449 212105203894780027286206837)
              ·
                refine ⟨19884862865135627558081891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212105203894780027286206837 19884862865135627558081891)
                ·
                  refine ⟨29827294297703441337122837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19884862865135627558081891 29827294297703441337122837)
                  ·
                    refine ⟨1398154420204848812677633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29827294297703441337122837 1398154420204848812677633)
                    ·
                      rfl

theorem cell22_4084344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_4084344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084344 prefixEnd_4084344 := by exact prefixLift 4084344
  have htrace : WordTrace (prefixWord ++ tailWord_4084344) baseStart_4084344 baseEnd_4084344 := by
    simpa [prefixWord, tailWord_4084344, baseEnd_4084344] using wordTrace_append hprefix tailTrace_4084344
  have hstable : (prefixWord ++ tailWord_4084344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084344).length < 2 ^ (prefixWord ++ tailWord_4084344).sum := by decide
  have hdescent : baseEnd_4084344 < baseStart_4084344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084354 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 5]
def baseStart_4084354 : Nat := 118140960795 + 4084354 * 2 ^ 59
def prefixEnd_4084354 : Nat := 4983230072969 + 3 ^ 40 * 4084354 * 2
def baseEnd_4084354 : Nat := 466052614469737373309201

theorem tailTrace_4084354 : CollatzResearch.WordTrace tailWord_4084354 prefixEnd_4084354 466052614469737373309201 := by
  unfold tailWord_4084354
  simp only [CollatzResearch.WordTrace]
  refine ⟨37242157161272621243337029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99312419096726989982232077 37242157161272621243337029)
  ·
    refine ⟨6982904467738616483125693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37242157161272621243337029 6982904467738616483125693)
    ·
      refine ⟨2618589175401981181172135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6982904467738616483125693 2618589175401981181172135)
      ·
        refine ⟨3927883763102971771758203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618589175401981181172135 3927883763102971771758203)
        ·
          refine ⟨5891825644654457657637305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927883763102971771758203 5891825644654457657637305)
          ·
            refine ⟨4418869233490843243227979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5891825644654457657637305 4418869233490843243227979)
            ·
              refine ⟨6628303850236264864841969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418869233490843243227979 6628303850236264864841969)
              ·
                refine ⟨4971227887677198648631477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6628303850236264864841969 4971227887677198648631477)
                ·
                  refine ⟨466052614469737373309201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4971227887677198648631477 466052614469737373309201)
                  ·
                    rfl

theorem cell22_4084354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_4084354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084354 prefixEnd_4084354 := by exact prefixLift 4084354
  have htrace : WordTrace (prefixWord ++ tailWord_4084354) baseStart_4084354 baseEnd_4084354 := by
    simpa [prefixWord, tailWord_4084354, baseEnd_4084354] using wordTrace_append hprefix tailTrace_4084354
  have hstable : (prefixWord ++ tailWord_4084354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084354).length < 2 ^ (prefixWord ++ tailWord_4084354).sum := by decide
  have hdescent : baseEnd_4084354 < baseStart_4084354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084359 : List Nat := [1, 1, 4, 2, 1, 2, 11]
def baseStart_4084359 : Nat := 118140960795 + 4084359 * 2 ^ 59
def prefixEnd_4084359 : Nat := 4983230072969 + 3 ^ 40 * 4084359 * 2
def baseEnd_4084359 : Nat := 51783687222644213835281

theorem tailTrace_4084359 : CollatzResearch.WordTrace tailWord_4084359 prefixEnd_4084359 51783687222644213835281 := by
  unfold tailWord_4084359
  simp only [CollatzResearch.WordTrace]
  refine ⟨148968811010072370827280131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99312540673381580551520087 148968811010072370827280131)
  ·
    refine ⟨223453216515108556240920197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148968811010072370827280131 223453216515108556240920197)
    ·
      refine ⟨41897478096582854295172537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223453216515108556240920197 41897478096582854295172537)
      ·
        refine ⟨31423108572437140721379403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41897478096582854295172537 31423108572437140721379403)
        ·
          refine ⟨47134662858655711082069105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31423108572437140721379403 47134662858655711082069105)
          ·
            refine ⟨35350997143991783311551829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47134662858655711082069105 35350997143991783311551829)
            ·
              refine ⟨51783687222644213835281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35350997143991783311551829 51783687222644213835281)
              ·
                rfl

theorem cell22_4084359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 11].length) (baseStart_4084359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084359 prefixEnd_4084359 := by exact prefixLift 4084359
  have htrace : WordTrace (prefixWord ++ tailWord_4084359) baseStart_4084359 baseEnd_4084359 := by
    simpa [prefixWord, tailWord_4084359, baseEnd_4084359] using wordTrace_append hprefix tailTrace_4084359
  have hstable : (prefixWord ++ tailWord_4084359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084359).length < 2 ^ (prefixWord ++ tailWord_4084359).sum := by decide
  have hdescent : baseEnd_4084359 < baseStart_4084359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084481 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_4084481 : Nat := 118140960795 + 4084481 * 2 ^ 59
def prefixEnd_4084481 : Nat := 4983230072969 + 3 ^ 40 * 4084481 * 2
def baseEnd_4084481 : Nat := 1398201318104626122002213

theorem tailTrace_4084481 : CollatzResearch.WordTrace tailWord_4084481 prefixEnd_4084481 1398201318104626122002213 := by
  unfold tailWord_4084481
  simp only [CollatzResearch.WordTrace]
  refine ⟨148973260715630385663221297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99315507143753590442147531 148973260715630385663221297)
  ·
    refine ⟨111729945536722789247415973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148973260715630385663221297 111729945536722789247415973)
    ·
      refine ⟨20949364788135522983890495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111729945536722789247415973 20949364788135522983890495)
      ·
        refine ⟨31424047182203284475835743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20949364788135522983890495 31424047182203284475835743)
        ·
          refine ⟨47136070773304926713753615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31424047182203284475835743 47136070773304926713753615)
          ·
            refine ⟨70704106159957390070630423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47136070773304926713753615 70704106159957390070630423)
            ·
              refine ⟨106056159239936085105945635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70704106159957390070630423 106056159239936085105945635)
              ·
                refine ⟨159084238859904127658918453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106056159239936085105945635 159084238859904127658918453)
                ·
                  refine ⟨14914147393116011968023605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159084238859904127658918453 14914147393116011968023605)
                  ·
                    refine ⟨1398201318104626122002213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14914147393116011968023605 1398201318104626122002213)
                    ·
                      rfl

theorem cell22_4084481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_4084481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084481 prefixEnd_4084481 := by exact prefixLift 4084481
  have htrace : WordTrace (prefixWord ++ tailWord_4084481) baseStart_4084481 baseEnd_4084481 := by
    simpa [prefixWord, tailWord_4084481, baseEnd_4084481] using wordTrace_append hprefix tailTrace_4084481
  have hstable : (prefixWord ++ tailWord_4084481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084481).length < 2 ^ (prefixWord ++ tailWord_4084481).sum := by decide
  have hdescent : baseEnd_4084481 < baseStart_4084481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084532 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_4084532 : Nat := 118140960795 + 4084532 * 2 ^ 59
def prefixEnd_4084532 : Nat := 4983230072969 + 3 ^ 40 * 4084532 * 2
def baseEnd_4084532 : Nat := 1398218776446878988977057

theorem tailTrace_4084532 : CollatzResearch.WordTrace tailWord_4084532 prefixEnd_4084532 1398218776446878988977057 := by
  unfold tailWord_4084532
  simp only [CollatzResearch.WordTrace]
  refine ⟨74487560419222810686663925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99316747225630414248885233 74487560419222810686663925)
  ·
    refine ⟨6983208789302138501874743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74487560419222810686663925 6983208789302138501874743)
    ·
      refine ⟨10474813183953207752812115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6983208789302138501874743 10474813183953207752812115)
      ·
        refine ⟨15712219775929811629218173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10474813183953207752812115 15712219775929811629218173)
        ·
          refine ⟨5892082415973679360956815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15712219775929811629218173 5892082415973679360956815)
          ·
            refine ⟨8838123623960519041435223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892082415973679360956815 8838123623960519041435223)
            ·
              refine ⟨13257185435940778562152835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838123623960519041435223 13257185435940778562152835)
              ·
                refine ⟨19885778153911167843229253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13257185435940778562152835 19885778153911167843229253)
                ·
                  refine ⟨3728583403858343970605485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19885778153911167843229253 3728583403858343970605485)
                  ·
                    refine ⟨1398218776446878988977057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3728583403858343970605485 1398218776446878988977057)
                    ·
                      rfl

theorem cell22_4084532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_4084532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084532 prefixEnd_4084532 := by exact prefixLift 4084532
  have htrace : WordTrace (prefixWord ++ tailWord_4084532) baseStart_4084532 baseEnd_4084532 := by
    simpa [prefixWord, tailWord_4084532, baseEnd_4084532] using wordTrace_append hprefix tailTrace_4084532
  have hstable : (prefixWord ++ tailWord_4084532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084532).length < 2 ^ (prefixWord ++ tailWord_4084532).sum := by decide
  have hdescent : baseEnd_4084532 < baseStart_4084532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084620 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_4084620 : Nat := 118140960795 + 4084620 * 2 ^ 59
def prefixEnd_4084620 : Nat := 4983230072969 + 3 ^ 40 * 4084620 * 2
def baseEnd_4084620 : Nat := 1398248900645276092776787

theorem tailTrace_4084620 : CollatzResearch.WordTrace tailWord_4084620 prefixEnd_4084620 1398248900645276092776787 := by
  unfold tailWord_4084620
  simp only [CollatzResearch.WordTrace]
  refine ⟨74489165231063406201265657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99318886974751208268354209 74489165231063406201265657)
  ·
    refine ⟨55866873923297554650949243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74489165231063406201265657 55866873923297554650949243)
    ·
      refine ⟨83800310884946331976423865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55866873923297554650949243 83800310884946331976423865)
      ·
        refine ⟨62850233163709748982317899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83800310884946331976423865 62850233163709748982317899)
        ·
          refine ⟨94275349745564623473476849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62850233163709748982317899 94275349745564623473476849)
          ·
            refine ⟨70706512309173467605107637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94275349745564623473476849 70706512309173467605107637)
            ·
              refine ⟨6628735528985012587978841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70706512309173467605107637 6628735528985012587978841)
              ·
                refine ⟨4971551646738759440984131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6628735528985012587978841 4971551646738759440984131)
                ·
                  refine ⟨7457327470108139161476197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4971551646738759440984131 7457327470108139161476197)
                  ·
                    refine ⟨1398248900645276092776787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7457327470108139161476197 1398248900645276092776787)
                    ·
                      rfl

theorem cell22_4084620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_4084620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084620 prefixEnd_4084620 := by exact prefixLift 4084620
  have htrace : WordTrace (prefixWord ++ tailWord_4084620) baseStart_4084620 baseEnd_4084620 := by
    simpa [prefixWord, tailWord_4084620, baseEnd_4084620] using wordTrace_append hprefix tailTrace_4084620
  have hstable : (prefixWord ++ tailWord_4084620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084620).length < 2 ^ (prefixWord ++ tailWord_4084620).sum := by decide
  have hdescent : baseEnd_4084620 < baseStart_4084620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084637 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_4084637 : Nat := 118140960795 + 4084637 * 2 ^ 59
def prefixEnd_4084637 : Nat := 4983230072969 + 3 ^ 40 * 4084637 * 2
def baseEnd_4084637 : Nat := 1398254720092693715101735

theorem tailTrace_4084637 : CollatzResearch.WordTrace tailWord_4084637 prefixEnd_4084637 1398254720092693715101735 := by
  unfold tailWord_4084637
  simp only [CollatzResearch.WordTrace]
  refine ⟨148978950503065224305900165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99319300335376816203933443 148978950503065224305900165)
  ·
    refine ⟨27933553219324729557356281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148978950503065224305900165 27933553219324729557356281)
    ·
      refine ⟨20950164914493547168017211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27933553219324729557356281 20950164914493547168017211)
      ·
        refine ⟨31425247371740320752025817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20950164914493547168017211 31425247371740320752025817)
        ·
          refine ⟨23568935528805240564019363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31425247371740320752025817 23568935528805240564019363)
          ·
            refine ⟨35353403293207860846029045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23568935528805240564019363 35353403293207860846029045)
            ·
              refine ⟨3314381558738236954315223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35353403293207860846029045 3314381558738236954315223)
              ·
                refine ⟨4971572338107355431472835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314381558738236954315223 4971572338107355431472835)
                ·
                  refine ⟨7457358507161033147209253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4971572338107355431472835 7457358507161033147209253)
                  ·
                    refine ⟨1398254720092693715101735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7457358507161033147209253 1398254720092693715101735)
                    ·
                      rfl

theorem cell22_4084637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_4084637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084637 prefixEnd_4084637 := by exact prefixLift 4084637
  have htrace : WordTrace (prefixWord ++ tailWord_4084637) baseStart_4084637 baseEnd_4084637 := by
    simpa [prefixWord, tailWord_4084637, baseEnd_4084637] using wordTrace_append hprefix tailTrace_4084637
  have hstable : (prefixWord ++ tailWord_4084637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084637).length < 2 ^ (prefixWord ++ tailWord_4084637).sum := by decide
  have hdescent : baseEnd_4084637 < baseStart_4084637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084663 : List Nat := [1, 1, 3, 1, 3, 1, 5, 7]
def baseStart_4084663 : Nat := 118140960795 + 4084663 * 2 ^ 59
def prefixEnd_4084663 : Nat := 4983230072969 + 3 ^ 40 * 4084663 * 2
def baseEnd_4084663 : Nat := 155362624491559812661295

theorem tailTrace_4084663 : CollatzResearch.WordTrace tailWord_4084663 prefixEnd_4084663 155362624491559812661295 := by
  unfold tailWord_4084663
  simp only [CollatzResearch.WordTrace]
  refine ⟨148979898800971030746346643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99319932533980687164231095 148979898800971030746346643)
  ·
    refine ⟨223469848201456546119519965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148979898800971030746346643 223469848201456546119519965)
    ·
      refine ⟨83801193075546204794819987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223469848201456546119519965 83801193075546204794819987)
      ·
        refine ⟨125701789613319307192229981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83801193075546204794819987 125701789613319307192229981)
        ·
          refine ⟨47138171104994740197086243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125701789613319307192229981 47138171104994740197086243)
          ·
            refine ⟨70707256657492110295629365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47138171104994740197086243 70707256657492110295629365)
            ·
              refine ⟨6628805311639885340215253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70707256657492110295629365 6628805311639885340215253)
              ·
                refine ⟨155362624491559812661295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6628805311639885340215253 155362624491559812661295)
                ·
                  rfl

theorem cell22_4084663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 7].length) (baseStart_4084663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084663 prefixEnd_4084663 := by exact prefixLift 4084663
  have htrace : WordTrace (prefixWord ++ tailWord_4084663) baseStart_4084663 baseEnd_4084663 := by
    simpa [prefixWord, tailWord_4084663, baseEnd_4084663] using wordTrace_append hprefix tailTrace_4084663
  have hstable : (prefixWord ++ tailWord_4084663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084663).length < 2 ^ (prefixWord ++ tailWord_4084663).sum := by decide
  have hdescent : baseEnd_4084663 < baseStart_4084663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084746 : List Nat := [3, 1, 2, 2, 3, 3, 1, 3, 1, 3]
def baseStart_4084746 : Nat := 118140960795 + 4084746 * 2 ^ 59
def prefixEnd_4084746 : Nat := 4983230072969 + 3 ^ 40 * 4084746 * 2
def baseEnd_4084746 : Nat := 1398292033020253764126401

theorem tailTrace_4084746 : CollatzResearch.WordTrace tailWord_4084746 prefixEnd_4084746 1398292033020253764126401 := by
  unfold tailWord_4084746
  simp only [CollatzResearch.WordTrace]
  refine ⟨37245731514917583980404523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99321950706446890614412061 37245731514917583980404523)
  ·
    refine ⟨55868597272376375970606785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37245731514917583980404523 55868597272376375970606785)
    ·
      refine ⟨41901447954282281977955089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55868597272376375970606785 41901447954282281977955089)
      ·
        refine ⟨31426085965711711483466317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41901447954282281977955089 31426085965711711483466317)
        ·
          refine ⟨11784782237141891806299869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31426085965711711483466317 11784782237141891806299869)
          ·
            refine ⟨4419293338928209427362451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11784782237141891806299869 4419293338928209427362451)
            ·
              refine ⟨6628940008392314141043677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419293338928209427362451 6628940008392314141043677)
              ·
                refine ⟨2485852503147117802891379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6628940008392314141043677 2485852503147117802891379)
                ·
                  refine ⟨3728778754720676704337069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2485852503147117802891379 3728778754720676704337069)
                  ·
                    refine ⟨1398292033020253764126401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3728778754720676704337069 1398292033020253764126401)
                    ·
                      rfl

theorem cell22_4084746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_4084746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084746 prefixEnd_4084746 := by exact prefixLift 4084746
  have htrace : WordTrace (prefixWord ++ tailWord_4084746) baseStart_4084746 baseEnd_4084746 := by
    simpa [prefixWord, tailWord_4084746, baseEnd_4084746] using wordTrace_append hprefix tailTrace_4084746
  have hstable : (prefixWord ++ tailWord_4084746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084746).length < 2 ^ (prefixWord ++ tailWord_4084746).sum := by decide
  have hdescent : baseEnd_4084746 < baseStart_4084746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084753 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 8]
def baseStart_4084753 : Nat := 118140960795 + 4084753 * 2 ^ 59
def prefixEnd_4084753 : Nat := 4983230072969 + 3 ^ 40 * 4084753 * 2
def baseEnd_4084753 : Nat := 466098143087769359733793

theorem tailTrace_4084753 : CollatzResearch.WordTrace tailWord_4084753 prefixEnd_4084753 466098143087769359733793 := by
  unfold tailWord_4084753
  simp only [CollatzResearch.WordTrace]
  refine ⟨148983181370644976117122913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99322120913763317411415275 148983181370644976117122913)
  ·
    refine ⟨111737386027983732087842185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148983181370644976117122913 111737386027983732087842185)
    ·
      refine ⟨83803039520987799065881639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111737386027983732087842185 83803039520987799065881639)
      ·
        refine ⟨125704559281481698598822459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83803039520987799065881639 125704559281481698598822459)
        ·
          refine ⟨188556838922222547898233689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125704559281481698598822459 188556838922222547898233689)
          ·
            refine ⟨141417629191666910923675267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188556838922222547898233689 141417629191666910923675267)
            ·
              refine ⟨212126443787500366385512901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141417629191666910923675267 212126443787500366385512901)
              ·
                refine ⟨39773708210156318697283669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212126443787500366385512901 39773708210156318697283669)
                ·
                  refine ⟨466098143087769359733793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39773708210156318697283669 466098143087769359733793)
                  ·
                    rfl

theorem cell22_4084753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_4084753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084753 prefixEnd_4084753 := by exact prefixLift 4084753
  have htrace : WordTrace (prefixWord ++ tailWord_4084753) baseStart_4084753 baseEnd_4084753 := by
    simpa [prefixWord, tailWord_4084753, baseEnd_4084753] using wordTrace_append hprefix tailTrace_4084753
  have hstable : (prefixWord ++ tailWord_4084753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084753).length < 2 ^ (prefixWord ++ tailWord_4084753).sum := by decide
  have hdescent : baseEnd_4084753 < baseStart_4084753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084785 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 1, 5]
def baseStart_4084785 : Nat := 118140960795 + 4084785 * 2 ^ 59
def prefixEnd_4084785 : Nat := 4983230072969 + 3 ^ 40 * 4084785 * 2
def baseEnd_4084785 : Nat := 1398305383517270662401281

theorem tailTrace_4084785 : CollatzResearch.WordTrace tailWord_4084785 prefixEnd_4084785 1398305383517270662401281 := by
  unfold tailWord_4084785
  simp only [CollatzResearch.WordTrace]
  refine ⟨148984348506529045582287809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99322899004352697054858539 148984348506529045582287809)
  ·
    refine ⟨111738261379896784186715857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148984348506529045582287809 111738261379896784186715857)
    ·
      refine ⟨83803696034922588140036893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111738261379896784186715857 83803696034922588140036893)
      ·
        refine ⟨31426386013095970552513835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83803696034922588140036893 31426386013095970552513835)
        ·
          refine ⟨47139579019643955828770753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31426386013095970552513835 47139579019643955828770753)
          ·
            refine ⟨35354684264732966871578065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47139579019643955828770753 35354684264732966871578065)
            ·
              refine ⟨26516013198549725153683549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35354684264732966871578065 26516013198549725153683549)
              ·
                refine ⟨9943504949456146932631331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26516013198549725153683549 9943504949456146932631331)
                ·
                  refine ⟨14915257424184220398946997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9943504949456146932631331 14915257424184220398946997)
                  ·
                    refine ⟨1398305383517270662401281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14915257424184220398946997 1398305383517270662401281)
                    ·
                      rfl

theorem cell22_4084785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_4084785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084785 prefixEnd_4084785 := by exact prefixLift 4084785
  have htrace : WordTrace (prefixWord ++ tailWord_4084785) baseStart_4084785 baseEnd_4084785 := by
    simpa [prefixWord, tailWord_4084785, baseEnd_4084785] using wordTrace_append hprefix tailTrace_4084785
  have hstable : (prefixWord ++ tailWord_4084785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084785).length < 2 ^ (prefixWord ++ tailWord_4084785).sum := by decide
  have hdescent : baseEnd_4084785 < baseStart_4084785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084847 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 3, 3]
def baseStart_4084847 : Nat := 118140960795 + 4084847 * 2 ^ 59
def prefixEnd_4084847 : Nat := 4983230072969 + 3 ^ 40 * 4084847 * 2
def baseEnd_4084847 : Nat := 1398326607384323167351091

theorem tailTrace_4084847 : CollatzResearch.WordTrace tailWord_4084847 prefixEnd_4084847 1398326607384323167351091 := by
  unfold tailWord_4084847
  simp only [CollatzResearch.WordTrace]
  refine ⟨148986609832304430171044795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99324406554869620114029863 148986609832304430171044795)
  ·
    refine ⟨223479914748456645256567193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148986609832304430171044795 223479914748456645256567193)
    ·
      refine ⟨167609936061342483942425395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223479914748456645256567193 167609936061342483942425395)
      ·
        refine ⟨251414904092013725913638093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167609936061342483942425395 251414904092013725913638093)
        ·
          refine ⟨94280589034505147217614285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251414904092013725913638093 94280589034505147217614285)
          ·
            refine ⟨35355220887939430206605357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94280589034505147217614285 35355220887939430206605357)
            ·
              refine ⟨13258207832977286327477009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35355220887939430206605357 13258207832977286327477009)
              ·
                refine ⟨9943655874732964745607757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13258207832977286327477009 9943655874732964745607757)
                ·
                  refine ⟨3728870953024861779602909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9943655874732964745607757 3728870953024861779602909)
                  ·
                    refine ⟨1398326607384323167351091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3728870953024861779602909 1398326607384323167351091)
                    ·
                      rfl

theorem cell22_4084847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 3].length) (baseStart_4084847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084847 prefixEnd_4084847 := by exact prefixLift 4084847
  have htrace : WordTrace (prefixWord ++ tailWord_4084847) baseStart_4084847 baseEnd_4084847 := by
    simpa [prefixWord, tailWord_4084847, baseEnd_4084847] using wordTrace_append hprefix tailTrace_4084847
  have hstable : (prefixWord ++ tailWord_4084847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084847).length < 2 ^ (prefixWord ++ tailWord_4084847).sum := by decide
  have hdescent : baseEnd_4084847 < baseStart_4084847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084860 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 7]
def baseStart_4084860 : Nat := 118140960795 + 4084860 * 2 ^ 59
def prefixEnd_4084860 : Nat := 4983230072969 + 3 ^ 40 * 4084860 * 2
def baseEnd_4084860 : Nat := 466110352516665155592017

theorem tailTrace_4084860 : CollatzResearch.WordTrace tailWord_4084860 prefixEnd_4084860 466110352516665155592017 := by
  unfold tailWord_4084860
  simp only [CollatzResearch.WordTrace]
  refine ⟨74493541990628666695634017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99324722654171555594178689 74493541990628666695634017)
  ·
    refine ⟨55870156492971500021725513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74493541990628666695634017 55870156492971500021725513)
    ·
      refine ⟨41902617369728625016294135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55870156492971500021725513 41902617369728625016294135)
      ·
        refine ⟨62853926054592937524441203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41902617369728625016294135 62853926054592937524441203)
        ·
          refine ⟨94280889081889406286661805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62853926054592937524441203 94280889081889406286661805)
          ·
            refine ⟨35355333405708527357498177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94280889081889406286661805 35355333405708527357498177)
            ·
              refine ⟨26516500054281395518123633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35355333405708527357498177 26516500054281395518123633)
              ·
                refine ⟨19887375040711046638592725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26516500054281395518123633 19887375040711046638592725)
                ·
                  refine ⟨466110352516665155592017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19887375040711046638592725 466110352516665155592017)
                  ·
                    rfl

theorem cell22_4084860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_4084860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084860 prefixEnd_4084860 := by exact prefixLift 4084860
  have htrace : WordTrace (prefixWord ++ tailWord_4084860) baseStart_4084860 baseEnd_4084860 := by
    simpa [prefixWord, tailWord_4084860, baseEnd_4084860] using wordTrace_append hprefix tailTrace_4084860
  have hstable : (prefixWord ++ tailWord_4084860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084860).length < 2 ^ (prefixWord ++ tailWord_4084860).sum := by decide
  have hdescent : baseEnd_4084860 < baseStart_4084860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084864 : List Nat := [2, 1, 1, 2, 1, 3, 3, 5, 1, 3]
def baseStart_4084864 : Nat := 118140960795 + 4084864 * 2 ^ 59
def prefixEnd_4084864 : Nat := 4983230072969 + 3 ^ 40 * 4084864 * 2
def baseEnd_4084864 : Nat := 1398332426831740789676039

theorem tailTrace_4084864 : CollatzResearch.WordTrace tailWord_4084864 prefixEnd_4084864 1398332426831740789676039 := by
  unfold tailWord_4084864
  simp only [CollatzResearch.WordTrace]
  refine ⟨74493614936621421037206823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99324819915495228049609097 74493614936621421037206823)
  ·
    refine ⟨111740422404932131555810235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74493614936621421037206823 111740422404932131555810235)
    ·
      refine ⟨167610633607398197333715353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111740422404932131555810235 167610633607398197333715353)
      ·
        refine ⟨125707975205548648000286515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167610633607398197333715353 125707975205548648000286515)
        ·
          refine ⟨188561962808322972000429773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125707975205548648000286515 188561962808322972000429773)
          ·
            refine ⟨70710736053121114500161165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188561962808322972000429773 70710736053121114500161165)
            ·
              refine ⟨26516526019920417937560437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70710736053121114500161165 26516526019920417937560437)
              ·
                refine ⟨2485924314367539181646291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26516526019920417937560437 2485924314367539181646291)
                ·
                  refine ⟨3728886471551308772469437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2485924314367539181646291 3728886471551308772469437)
                  ·
                    refine ⟨1398332426831740789676039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3728886471551308772469437 1398332426831740789676039)
                    ·
                      rfl

theorem cell22_4084864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 1, 3].length) (baseStart_4084864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084864 prefixEnd_4084864 := by exact prefixLift 4084864
  have htrace : WordTrace (prefixWord ++ tailWord_4084864) baseStart_4084864 baseEnd_4084864 := by
    simpa [prefixWord, tailWord_4084864, baseEnd_4084864] using wordTrace_append hprefix tailTrace_4084864
  have hstable : (prefixWord ++ tailWord_4084864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084864).length < 2 ^ (prefixWord ++ tailWord_4084864).sum := by decide
  have hdescent : baseEnd_4084864 < baseStart_4084864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084892 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_4084892 : Nat := 118140960795 + 4084892 * 2 ^ 59
def prefixEnd_4084892 : Nat := 4983230072969 + 3 ^ 40 * 4084892 * 2
def baseEnd_4084892 : Nat := 1398342011803958049975953

theorem tailTrace_4084892 : CollatzResearch.WordTrace tailWord_4084892 prefixEnd_4084892 1398342011803958049975953 := by
  unfold tailWord_4084892
  simp only [CollatzResearch.WordTrace]
  refine ⟨74494125558570701428216465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99325500744760935237621953 74494125558570701428216465)
  ·
    refine ⟨55870594168928026071162349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74494125558570701428216465 55870594168928026071162349)
    ·
      refine ⟨20951472813348009776685881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55870594168928026071162349 20951472813348009776685881)
      ·
        refine ⟨15713604610011007332514411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20951472813348009776685881 15713604610011007332514411)
        ·
          refine ⟨23570406915016510998771617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15713604610011007332514411 23570406915016510998771617)
          ·
            refine ⟨17677805186262383249078713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23570406915016510998771617 17677805186262383249078713)
            ·
              refine ⟨13258353889696787436809035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17677805186262383249078713 13258353889696787436809035)
              ·
                refine ⟨19887530834545181155213553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13258353889696787436809035 19887530834545181155213553)
                ·
                  refine ⟨14915648125908885866410165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19887530834545181155213553 14915648125908885866410165)
                  ·
                    refine ⟨1398342011803958049975953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14915648125908885866410165 1398342011803958049975953)
                    ·
                      rfl

theorem cell22_4084892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_4084892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084892 prefixEnd_4084892 := by exact prefixLift 4084892
  have htrace : WordTrace (prefixWord ++ tailWord_4084892) baseStart_4084892 baseEnd_4084892 := by
    simpa [prefixWord, tailWord_4084892, baseEnd_4084892] using wordTrace_append hprefix tailTrace_4084892
  have hstable : (prefixWord ++ tailWord_4084892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084892).length < 2 ^ (prefixWord ++ tailWord_4084892).sum := by decide
  have hdescent : baseEnd_4084892 < baseStart_4084892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084924 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_4084924 : Nat := 118140960795 + 4084924 * 2 ^ 59
def prefixEnd_4084924 : Nat := 4983230072969 + 3 ^ 40 * 4084924 * 2
def baseEnd_4084924 : Nat := 1398352966057920633175855

theorem tailTrace_4084924 : CollatzResearch.WordTrace tailWord_4084924 prefixEnd_4084924 1398352966057920633175855 := by
  unfold tailWord_4084924
  simp only [CollatzResearch.WordTrace]
  refine ⟨74494709126512736160798913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99326278835350314881065217 74494709126512736160798913)
  ·
    refine ⟨55871031844884552120599185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74494709126512736160798913 55871031844884552120599185)
    ·
      refine ⟨41903273883663414090449389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55871031844884552120599185 41903273883663414090449389)
      ·
        refine ⟨15713727706373780283918521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41903273883663414090449389 15713727706373780283918521)
        ·
          refine ⟨11785295779780335212938891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15713727706373780283918521 11785295779780335212938891)
          ·
            refine ⟨17677943669670502819408337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11785295779780335212938891 17677943669670502819408337)
            ·
              refine ⟨13258457752252877114556253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17677943669670502819408337 13258457752252877114556253)
              ·
                refine ⟨4971921657094828917958595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13258457752252877114556253 4971921657094828917958595)
                ·
                  refine ⟨7457882485642243376937893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4971921657094828917958595 7457882485642243376937893)
                  ·
                    refine ⟨1398352966057920633175855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7457882485642243376937893 1398352966057920633175855)
                    ·
                      rfl

theorem cell22_4084924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_4084924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4084924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4084924 prefixEnd_4084924 := by exact prefixLift 4084924
  have htrace : WordTrace (prefixWord ++ tailWord_4084924) baseStart_4084924 baseEnd_4084924 := by
    simpa [prefixWord, tailWord_4084924, baseEnd_4084924] using wordTrace_append hprefix tailTrace_4084924
  have hstable : (prefixWord ++ tailWord_4084924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084924).length < 2 ^ (prefixWord ++ tailWord_4084924).sum := by decide
  have hdescent : baseEnd_4084924 < baseStart_4084924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085044 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4085044 : Nat := 118140960795 + 4085044 * 2 ^ 59
def prefixEnd_4085044 : Nat := 4983230072969 + 3 ^ 40 * 4085044 * 2
def baseEnd_4085044 : Nat := 1398394044510280320175487

theorem tailTrace_4085044 : CollatzResearch.WordTrace tailWord_4085044 prefixEnd_4085044 1398394044510280320175487 := by
  unfold tailWord_4085044
  simp only [CollatzResearch.WordTrace]
  refine ⟨74496897506295366407983093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99329196675060488543977457 74496897506295366407983093)
  ·
    refine ⟨6984084141215190600748415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74496897506295366407983093 6984084141215190600748415)
    ·
      refine ⟨10476126211822785901122623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6984084141215190600748415 10476126211822785901122623)
      ·
        refine ⟨15714189317734178851683935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10476126211822785901122623 15714189317734178851683935)
        ·
          refine ⟨23571283976601268277525903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15714189317734178851683935 23571283976601268277525903)
          ·
            refine ⟨35356925964901902416288855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23571283976601268277525903 35356925964901902416288855)
            ·
              refine ⟨53035388947352853624433283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35356925964901902416288855 53035388947352853624433283)
              ·
                refine ⟨79553083421029280436649925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53035388947352853624433283 79553083421029280436649925)
                ·
                  refine ⟨14916203141442990081871861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79553083421029280436649925 14916203141442990081871861)
                  ·
                    refine ⟨1398394044510280320175487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14916203141442990081871861 1398394044510280320175487)
                    ·
                      rfl

theorem cell22_4085044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4085044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085044 prefixEnd_4085044 := by exact prefixLift 4085044
  have htrace : WordTrace (prefixWord ++ tailWord_4085044) baseStart_4085044 baseEnd_4085044 := by
    simpa [prefixWord, tailWord_4085044, baseEnd_4085044] using wordTrace_append hprefix tailTrace_4085044
  have hstable : (prefixWord ++ tailWord_4085044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085044).length < 2 ^ (prefixWord ++ tailWord_4085044).sum := by decide
  have hdescent : baseEnd_4085044 < baseStart_4085044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085076 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_4085076 : Nat := 118140960795 + 4085076 * 2 ^ 59
def prefixEnd_4085076 : Nat := 4983230072969 + 3 ^ 40 * 4085076 * 2
def baseEnd_4085076 : Nat := 1398404998764242903375389

theorem tailTrace_4085076 : CollatzResearch.WordTrace tailWord_4085076 prefixEnd_4085076 1398404998764242903375389 := by
  unfold tailWord_4085076
  simp only [CollatzResearch.WordTrace]
  refine ⟨74497481074237401140565541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99329974765649868187420721 74497481074237401140565541)
  ·
    refine ⟨13968277701419512713856039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74497481074237401140565541 13968277701419512713856039)
    ·
      refine ⟨20952416552129269070784059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13968277701419512713856039 20952416552129269070784059)
      ·
        refine ⟨31428624828193903606176089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20952416552129269070784059 31428624828193903606176089)
        ·
          refine ⟨23571468621145427704632067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31428624828193903606176089 23571468621145427704632067)
          ·
            refine ⟨35357202931718141556948101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23571468621145427704632067 35357202931718141556948101)
            ·
              refine ⟨6629475549697151541927769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35357202931718141556948101 6629475549697151541927769)
              ·
                refine ⟨4972106662272863656445827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6629475549697151541927769 4972106662272863656445827)
                ·
                  refine ⟨7458159993409295484668741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972106662272863656445827 7458159993409295484668741)
                  ·
                    refine ⟨1398404998764242903375389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7458159993409295484668741 1398404998764242903375389)
                    ·
                      rfl

theorem cell22_4085076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_4085076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085076 prefixEnd_4085076 := by exact prefixLift 4085076
  have htrace : WordTrace (prefixWord ++ tailWord_4085076) baseStart_4085076 baseEnd_4085076 := by
    simpa [prefixWord, tailWord_4085076, baseEnd_4085076] using wordTrace_append hprefix tailTrace_4085076
  have hstable : (prefixWord ++ tailWord_4085076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085076).length < 2 ^ (prefixWord ++ tailWord_4085076).sum := by decide
  have hdescent : baseEnd_4085076 < baseStart_4085076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085091 : List Nat := [1, 1, 1, 5, 2, 2, 3, 3, 4]
def baseStart_4085091 : Nat := 118140960795 + 4085091 * 2 ^ 59
def prefixEnd_4085091 : Nat := 4983230072969 + 3 ^ 40 * 4085091 * 2
def baseEnd_4085091 : Nat := 466136711190262621416781

theorem tailTrace_4085091 : CollatzResearch.WordTrace tailWord_4085091 prefixEnd_4085091 466136711190262621416781 := by
  unfold tailWord_4085091
  simp only [CollatzResearch.WordTrace]
  refine ⟨148995509243420459842927127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99330339495613639895284751 148995509243420459842927127)
  ·
    refine ⟨223493263865130689764390691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148995509243420459842927127 223493263865130689764390691)
    ·
      refine ⟨335239895797696034646586037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223493263865130689764390691 335239895797696034646586037)
      ·
        refine ⟨31428740231034003248117441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335239895797696034646586037 31428740231034003248117441)
        ·
          refine ⟨23571555173275502436088081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31428740231034003248117441 23571555173275502436088081)
          ·
            refine ⟨17678666379956626827066061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23571555173275502436088081 17678666379956626827066061)
            ·
              refine ⟨6629499892483735060149773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17678666379956626827066061 6629499892483735060149773)
              ·
                refine ⟨2486062459681400647556165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6629499892483735060149773 2486062459681400647556165)
                ·
                  refine ⟨466136711190262621416781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486062459681400647556165 466136711190262621416781)
                  ·
                    rfl

theorem cell22_4085091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 4].length) (baseStart_4085091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085091 prefixEnd_4085091 := by exact prefixLift 4085091
  have htrace : WordTrace (prefixWord ++ tailWord_4085091) baseStart_4085091 baseEnd_4085091 := by
    simpa [prefixWord, tailWord_4085091, baseEnd_4085091] using wordTrace_append hprefix tailTrace_4085091
  have hstable : (prefixWord ++ tailWord_4085091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085091).length < 2 ^ (prefixWord ++ tailWord_4085091).sum := by decide
  have hdescent : baseEnd_4085091 < baseStart_4085091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085104 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 2, 4]
def baseStart_4085104 : Nat := 118140960795 + 4085104 * 2 ^ 59
def prefixEnd_4085104 : Nat := 4983230072969 + 3 ^ 40 * 4085104 * 2
def baseEnd_4085104 : Nat := 1398414583736460163675303

theorem tailTrace_4085104 : CollatzResearch.WordTrace tailWord_4085104 prefixEnd_4085104 1398414583736460163675303 := by
  unfold tailWord_4085104
  simp only [CollatzResearch.WordTrace]
  refine ⟨74497991696186681531575183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99330655594915575375433577 74497991696186681531575183)
  ·
    refine ⟨111746987544280022297362775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74497991696186681531575183 111746987544280022297362775)
    ·
      refine ⟨167620481316420033446044163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111746987544280022297362775 167620481316420033446044163)
      ·
        refine ⟨251430721974630050169066245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167620481316420033446044163 251430721974630050169066245)
        ·
          refine ⟨47143260370243134406699921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251430721974630050169066245 47143260370243134406699921)
          ·
            refine ⟨35357445277682350805024941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47143260370243134406699921 35357445277682350805024941)
            ·
              refine ⟨13259041979130881551884353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35357445277682350805024941 13259041979130881551884353)
              ·
                refine ⟨9944281484348161163913265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13259041979130881551884353 9944281484348161163913265)
                ·
                  refine ⟨7458211113261120872934949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9944281484348161163913265 7458211113261120872934949)
                  ·
                    refine ⟨1398414583736460163675303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7458211113261120872934949 1398414583736460163675303)
                    ·
                      rfl

theorem cell22_4085104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_4085104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085104 prefixEnd_4085104 := by exact prefixLift 4085104
  have htrace : WordTrace (prefixWord ++ tailWord_4085104) baseStart_4085104 baseEnd_4085104 := by
    simpa [prefixWord, tailWord_4085104, baseEnd_4085104] using wordTrace_append hprefix tailTrace_4085104
  have hstable : (prefixWord ++ tailWord_4085104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085104).length < 2 ^ (prefixWord ++ tailWord_4085104).sum := by decide
  have hdescent : baseEnd_4085104 < baseStart_4085104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085106 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_4085106 : Nat := 118140960795 + 4085106 * 2 ^ 59
def prefixEnd_4085106 : Nat := 4983230072969 + 3 ^ 40 * 4085106 * 2
def baseEnd_4085106 : Nat := 1398415268377332825125297

theorem tailTrace_4085106 : CollatzResearch.WordTrace tailWord_4085106 prefixEnd_4085106 1398415268377332825125297 := by
  unfold tailWord_4085106
  simp only [CollatzResearch.WordTrace]
  refine ⟨37249014084591529351180793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99330704225577411603148781 37249014084591529351180793)
  ·
    refine ⟨27936760563443647013385595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37249014084591529351180793 27936760563443647013385595)
    ·
      refine ⟨41905140845165470520078393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27936760563443647013385595 41905140845165470520078393)
      ·
        refine ⟨31428855633874102890058795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41905140845165470520078393 31428855633874102890058795)
        ·
          refine ⟨47143283450811154335088193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31428855633874102890058795 47143283450811154335088193)
          ·
            refine ⟨35357462588108365751316145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47143283450811154335088193 35357462588108365751316145)
            ·
              refine ⟨26518096941081274313487109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35357462588108365751316145 26518096941081274313487109)
              ·
                refine ⟨4972143176452738933778833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26518096941081274313487109 4972143176452738933778833)
                ·
                  refine ⟨3729107382339554200334125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4972143176452738933778833 3729107382339554200334125)
                  ·
                    refine ⟨1398415268377332825125297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3729107382339554200334125 1398415268377332825125297)
                    ·
                      rfl

theorem cell22_4085106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_4085106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085106 prefixEnd_4085106 := by exact prefixLift 4085106
  have htrace : WordTrace (prefixWord ++ tailWord_4085106) baseStart_4085106 baseEnd_4085106 := by
    simpa [prefixWord, tailWord_4085106, baseEnd_4085106] using wordTrace_append hprefix tailTrace_4085106
  have hstable : (prefixWord ++ tailWord_4085106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085106).length < 2 ^ (prefixWord ++ tailWord_4085106).sum := by decide
  have hdescent : baseEnd_4085106 < baseStart_4085106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085123 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 2, 3]
def baseStart_4085123 : Nat := 118140960795 + 4085123 * 2 ^ 59
def prefixEnd_4085123 : Nat := 4983230072969 + 3 ^ 40 * 4085123 * 2
def baseEnd_4085123 : Nat := 1398421087824750447450245

theorem tailTrace_4085123 : CollatzResearch.WordTrace tailWord_4085123 prefixEnd_4085123 1398421087824750447450245 := by
  unfold tailWord_4085123
  simp only [CollatzResearch.WordTrace]
  refine ⟨148996676379304529308092023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99331117586203019538728015 148996676379304529308092023)
  ·
    refine ⟨223495014568956793962138035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148996676379304529308092023 223495014568956793962138035)
    ·
      refine ⟨335242521853435190943207053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223495014568956793962138035 335242521853435190943207053)
      ·
        refine ⟨125715945695038196603702645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335242521853435190943207053 125715945695038196603702645)
        ·
          refine ⟨11785869908909830931597123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125715945695038196603702645 11785869908909830931597123)
          ·
            refine ⟨17678804863364746397395685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11785869908909830931597123 17678804863364746397395685)
            ·
              refine ⟨3314775911880889949511691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17678804863364746397395685 3314775911880889949511691)
              ·
                refine ⟨4972163867821334924267537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314775911880889949511691 4972163867821334924267537)
                ·
                  refine ⟨3729122900866001193200653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4972163867821334924267537 3729122900866001193200653)
                  ·
                    refine ⟨1398421087824750447450245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3729122900866001193200653 1398421087824750447450245)
                    ·
                      rfl

theorem cell22_4085123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 2, 3].length) (baseStart_4085123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085123 prefixEnd_4085123 := by exact prefixLift 4085123
  have htrace : WordTrace (prefixWord ++ tailWord_4085123) baseStart_4085123 baseEnd_4085123 := by
    simpa [prefixWord, tailWord_4085123, baseEnd_4085123] using wordTrace_append hprefix tailTrace_4085123
  have hstable : (prefixWord ++ tailWord_4085123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085123).length < 2 ^ (prefixWord ++ tailWord_4085123).sum := by decide
  have hdescent : baseEnd_4085123 < baseStart_4085123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085164 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 5]
def baseStart_4085164 : Nat := 118140960795 + 4085164 * 2 ^ 59
def prefixEnd_4085164 : Nat := 4983230072969 + 3 ^ 40 * 4085164 * 2
def baseEnd_4085164 : Nat := 466145040987546669058373

theorem tailTrace_4085164 : CollatzResearch.WordTrace tailWord_4085164 prefixEnd_4085164 466145040987546669058373 := by
  unfold tailWord_4085164
  simp only [CollatzResearch.WordTrace]
  refine ⟨74499085886077996655167273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99332114514770662206889697 74499085886077996655167273)
  ·
    refine ⟨55874314414558497491375455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74499085886077996655167273 55874314414558497491375455)
    ·
      refine ⟨83811471621837746237063183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55874314414558497491375455 83811471621837746237063183)
      ·
        refine ⟨125717207432756619355594775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83811471621837746237063183 125717207432756619355594775)
        ·
          refine ⟨188575811149134929033392163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125717207432756619355594775 188575811149134929033392163)
          ·
            refine ⟨282863716723702393550088245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188575811149134929033392163 282863716723702393550088245)
            ·
              refine ⟨26518473442847099395320773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 282863716723702393550088245 26518473442847099395320773)
              ·
                refine ⟨4972213770533831136622645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26518473442847099395320773 4972213770533831136622645)
                ·
                  refine ⟨466145040987546669058373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4972213770533831136622645 466145040987546669058373)
                  ·
                    rfl

theorem cell22_4085164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_4085164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085164 prefixEnd_4085164 := by exact prefixLift 4085164
  have htrace : WordTrace (prefixWord ++ tailWord_4085164) baseStart_4085164 baseEnd_4085164 := by
    simpa [prefixWord, tailWord_4085164, baseEnd_4085164] using wordTrace_append hprefix tailTrace_4085164
  have hstable : (prefixWord ++ tailWord_4085164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085164).length < 2 ^ (prefixWord ++ tailWord_4085164).sum := by decide
  have hdescent : baseEnd_4085164 < baseStart_4085164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085239 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 6, 4]
def baseStart_4085239 : Nat := 118140960795 + 4085239 * 2 ^ 59
def prefixEnd_4085239 : Nat := 4983230072969 + 3 ^ 40 * 4085239 * 2
def baseEnd_4085239 : Nat := 1398460796995364811549889

theorem tailTrace_4085239 : CollatzResearch.WordTrace tailWord_4085239 prefixEnd_4085239 1398460796995364811549889 := by
  unfold tailWord_4085239
  simp only [CollatzResearch.WordTrace]
  refine ⟨149000907246884281119314771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99333938164589520746209847 149000907246884281119314771)
  ·
    refine ⟨223501360870326421678972157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149000907246884281119314771 223501360870326421678972157)
    ·
      refine ⟨83813010326372408129614559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223501360870326421678972157 83813010326372408129614559)
      ·
        refine ⟨125719515489558612194421839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83813010326372408129614559 125719515489558612194421839)
        ·
          refine ⟨188579273234337918291632759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125719515489558612194421839 188579273234337918291632759)
          ·
            refine ⟨282868909851506877437449139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188579273234337918291632759 282868909851506877437449139)
            ·
              refine ⟨424303364777260316156173709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282868909851506877437449139 424303364777260316156173709)
              ·
                refine ⟨159113761791472618558565141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424303364777260316156173709 159113761791472618558565141)
                ·
                  refine ⟨7458457583975278994932741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159113761791472618558565141 7458457583975278994932741)
                  ·
                    refine ⟨1398460796995364811549889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7458457583975278994932741 1398460796995364811549889)
                    ·
                      rfl

theorem cell22_4085239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_4085239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085239 prefixEnd_4085239 := by exact prefixLift 4085239
  have htrace : WordTrace (prefixWord ++ tailWord_4085239) baseStart_4085239 baseEnd_4085239 := by
    simpa [prefixWord, tailWord_4085239, baseEnd_4085239] using wordTrace_append hprefix tailTrace_4085239
  have hstable : (prefixWord ++ tailWord_4085239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085239).length < 2 ^ (prefixWord ++ tailWord_4085239).sum := by decide
  have hdescent : baseEnd_4085239 < baseStart_4085239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085260 : List Nat := [2, 2, 1, 2, 5, 2, 1, 3, 4]
def baseStart_4085260 : Nat := 118140960795 + 4085260 * 2 ^ 59
def prefixEnd_4085260 : Nat := 4983230072969 + 3 ^ 40 * 4085260 * 2
def baseEnd_4085260 : Nat := 466155995241509252258275

theorem tailTrace_4085260 : CollatzResearch.WordTrace tailWord_4085260 prefixEnd_4085260 466155995241509252258275 := by
  unfold tailWord_4085260
  simp only [CollatzResearch.WordTrace]
  refine ⟨74500836589904100852914617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99334448786538801137219489 74500836589904100852914617)
  ·
    refine ⟨55875627442428075639685963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74500836589904100852914617 55875627442428075639685963)
    ·
      refine ⟨83813441163642113459528945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55875627442428075639685963 83813441163642113459528945)
      ·
        refine ⟨62860080872731585094646709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83813441163642113459528945 62860080872731585094646709)
        ·
          refine ⟨5893132581818586102623129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62860080872731585094646709 5893132581818586102623129)
          ·
            refine ⟨4419849436363939576967347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5893132581818586102623129 4419849436363939576967347)
            ·
              refine ⟨6629774154545909365451021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419849436363939576967347 6629774154545909365451021)
              ·
                refine ⟨2486165307954716012044133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6629774154545909365451021 2486165307954716012044133)
                ·
                  refine ⟨466155995241509252258275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486165307954716012044133 466155995241509252258275)
                  ·
                    rfl

theorem cell22_4085260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_4085260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085260 prefixEnd_4085260 := by exact prefixLift 4085260
  have htrace : WordTrace (prefixWord ++ tailWord_4085260) baseStart_4085260 baseEnd_4085260 := by
    simpa [prefixWord, tailWord_4085260, baseEnd_4085260] using wordTrace_append hprefix tailTrace_4085260
  have hstable : (prefixWord ++ tailWord_4085260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085260).length < 2 ^ (prefixWord ++ tailWord_4085260).sum := by decide
  have hdescent : baseEnd_4085260 < baseStart_4085260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085288 : List Nat := [2, 1, 5, 2, 2, 1, 2, 7]
def baseStart_4085288 : Nat := 118140960795 + 4085288 * 2 ^ 59
def prefixEnd_4085288 : Nat := 4983230072969 + 3 ^ 40 * 4085288 * 2
def baseEnd_4085288 : Nat := 155386396744082779674971

theorem tailTrace_4085288 : CollatzResearch.WordTrace tailWord_4085288 prefixEnd_4085288 155386396744082779674971 := by
  unfold tailWord_4085288
  simp only [CollatzResearch.WordTrace]
  refine ⟨74501347211853381243924259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99335129615804508325232345 74501347211853381243924259)
  ·
    refine ⟨111752020817780071865886389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74501347211853381243924259 111752020817780071865886389)
    ·
      refine ⟨10476751951666881737426849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111752020817780071865886389 10476751951666881737426849)
      ·
        refine ⟨7857563963750161303070137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10476751951666881737426849 7857563963750161303070137)
        ·
          refine ⟨5893172972812620977302603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7857563963750161303070137 5893172972812620977302603)
          ·
            refine ⟨8839759459218931465953905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893172972812620977302603 8839759459218931465953905)
            ·
              refine ⟨6629819594414198599465429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8839759459218931465953905 6629819594414198599465429)
              ·
                refine ⟨155386396744082779674971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6629819594414198599465429 155386396744082779674971)
                ·
                  rfl

theorem cell22_4085288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 7].length) (baseStart_4085288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085288 prefixEnd_4085288 := by exact prefixLift 4085288
  have htrace : WordTrace (prefixWord ++ tailWord_4085288) baseStart_4085288 baseEnd_4085288 := by
    simpa [prefixWord, tailWord_4085288, baseEnd_4085288] using wordTrace_append hprefix tailTrace_4085288
  have hstable : (prefixWord ++ tailWord_4085288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085288).length < 2 ^ (prefixWord ++ tailWord_4085288).sum := by decide
  have hdescent : baseEnd_4085288 < baseStart_4085288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085376 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 1, 5]
def baseStart_4085376 : Nat := 118140960795 + 4085376 * 2 ^ 59
def prefixEnd_4085376 : Nat := 4983230072969 + 3 ^ 40 * 4085376 * 2
def baseEnd_4085376 : Nat := 1398507694895142120874469

theorem tailTrace_4085376 : CollatzResearch.WordTrace tailWord_4085376 prefixEnd_4085376 1398507694895142120874469 := by
  unfold tailWord_4085376
  simp only [CollatzResearch.WordTrace]
  refine ⟨74502952023693976758525991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99337269364925302344701321 74502952023693976758525991)
  ·
    refine ⟨111754428035540965137788987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74502952023693976758525991 111754428035540965137788987)
    ·
      refine ⟨167631642053311447706683481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111754428035540965137788987 167631642053311447706683481)
      ·
        refine ⟨125723731539983585780012611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167631642053311447706683481 125723731539983585780012611)
        ·
          refine ⟨188585597309975378670018917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125723731539983585780012611 188585597309975378670018917)
          ·
            refine ⟨35359799495620383500628547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188585597309975378670018917 35359799495620383500628547)
            ·
              refine ⟨53039699243430575250942821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35359799495620383500628547 53039699243430575250942821)
              ·
                refine ⟨9944943608143232859551779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53039699243430575250942821 9944943608143232859551779)
                ·
                  refine ⟨14917415412214849289327669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9944943608143232859551779 14917415412214849289327669)
                  ·
                    refine ⟨1398507694895142120874469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14917415412214849289327669 1398507694895142120874469)
                    ·
                      rfl

theorem cell22_4085376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_4085376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085376 prefixEnd_4085376 := by exact prefixLift 4085376
  have htrace : WordTrace (prefixWord ++ tailWord_4085376) baseStart_4085376 baseEnd_4085376 := by
    simpa [prefixWord, tailWord_4085376, baseEnd_4085376] using wordTrace_append hprefix tailTrace_4085376
  have hstable : (prefixWord ++ tailWord_4085376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085376).length < 2 ^ (prefixWord ++ tailWord_4085376).sum := by decide
  have hdescent : baseEnd_4085376 < baseStart_4085376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085380 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_4085380 : Nat := 118140960795 + 4085380 * 2 ^ 59
def prefixEnd_4085380 : Nat := 4983230072969 + 3 ^ 40 * 4085380 * 2
def baseEnd_4085380 : Nat := 1398509064176887443774457

theorem tailTrace_4085380 : CollatzResearch.WordTrace tailWord_4085380 prefixEnd_4085380 1398509064176887443774457 := by
  unfold tailWord_4085380
  simp only [CollatzResearch.WordTrace]
  refine ⟨74503024969686731100098797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99337366626248974800131729 74503024969686731100098797)
  ·
    refine ⟨27938634363632524162537049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74503024969686731100098797 27938634363632524162537049)
    ·
      refine ⟨20953975772724393121902787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27938634363632524162537049 20953975772724393121902787)
      ·
        refine ⟨31430963659086589682854181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20953975772724393121902787 31430963659086589682854181)
        ·
          refine ⟨5893305686078735565535159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31430963659086589682854181 5893305686078735565535159)
          ·
            refine ⟨8839958529118103348302739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893305686078735565535159 8839958529118103348302739)
            ·
              refine ⟨13259937793677155022454109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839958529118103348302739 13259937793677155022454109)
              ·
                refine ⟨4972476672628933133420291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13259937793677155022454109 4972476672628933133420291)
                ·
                  refine ⟨7458715008943399700130437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972476672628933133420291 7458715008943399700130437)
                  ·
                    refine ⟨1398509064176887443774457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7458715008943399700130437 1398509064176887443774457)
                    ·
                      rfl

theorem cell22_4085380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_4085380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085380 prefixEnd_4085380 := by exact prefixLift 4085380
  have htrace : WordTrace (prefixWord ++ tailWord_4085380) baseStart_4085380 baseEnd_4085380 := by
    simpa [prefixWord, tailWord_4085380, baseEnd_4085380] using wordTrace_append hprefix tailTrace_4085380
  have hstable : (prefixWord ++ tailWord_4085380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085380).length < 2 ^ (prefixWord ++ tailWord_4085380).sum := by decide
  have hdescent : baseEnd_4085380 < baseStart_4085380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085393 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 2, 3]
def baseStart_4085393 : Nat := 118140960795 + 4085393 * 2 ^ 59
def prefixEnd_4085393 : Nat := 4983230072969 + 3 ^ 40 * 4085393 * 2
def baseEnd_4085393 : Nat := 1398513514342559743199417

theorem tailTrace_4085393 : CollatzResearch.WordTrace tailWord_4085393 prefixEnd_4085393 1398513514342559743199417 := by
  unfold tailWord_4085393
  simp only [CollatzResearch.WordTrace]
  refine ⟨149006524088326365420420833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99337682725550910280280555 149006524088326365420420833)
  ·
    refine ⟨111754893066244774065315625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149006524088326365420420833 111754893066244774065315625)
    ·
      refine ⟨83816169799683580548986719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111754893066244774065315625 83816169799683580548986719)
      ·
        refine ⟨125724254699525370823480079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83816169799683580548986719 125724254699525370823480079)
        ·
          refine ⟨188586382049288056235220119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125724254699525370823480079 188586382049288056235220119)
          ·
            refine ⟨282879573073932084352830179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188586382049288056235220119 282879573073932084352830179)
            ·
              refine ⟨424319359610898126529245269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282879573073932084352830179 424319359610898126529245269)
              ·
                refine ⟨4972492495440212420264593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 424319359610898126529245269 4972492495440212420264593)
                ·
                  refine ⟨3729369371580159315198445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4972492495440212420264593 3729369371580159315198445)
                  ·
                    refine ⟨1398513514342559743199417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3729369371580159315198445 1398513514342559743199417)
                    ·
                      rfl

theorem cell22_4085393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_4085393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085393 prefixEnd_4085393 := by exact prefixLift 4085393
  have htrace : WordTrace (prefixWord ++ tailWord_4085393) baseStart_4085393 baseEnd_4085393 := by
    simpa [prefixWord, tailWord_4085393, baseEnd_4085393] using wordTrace_append hprefix tailTrace_4085393
  have hstable : (prefixWord ++ tailWord_4085393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085393).length < 2 ^ (prefixWord ++ tailWord_4085393).sum := by decide
  have hdescent : baseEnd_4085393 < baseStart_4085393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085429 : List Nat := [1, 3, 3, 3, 3, 1, 1, 3, 4]
def baseStart_4085429 : Nat := 118140960795 + 4085429 * 2 ^ 59
def prefixEnd_4085429 : Nat := 4983230072969 + 3 ^ 40 * 4085429 * 2
def baseEnd_4085429 : Nat := 466175279292755883099769

theorem tailTrace_4085429 : CollatzResearch.WordTrace tailWord_4085429 prefixEnd_4085429 466175279292755883099769 := by
  unfold tailWord_4085429
  simp only [CollatzResearch.WordTrace]
  refine ⟨149007837116195943568731341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99338558077463962379154227 149007837116195943568731341)
  ·
    refine ⟨55877938918573478838274253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149007837116195943568731341 55877938918573478838274253)
    ·
      refine ⟨20954227094465054564352845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55877938918573478838274253 20954227094465054564352845)
      ·
        refine ⟨7857835160424395461632317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20954227094465054564352845 7857835160424395461632317)
        ·
          refine ⟨2946688185159148298112119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7857835160424395461632317 2946688185159148298112119)
          ·
            refine ⟨4420032277738722447168179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946688185159148298112119 4420032277738722447168179)
            ·
              refine ⟨6630048416608083670752269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420032277738722447168179 6630048416608083670752269)
              ·
                refine ⟨2486268156228031376532101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6630048416608083670752269 2486268156228031376532101)
                ·
                  refine ⟨466175279292755883099769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486268156228031376532101 466175279292755883099769)
                  ·
                    rfl

theorem cell22_4085429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_4085429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085429 prefixEnd_4085429 := by exact prefixLift 4085429
  have htrace : WordTrace (prefixWord ++ tailWord_4085429) baseStart_4085429 baseEnd_4085429 := by
    simpa [prefixWord, tailWord_4085429, baseEnd_4085429] using wordTrace_append hprefix tailTrace_4085429
  have hstable : (prefixWord ++ tailWord_4085429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085429).length < 2 ^ (prefixWord ++ tailWord_4085429).sum := by decide
  have hdescent : baseEnd_4085429 < baseStart_4085429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085446 : List Nat := [6, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_4085446 : Nat := 118140960795 + 4085446 * 2 ^ 59
def prefixEnd_4085446 : Nat := 4983230072969 + 3 ^ 40 * 4085446 * 2
def baseEnd_4085446 : Nat := 466177219108561757208085

theorem tailTrace_4085446 : CollatzResearch.WordTrace tailWord_4085446 prefixEnd_4085446 466177219108561757208085 := by
  unfold tailWord_4085446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656514286160448608503131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99338971438089570314733461 4656514286160448608503131)
  ·
    refine ⟨6984771429240672912754697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4656514286160448608503131 6984771429240672912754697)
    ·
      refine ⟨5238578571930504684566023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6984771429240672912754697 5238578571930504684566023)
      ·
        refine ⟨7857867857895757026849035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5238578571930504684566023 7857867857895757026849035)
        ·
          refine ⟨11786801786843635540273553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7857867857895757026849035 11786801786843635540273553)
          ·
            refine ⟨8840101340132726655205165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11786801786843635540273553 8840101340132726655205165)
            ·
              refine ⟨3315038002549772495701937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8840101340132726655205165 3315038002549772495701937)
              ·
                refine ⟨2486278501912329371776453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3315038002549772495701937 2486278501912329371776453)
                ·
                  refine ⟨466177219108561757208085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486278501912329371776453 466177219108561757208085)
                  ·
                    rfl

theorem cell22_4085446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_4085446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085446 prefixEnd_4085446 := by exact prefixLift 4085446
  have htrace : WordTrace (prefixWord ++ tailWord_4085446) baseStart_4085446 baseEnd_4085446 := by
    simpa [prefixWord, tailWord_4085446, baseEnd_4085446] using wordTrace_append hprefix tailTrace_4085446
  have hstable : (prefixWord ++ tailWord_4085446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085446).length < 2 ^ (prefixWord ++ tailWord_4085446).sum := by decide
  have hdescent : baseEnd_4085446 < baseStart_4085446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085455 : List Nat := [1, 1, 2, 1, 1, 3, 1, 8, 1, 3]
def baseStart_4085455 : Nat := 118140960795 + 4085455 * 2 ^ 59
def prefixEnd_4085455 : Nat := 4983230072969 + 3 ^ 40 * 4085455 * 2
def baseEnd_4085455 : Nat := 1398534738209612248149227

theorem tailTrace_4085455 : CollatzResearch.WordTrace tailWord_4085455 prefixEnd_4085455 1398534738209612248149227 := by
  unfold tailWord_4085455
  simp only [CollatzResearch.WordTrace]
  refine ⟨149008785414101750009177819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99339190276067833339451879 149008785414101750009177819)
  ·
    refine ⟨223513178121152625013766729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149008785414101750009177819 223513178121152625013766729)
    ·
      refine ⟨167634883590864468760325047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223513178121152625013766729 167634883590864468760325047)
      ·
        refine ⟨251452325386296703140487571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167634883590864468760325047 251452325386296703140487571)
        ·
          refine ⟨377178488079445054710731357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251452325386296703140487571 377178488079445054710731357)
          ·
            refine ⟨141441933029791895516524259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377178488079445054710731357 141441933029791895516524259)
            ·
              refine ⟨212162899544687843274786389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141441933029791895516524259 212162899544687843274786389)
              ·
                refine ⟨2486283979039310663376403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 212162899544687843274786389 2486283979039310663376403)
                ·
                  refine ⟨3729425968558965995064605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486283979039310663376403 3729425968558965995064605)
                  ·
                    refine ⟨1398534738209612248149227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3729425968558965995064605 1398534738209612248149227)
                    ·
                      rfl

theorem cell22_4085455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 1, 3].length) (baseStart_4085455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085455 prefixEnd_4085455 := by exact prefixLift 4085455
  have htrace : WordTrace (prefixWord ++ tailWord_4085455) baseStart_4085455 baseEnd_4085455 := by
    simpa [prefixWord, tailWord_4085455, baseEnd_4085455] using wordTrace_append hprefix tailTrace_4085455
  have hstable : (prefixWord ++ tailWord_4085455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085455).length < 2 ^ (prefixWord ++ tailWord_4085455).sum := by decide
  have hdescent : baseEnd_4085455 < baseStart_4085455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085496 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 10]
def baseStart_4085496 : Nat := 118140960795 + 4085496 * 2 ^ 59
def prefixEnd_4085496 : Nat := 4983230072969 + 3 ^ 40 * 4085496 * 2
def baseEnd_4085496 : Nat := 466182924449167269291367

theorem tailTrace_4085496 : CollatzResearch.WordTrace tailWord_4085496 prefixEnd_4085496 466182924449167269291367 := by
  unfold tailWord_4085496
  simp only [CollatzResearch.WordTrace]
  refine ⟨74505140403476607005710171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99340187204635476007613561 74505140403476607005710171)
  ·
    refine ⟨111757710605214910508565257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74505140403476607005710171 111757710605214910508565257)
    ·
      refine ⟨83818282953911182881423943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111757710605214910508565257 83818282953911182881423943)
      ·
        refine ⟨125727424430866774322135915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83818282953911182881423943 125727424430866774322135915)
        ·
          refine ⟨188591136646300161483203873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125727424430866774322135915 188591136646300161483203873)
          ·
            refine ⟨141443352484725121112402905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188591136646300161483203873 141443352484725121112402905)
            ·
              refine ⟨106082514363543840834302179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141443352484725121112402905 106082514363543840834302179)
              ·
                refine ⟨159123771545315761251453269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106082514363543840834302179 159123771545315761251453269)
                ·
                  refine ⟨466182924449167269291367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 159123771545315761251453269 466182924449167269291367)
                  ·
                    rfl

theorem cell22_4085496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_4085496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085496 prefixEnd_4085496 := by exact prefixLift 4085496
  have htrace : WordTrace (prefixWord ++ tailWord_4085496) baseStart_4085496 baseEnd_4085496 := by
    simpa [prefixWord, tailWord_4085496, baseEnd_4085496] using wordTrace_append hprefix tailTrace_4085496
  have hstable : (prefixWord ++ tailWord_4085496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085496).length < 2 ^ (prefixWord ++ tailWord_4085496).sum := by decide
  have hdescent : baseEnd_4085496 < baseStart_4085496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085502 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_4085502 : Nat := 118140960795 + 4085502 * 2 ^ 59
def prefixEnd_4085502 : Nat := 4983230072969 + 3 ^ 40 * 4085502 * 2
def baseEnd_4085502 : Nat := 466183609090039930741361

theorem tailTrace_4085502 : CollatzResearch.WordTrace tailWord_4085502 prefixEnd_4085502 466183609090039930741361 := by
  unfold tailWord_4085502
  simp only [CollatzResearch.WordTrace]
  refine ⟨18626312455616434629517345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99340333096620984690759173 18626312455616434629517345)
  ·
    refine ⟨13969734341712325972138009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18626312455616434629517345 13969734341712325972138009)
    ·
      refine ⟨10477300756284244479103507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13969734341712325972138009 10477300756284244479103507)
      ·
        refine ⟨15715951134426366718655261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10477300756284244479103507 15715951134426366718655261)
        ·
          refine ⟨5893481675409887519495723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15715951134426366718655261 5893481675409887519495723)
          ·
            refine ⟨8840222513114831279243585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893481675409887519495723 8840222513114831279243585)
            ·
              refine ⟨6630166884836123459432689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8840222513114831279243585 6630166884836123459432689)
              ·
                refine ⟨4972625163627092594574517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6630166884836123459432689 4972625163627092594574517)
                ·
                  refine ⟨466183609090039930741361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4972625163627092594574517 466183609090039930741361)
                  ·
                    rfl

theorem cell22_4085502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_4085502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085502 prefixEnd_4085502 := by exact prefixLift 4085502
  have htrace : WordTrace (prefixWord ++ tailWord_4085502) baseStart_4085502 baseEnd_4085502 := by
    simpa [prefixWord, tailWord_4085502, baseEnd_4085502] using wordTrace_append hprefix tailTrace_4085502
  have hstable : (prefixWord ++ tailWord_4085502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085502).length < 2 ^ (prefixWord ++ tailWord_4085502).sum := by decide
  have hdescent : baseEnd_4085502 < baseStart_4085502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085528 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 1, 5]
def baseStart_4085528 : Nat := 118140960795 + 4085528 * 2 ^ 59
def prefixEnd_4085528 : Nat := 4983230072969 + 3 ^ 40 * 4085528 * 2
def baseEnd_4085528 : Nat := 1398559727601464391074003

theorem tailTrace_4085528 : CollatzResearch.WordTrace tailWord_4085528 prefixEnd_4085528 1398559727601464391074003 := by
  unfold tailWord_4085528
  simp only [CollatzResearch.WordTrace]
  refine ⟨74505723971418641738292619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99340965295224855651056825 74505723971418641738292619)
  ·
    refine ⟨111758585957127962607438929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74505723971418641738292619 111758585957127962607438929)
    ·
      refine ⟨83818939467845971955579197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111758585957127962607438929 83818939467845971955579197)
      ·
        refine ⟨31432102300442239483342199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83818939467845971955579197 31432102300442239483342199)
        ·
          refine ⟨47148153450663359225013299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31432102300442239483342199 47148153450663359225013299)
          ·
            refine ⟨70722230175995038837519949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47148153450663359225013299 70722230175995038837519949)
            ·
              refine ⟨26520836315998139564069981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70722230175995038837519949 26520836315998139564069981)
              ·
                refine ⟨9945313618499302336526243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26520836315998139564069981 9945313618499302336526243)
                ·
                  refine ⟨14917970427748953504789365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9945313618499302336526243 14917970427748953504789365)
                  ·
                    refine ⟨1398559727601464391074003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14917970427748953504789365 1398559727601464391074003)
                    ·
                      rfl

theorem cell22_4085528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_4085528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085528 prefixEnd_4085528 := by exact prefixLift 4085528
  have htrace : WordTrace (prefixWord ++ tailWord_4085528) baseStart_4085528 baseEnd_4085528 := by
    simpa [prefixWord, tailWord_4085528, baseEnd_4085528] using wordTrace_append hprefix tailTrace_4085528
  have hstable : (prefixWord ++ tailWord_4085528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085528).length < 2 ^ (prefixWord ++ tailWord_4085528).sum := by decide
  have hdescent : baseEnd_4085528 < baseStart_4085528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085562 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 2, 3]
def baseStart_4085562 : Nat := 118140960795 + 4085562 * 2 ^ 59
def prefixEnd_4085562 : Nat := 4983230072969 + 3 ^ 40 * 4085562 * 2
def baseEnd_4085562 : Nat := 1398571366496299635723899

theorem tailTrace_4085562 : CollatzResearch.WordTrace tailWord_4085562 prefixEnd_4085562 1398571366496299635723899 := by
  unfold tailWord_4085562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37253172006178526820830735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99341792016476071522215293 37253172006178526820830735)
  ·
    refine ⟨55879758009267790231246103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37253172006178526820830735 55879758009267790231246103)
    ·
      refine ⟨83819637013901685346869155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55879758009267790231246103 83819637013901685346869155)
      ·
        refine ⟨125729455520852528020303733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83819637013901685346869155 125729455520852528020303733)
        ·
          refine ⟨11787136455079924501903475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125729455520852528020303733 11787136455079924501903475)
          ·
            refine ⟨17680704682619886752855213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11787136455079924501903475 17680704682619886752855213)
            ·
              refine ⟨6630264255982457532320705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17680704682619886752855213 6630264255982457532320705)
              ·
                refine ⟨4972698191986843149240529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6630264255982457532320705 4972698191986843149240529)
                ·
                  refine ⟨3729523643990132361930397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4972698191986843149240529 3729523643990132361930397)
                  ·
                    refine ⟨1398571366496299635723899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3729523643990132361930397 1398571366496299635723899)
                    ·
                      rfl

theorem cell22_4085562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_4085562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085562 prefixEnd_4085562 := by exact prefixLift 4085562
  have htrace : WordTrace (prefixWord ++ tailWord_4085562) baseStart_4085562 baseEnd_4085562 := by
    simpa [prefixWord, tailWord_4085562, baseEnd_4085562] using wordTrace_append hprefix tailTrace_4085562
  have hstable : (prefixWord ++ tailWord_4085562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085562).length < 2 ^ (prefixWord ++ tailWord_4085562).sum := by decide
  have hdescent : baseEnd_4085562 < baseStart_4085562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085718 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_4085718 : Nat := 118140960795 + 4085718 * 2 ^ 59
def prefixEnd_4085718 : Nat := 4983230072969 + 3 ^ 40 * 4085718 * 2
def baseEnd_4085718 : Nat := 1398624768484367228823421

theorem tailTrace_4085718 : CollatzResearch.WordTrace tailWord_4085718 prefixEnd_4085718 1398624768484367228823421 := by
  unfold tailWord_4085718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9313648613259309120375113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99345585208099297284001205 9313648613259309120375113)
  ·
    refine ⟨6985236459944481840281335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9313648613259309120375113 6985236459944481840281335)
    ·
      refine ⟨10477854689916722760422003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6985236459944481840281335 10477854689916722760422003)
      ·
        refine ⟨15716782034875084140633005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10477854689916722760422003 15716782034875084140633005)
        ·
          refine ⟨5893793263078156552737377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15716782034875084140633005 5893793263078156552737377)
          ·
            refine ⟨4420344947308617414553033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5893793263078156552737377 4420344947308617414553033)
            ·
              refine ⟨3315258710481463060914775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420344947308617414553033 3315258710481463060914775)
              ·
                refine ⟨4972888065722194591372163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315258710481463060914775 4972888065722194591372163)
                ·
                  refine ⟨7459332098583291887058245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972888065722194591372163 7459332098583291887058245)
                  ·
                    refine ⟨1398624768484367228823421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7459332098583291887058245 1398624768484367228823421)
                    ·
                      rfl

theorem cell22_4085718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_4085718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085718 prefixEnd_4085718 := by exact prefixLift 4085718
  have htrace : WordTrace (prefixWord ++ tailWord_4085718) baseStart_4085718 baseEnd_4085718 := by
    simpa [prefixWord, tailWord_4085718, baseEnd_4085718] using wordTrace_append hprefix tailTrace_4085718
  have hstable : (prefixWord ++ tailWord_4085718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085718).length < 2 ^ (prefixWord ++ tailWord_4085718).sum := by decide
  have hdescent : baseEnd_4085718 < baseStart_4085718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085755 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 5]
def baseStart_4085755 : Nat := 118140960795 + 4085755 * 2 ^ 59
def prefixEnd_4085755 : Nat := 4983230072969 + 3 ^ 40 * 4085755 * 2
def baseEnd_4085755 : Nat := 466212478113503821882769

theorem tailTrace_4085755 : CollatzResearch.WordTrace tailWord_4085755 prefixEnd_4085755 466212478113503821882769 := by
  unfold tailWord_4085755
  simp only [CollatzResearch.WordTrace]
  refine ⟨149019727313014901245098719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99346484875343267496732479 149019727313014901245098719)
  ·
    refine ⟨223529590969522351867648079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149019727313014901245098719 223529590969522351867648079)
    ·
      refine ⟨335294386454283527801472119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223529590969522351867648079 335294386454283527801472119)
      ·
        refine ⟨502941579681425291702208179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335294386454283527801472119 502941579681425291702208179)
        ·
          refine ⟨754412369522137937553312269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502941579681425291702208179 754412369522137937553312269)
          ·
            refine ⟨282904638570801726582492101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 754412369522137937553312269 282904638570801726582492101)
            ·
              refine ⟨53044619732025323734217269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282904638570801726582492101 53044619732025323734217269)
              ·
                refine ⟨4972933099877374100082869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53044619732025323734217269 4972933099877374100082869)
                ·
                  refine ⟨466212478113503821882769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4972933099877374100082869 466212478113503821882769)
                  ·
                    rfl

theorem cell22_4085755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 5].length) (baseStart_4085755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085755 prefixEnd_4085755 := by exact prefixLift 4085755
  have htrace : WordTrace (prefixWord ++ tailWord_4085755) baseStart_4085755 baseEnd_4085755 := by
    simpa [prefixWord, tailWord_4085755, baseEnd_4085755] using wordTrace_append hprefix tailTrace_4085755
  have hstable : (prefixWord ++ tailWord_4085755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085755).length < 2 ^ (prefixWord ++ tailWord_4085755).sum := by decide
  have hdescent : baseEnd_4085755 < baseStart_4085755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085785 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 5, 4]
def baseStart_4085785 : Nat := 118140960795 + 4085785 * 2 ^ 59
def prefixEnd_4085785 : Nat := 4983230072969 + 3 ^ 40 * 4085785 * 2
def baseEnd_4085785 : Nat := 1398647703953601387398215

theorem tailTrace_4085785 : CollatzResearch.WordTrace tailWord_4085785 prefixEnd_4085785 1398647703953601387398215 := by
  unfold tailWord_4085785
  simp only [CollatzResearch.WordTrace]
  refine ⟨149020821502906216368690809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99347214335270810912460539 149020821502906216368690809)
  ·
    refine ⟨111765616127179662276518107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149020821502906216368690809 111765616127179662276518107)
    ·
      refine ⟨167648424190769493414777161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111765616127179662276518107 167648424190769493414777161)
      ·
        refine ⟨125736318143077120061082871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167648424190769493414777161 125736318143077120061082871)
        ·
          refine ⟨188604477214615680091624307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125736318143077120061082871 188604477214615680091624307)
          ·
            refine ⟨282906715821923520137436461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188604477214615680091624307 282906715821923520137436461)
            ·
              refine ⟨106090018433221320051538673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282906715821923520137436461 106090018433221320051538673)
              ·
                refine ⟨79567513824915990038654005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106090018433221320051538673 79567513824915990038654005)
                ·
                  refine ⟨7459454421085874066123813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79567513824915990038654005 7459454421085874066123813)
                  ·
                    refine ⟨1398647703953601387398215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7459454421085874066123813 1398647703953601387398215)
                    ·
                      rfl

theorem cell22_4085785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_4085785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085785 prefixEnd_4085785 := by exact prefixLift 4085785
  have htrace : WordTrace (prefixWord ++ tailWord_4085785) baseStart_4085785 baseEnd_4085785 := by
    simpa [prefixWord, tailWord_4085785, baseEnd_4085785] using wordTrace_append hprefix tailTrace_4085785
  have hstable : (prefixWord ++ tailWord_4085785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085785).length < 2 ^ (prefixWord ++ tailWord_4085785).sum := by decide
  have hdescent : baseEnd_4085785 < baseStart_4085785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085793 : List Nat := [1, 2, 3, 2, 4, 1, 3, 2, 1, 3]
def baseStart_4085793 : Nat := 118140960795 + 4085793 * 2 ^ 59
def prefixEnd_4085793 : Nat := 4983230072969 + 3 ^ 40 * 4085793 * 2
def baseEnd_4085793 : Nat := 1398650442517092033198191

theorem tailTrace_4085793 : CollatzResearch.WordTrace tailWord_4085793 prefixEnd_4085793 1398650442517092033198191 := by
  unfold tailWord_4085793
  simp only [CollatzResearch.WordTrace]
  refine ⟨149021113286877233734982033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99347408857918155823321355 149021113286877233734982033)
  ·
    refine ⟨111765834965157925301236525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149021113286877233734982033 111765834965157925301236525)
    ·
      refine ⟨41912188111934221987963697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111765834965157925301236525 41912188111934221987963697)
      ·
        refine ⟨31434141083950666490972773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41912188111934221987963697 31434141083950666490972773)
        ·
          refine ⟨5893901453240749967057395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31434141083950666490972773 5893901453240749967057395)
          ·
            refine ⟨8840852179861124950586093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893901453240749967057395 8840852179861124950586093)
            ·
              refine ⟨3315319567447921856469785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8840852179861124950586093 3315319567447921856469785)
              ·
                refine ⟨2486489675585941392352339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3315319567447921856469785 2486489675585941392352339)
                ·
                  refine ⟨3729734513378912088528509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486489675585941392352339 3729734513378912088528509)
                  ·
                    refine ⟨1398650442517092033198191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3729734513378912088528509 1398650442517092033198191)
                    ·
                      rfl

theorem cell22_4085793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_4085793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085793 prefixEnd_4085793 := by exact prefixLift 4085793
  have htrace : WordTrace (prefixWord ++ tailWord_4085793) baseStart_4085793 baseEnd_4085793 := by
    simpa [prefixWord, tailWord_4085793, baseEnd_4085793] using wordTrace_append hprefix tailTrace_4085793
  have hstable : (prefixWord ++ tailWord_4085793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085793).length < 2 ^ (prefixWord ++ tailWord_4085793).sum := by decide
  have hdescent : baseEnd_4085793 < baseStart_4085793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085806 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_4085806 : Nat := 118140960795 + 4085806 * 2 ^ 59
def prefixEnd_4085806 : Nat := 4983230072969 + 3 ^ 40 * 4085806 * 2
def baseEnd_4085806 : Nat := 466218297560921444207717

theorem tailTrace_4085806 : CollatzResearch.WordTrace tailWord_4085806 prefixEnd_4085806 466218297560921444207717 := by
  unfold tailWord_4085806
  simp only [CollatzResearch.WordTrace]
  refine ⟨18627698429478767119400659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99347724957220091303470181 18627698429478767119400659)
  ·
    refine ⟨27941547644218150679100989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18627698429478767119400659 27941547644218150679100989)
    ·
      refine ⟨10478080366581806504662871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27941547644218150679100989 10478080366581806504662871)
      ·
        refine ⟨15717120549872709756994307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10478080366581806504662871 15717120549872709756994307)
        ·
          refine ⟨23575680824809064635491461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15717120549872709756994307 23575680824809064635491461)
          ·
            refine ⟨4420440154651699619154649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23575680824809064635491461 4420440154651699619154649)
            ·
              refine ⟨3315330115988774714365987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420440154651699619154649 3315330115988774714365987)
              ·
                refine ⟨4972995173983162071548981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315330115988774714365987 4972995173983162071548981)
                ·
                  refine ⟨466218297560921444207717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4972995173983162071548981 466218297560921444207717)
                  ·
                    rfl

theorem cell22_4085806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_4085806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085806 prefixEnd_4085806 := by exact prefixLift 4085806
  have htrace : WordTrace (prefixWord ++ tailWord_4085806) baseStart_4085806 baseEnd_4085806 := by
    simpa [prefixWord, tailWord_4085806, baseEnd_4085806] using wordTrace_append hprefix tailTrace_4085806
  have hstable : (prefixWord ++ tailWord_4085806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085806).length < 2 ^ (prefixWord ++ tailWord_4085806).sum := by decide
  have hdescent : baseEnd_4085806 < baseStart_4085806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085832 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 4, 3]
def baseStart_4085832 : Nat := 118140960795 + 4085832 * 2 ^ 59
def prefixEnd_4085832 : Nat := 4983230072969 + 3 ^ 40 * 4085832 * 2
def baseEnd_4085832 : Nat := 1398663793014108931473071

theorem tailTrace_4085832 : CollatzResearch.WordTrace tailWord_4085832 prefixEnd_4085832 1398663793014108931473071 := by
  unfold tailWord_4085832
  simp only [CollatzResearch.WordTrace]
  refine ⟨74511267866867971697825875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99348357155823962263767833 74511267866867971697825875)
  ·
    refine ⟨111766901800301957546738813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74511267866867971697825875 111766901800301957546738813)
    ·
      refine ⟨41912588175113234080027055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111766901800301957546738813 41912588175113234080027055)
      ·
        refine ⟨62868882262669851120040583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41912588175113234080027055 62868882262669851120040583)
        ·
          refine ⟨94303323394004776680060875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62868882262669851120040583 94303323394004776680060875)
          ·
            refine ⟨141454985091007165020091313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94303323394004776680060875 141454985091007165020091313)
            ·
              refine ⟨106091238818255373765068485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141454985091007165020091313 106091238818255373765068485)
              ·
                refine ⟨19892107278422882580950341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106091238818255373765068485 19892107278422882580950341)
                ·
                  refine ⟨3729770114704290483928189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19892107278422882580950341 3729770114704290483928189)
                  ·
                    refine ⟨1398663793014108931473071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3729770114704290483928189 1398663793014108931473071)
                    ·
                      rfl

theorem cell22_4085832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_4085832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085832 prefixEnd_4085832 := by exact prefixLift 4085832
  have htrace : WordTrace (prefixWord ++ tailWord_4085832) baseStart_4085832 baseEnd_4085832 := by
    simpa [prefixWord, tailWord_4085832, baseEnd_4085832] using wordTrace_append hprefix tailTrace_4085832
  have hstable : (prefixWord ++ tailWord_4085832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085832).length < 2 ^ (prefixWord ++ tailWord_4085832).sum := by decide
  have hdescent : baseEnd_4085832 < baseStart_4085832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085845 : List Nat := [1, 3, 2, 2, 1, 13]
def baseStart_4085845 : Nat := 118140960795 + 4085845 * 2 ^ 59
def prefixEnd_4085845 : Nat := 4983230072969 + 3 ^ 40 * 4085845 * 2
def baseEnd_4085845 : Nat := 17267509175059027541951

theorem tailTrace_4085845 : CollatzResearch.WordTrace tailWord_4085845 prefixEnd_4085845 17267509175059027541951 := by
  unfold tailWord_4085845
  simp only [CollatzResearch.WordTrace]
  refine ⟨149023009882688846615874989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99348673255125897743916659 149023009882688846615874989)
  ·
    refine ⟨55883628706008317480953121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149023009882688846615874989 55883628706008317480953121)
    ·
      refine ⟨41912721529506238110714841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55883628706008317480953121 41912721529506238110714841)
      ·
        refine ⟨31434541147129678583036131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41912721529506238110714841 31434541147129678583036131)
        ·
          refine ⟨47151811720694517874554197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31434541147129678583036131 47151811720694517874554197)
          ·
            refine ⟨17267509175059027541951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 47151811720694517874554197 17267509175059027541951)
            ·
              rfl

theorem cell22_4085845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 13].length) (baseStart_4085845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085845 prefixEnd_4085845 := by exact prefixLift 4085845
  have htrace : WordTrace (prefixWord ++ tailWord_4085845) baseStart_4085845 baseEnd_4085845 := by
    simpa [prefixWord, tailWord_4085845, baseEnd_4085845] using wordTrace_append hprefix tailTrace_4085845
  have hstable : (prefixWord ++ tailWord_4085845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085845).length < 2 ^ (prefixWord ++ tailWord_4085845).sum := by decide
  have hdescent : baseEnd_4085845 < baseStart_4085845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085847 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 2, 4]
def baseStart_4085847 : Nat := 118140960795 + 4085847 * 2 ^ 59
def prefixEnd_4085847 : Nat := 4983230072969 + 3 ^ 40 * 4085847 * 2
def baseEnd_4085847 : Nat := 1398668927820653892348025

theorem tailTrace_4085847 : CollatzResearch.WordTrace tailWord_4085847 prefixEnd_4085847 1398668927820653892348025 := by
  unfold tailWord_4085847
  simp only [CollatzResearch.WordTrace]
  refine ⟨149023082828681600957447795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99348721885787733971631863 149023082828681600957447795)
  ·
    refine ⟨223534624243022401436171693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149023082828681600957447795 223534624243022401436171693)
    ·
      refine ⟨83825484091133400538564385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223534624243022401436171693 83825484091133400538564385)
      ·
        refine ⟨62869113068350050403923289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83825484091133400538564385 62869113068350050403923289)
        ·
          refine ⟨47151834801262537802942467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62869113068350050403923289 47151834801262537802942467)
          ·
            refine ⟨70727752201893806704413701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47151834801262537802942467 70727752201893806704413701)
            ·
              refine ⟨13261453537855088757077569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70727752201893806704413701 13261453537855088757077569)
              ·
                refine ⟨9946090153391316567808177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13261453537855088757077569 9946090153391316567808177)
                ·
                  refine ⟨7459567615043487425856133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9946090153391316567808177 7459567615043487425856133)
                  ·
                    refine ⟨1398668927820653892348025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7459567615043487425856133 1398668927820653892348025)
                    ·
                      rfl

theorem cell22_4085847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_4085847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085847 prefixEnd_4085847 := by exact prefixLift 4085847
  have htrace : WordTrace (prefixWord ++ tailWord_4085847) baseStart_4085847 baseEnd_4085847 := by
    simpa [prefixWord, tailWord_4085847, baseEnd_4085847] using wordTrace_append hprefix tailTrace_4085847
  have hstable : (prefixWord ++ tailWord_4085847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085847).length < 2 ^ (prefixWord ++ tailWord_4085847).sum := by decide
  have hdescent : baseEnd_4085847 < baseStart_4085847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085849 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 2, 3]
def baseStart_4085849 : Nat := 118140960795 + 4085849 * 2 ^ 59
def prefixEnd_4085849 : Nat := 4983230072969 + 3 ^ 40 * 4085849 * 2
def baseEnd_4085849 : Nat := 1398669612461526553798019

theorem tailTrace_4085849 : CollatzResearch.WordTrace tailWord_4085849 prefixEnd_4085849 1398669612461526553798019 := by
  unfold tailWord_4085849
  simp only [CollatzResearch.WordTrace]
  refine ⟨149023155774674355299020601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99348770516449570199347067 149023155774674355299020601)
  ·
    refine ⟨111767366831005766474265451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149023155774674355299020601 111767366831005766474265451)
    ·
      refine ⟨167651050246508649711398177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111767366831005766474265451 167651050246508649711398177)
      ·
        refine ⟨125738287684881487283548633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167651050246508649711398177 125738287684881487283548633)
        ·
          refine ⟨94303715763661115462661475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125738287684881487283548633 94303715763661115462661475)
          ·
            refine ⟨141455573645491673193992213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94303715763661115462661475 141455573645491673193992213)
            ·
              refine ⟨6630730014632422180968385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141455573645491673193992213 6630730014632422180968385)
              ·
                refine ⟨4973047510974316635726289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6630730014632422180968385 4973047510974316635726289)
                ·
                  refine ⟨3729785633230737476794717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4973047510974316635726289 3729785633230737476794717)
                  ·
                    refine ⟨1398669612461526553798019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3729785633230737476794717 1398669612461526553798019)
                    ·
                      rfl

theorem cell22_4085849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 3].length) (baseStart_4085849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085849 prefixEnd_4085849 := by exact prefixLift 4085849
  have htrace : WordTrace (prefixWord ++ tailWord_4085849) baseStart_4085849 baseEnd_4085849 := by
    simpa [prefixWord, tailWord_4085849, baseEnd_4085849] using wordTrace_append hprefix tailTrace_4085849
  have hstable : (prefixWord ++ tailWord_4085849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085849).length < 2 ^ (prefixWord ++ tailWord_4085849).sum := by decide
  have hdescent : baseEnd_4085849 < baseStart_4085849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085911 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 3, 3]
def baseStart_4085911 : Nat := 118140960795 + 4085911 * 2 ^ 59
def prefixEnd_4085911 : Nat := 4983230072969 + 3 ^ 40 * 4085911 * 2
def baseEnd_4085911 : Nat := 1398690836328579058747829

theorem tailTrace_4085911 : CollatzResearch.WordTrace tailWord_4085911 prefixEnd_4085911 1398690836328579058747829 := by
  unfold tailWord_4085911
  simp only [CollatzResearch.WordTrace]
  refine ⟨149025417100449739887777587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99350278066966493258518391 149025417100449739887777587)
  ·
    refine ⟨223538125650674609831666381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149025417100449739887777587 223538125650674609831666381)
    ·
      refine ⟨83826797119002978686874893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223538125650674609831666381 83826797119002978686874893)
      ·
        refine ⟨31435048919626117007578085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83826797119002978686874893 31435048919626117007578085)
        ·
          refine ⟨5894071672429896938920891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31435048919626117007578085 5894071672429896938920891)
          ·
            refine ⟨8841107508644845408381337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5894071672429896938920891 8841107508644845408381337)
            ·
              refine ⟨6630830631483634056286003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8841107508644845408381337 6630830631483634056286003)
              ·
                refine ⟨9946245947225451084429005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6630830631483634056286003 9946245947225451084429005)
                ·
                  refine ⟨3729842230209544156660877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9946245947225451084429005 3729842230209544156660877)
                  ·
                    refine ⟨1398690836328579058747829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3729842230209544156660877 1398690836328579058747829)
                    ·
                      rfl

theorem cell22_4085911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_4085911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085911 prefixEnd_4085911 := by exact prefixLift 4085911
  have htrace : WordTrace (prefixWord ++ tailWord_4085911) baseStart_4085911 baseEnd_4085911 := by
    simpa [prefixWord, tailWord_4085911, baseEnd_4085911] using wordTrace_append hprefix tailTrace_4085911
  have hstable : (prefixWord ++ tailWord_4085911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085911).length < 2 ^ (prefixWord ++ tailWord_4085911).sum := by decide
  have hdescent : baseEnd_4085911 < baseStart_4085911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085969 : List Nat := [1, 2, 2, 1, 2, 2, 2, 6, 4]
def baseStart_4085969 : Nat := 118140960795 + 4085969 * 2 ^ 59
def prefixEnd_4085969 : Nat := 4983230072969 + 3 ^ 40 * 4085969 * 2
def baseEnd_4085969 : Nat := 466236896971295413599217

theorem tailTrace_4085969 : CollatzResearch.WordTrace tailWord_4085969 prefixEnd_4085969 466236896971295413599217 := by
  unfold tailWord_4085969
  simp only [CollatzResearch.WordTrace]
  refine ⟨149027532534239615793388961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99351688356159743862259307 149027532534239615793388961)
  ·
    refine ⟨111770649400679711845041721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149027532534239615793388961 111770649400679711845041721)
    ·
      refine ⟨83827987050509783883781291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111770649400679711845041721 83827987050509783883781291)
      ·
        refine ⟨125741980575764675825671937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83827987050509783883781291 125741980575764675825671937)
        ·
          refine ⟨94306485431823506869253953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125741980575764675825671937 94306485431823506869253953)
          ·
            refine ⟨70729864073867630151940465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94306485431823506869253953 70729864073867630151940465)
            ·
              refine ⟨53047398055400722613955349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70729864073867630151940465 53047398055400722613955349)
              ·
                refine ⟨2486596783846908872529157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53047398055400722613955349 2486596783846908872529157)
                ·
                  refine ⟨466236896971295413599217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486596783846908872529157 466236896971295413599217)
                  ·
                    rfl

theorem cell22_4085969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 4].length) (baseStart_4085969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085969 prefixEnd_4085969 := by exact prefixLift 4085969
  have htrace : WordTrace (prefixWord ++ tailWord_4085969) baseStart_4085969 baseEnd_4085969 := by
    simpa [prefixWord, tailWord_4085969, baseEnd_4085969] using wordTrace_append hprefix tailTrace_4085969
  have hstable : (prefixWord ++ tailWord_4085969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085969).length < 2 ^ (prefixWord ++ tailWord_4085969).sum := by decide
  have hdescent : baseEnd_4085969 < baseStart_4085969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085999 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 2, 4]
def baseStart_4085999 : Nat := 118140960795 + 4085999 * 2 ^ 59
def prefixEnd_4085999 : Nat := 4983230072969 + 3 ^ 40 * 4085999 * 2
def baseEnd_4085999 : Nat := 1398720960526976162547559

theorem tailTrace_4085999 : CollatzResearch.WordTrace tailWord_4085999 prefixEnd_4085999 1398720960526976162547559 := by
  unfold tailWord_4085999
  simp only [CollatzResearch.WordTrace]
  refine ⟨149028626724130930916981051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99352417816087287277987367 149028626724130930916981051)
  ·
    refine ⟨223542940086196396375471577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149028626724130930916981051 223542940086196396375471577)
    ·
      refine ⟨167657205064647297281603683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223542940086196396375471577 167657205064647297281603683)
      ·
        refine ⟨251485807596970945922405525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167657205064647297281603683 251485807596970945922405525)
        ·
          refine ⟨11788397231108013090112759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251485807596970945922405525 11788397231108013090112759)
          ·
            refine ⟨17682595846662019635169139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11788397231108013090112759 17682595846662019635169139)
            ·
              refine ⟨26523893769993029452753709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17682595846662019635169139 26523893769993029452753709)
              ·
                refine ⟨9946460163747386044782641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26523893769993029452753709 9946460163747386044782641)
                ·
                  refine ⟨7459845122810539533586981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9946460163747386044782641 7459845122810539533586981)
                  ·
                    refine ⟨1398720960526976162547559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7459845122810539533586981 1398720960526976162547559)
                    ·
                      rfl

theorem cell22_4085999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_4085999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4085999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4085999 prefixEnd_4085999 := by exact prefixLift 4085999
  have htrace : WordTrace (prefixWord ++ tailWord_4085999) baseStart_4085999 baseEnd_4085999 := by
    simpa [prefixWord, tailWord_4085999, baseEnd_4085999] using wordTrace_append hprefix tailTrace_4085999
  have hstable : (prefixWord ++ tailWord_4085999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085999).length < 2 ^ (prefixWord ++ tailWord_4085999).sum := by decide
  have hdescent : baseEnd_4085999 < baseStart_4085999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086018 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_4086018 : Nat := 118140960795 + 4086018 * 2 ^ 59
def prefixEnd_4086018 : Nat := 4983230072969 + 3 ^ 40 * 4086018 * 2
def baseEnd_4086018 : Nat := 1398727464615266446322501

theorem tailTrace_4086018 : CollatzResearch.WordTrace tailWord_4086018 prefixEnd_4086018 1398727464615266446322501 := by
  unfold tailWord_4086018
  simp only [CollatzResearch.WordTrace]
  refine ⟨37257329927765524290480677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99352879807374731441281805 37257329927765524290480677)
  ·
    refine ⟨6985749361456035804465127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37257329927765524290480677 6985749361456035804465127)
    ·
      refine ⟨10478624042184053706697691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6985749361456035804465127 10478624042184053706697691)
      ·
        refine ⟨15717936063276080560046537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10478624042184053706697691 15717936063276080560046537)
        ·
          refine ⟨11788452047457060420034903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15717936063276080560046537 11788452047457060420034903)
          ·
            refine ⟨17682678071185590630052355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11788452047457060420034903 17682678071185590630052355)
            ·
              refine ⟨26524017106778385945078533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17682678071185590630052355 26524017106778385945078533)
              ·
                refine ⟨4973253207520947364702225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26524017106778385945078533 4973253207520947364702225)
                ·
                  refine ⟨3729939905640710523526669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4973253207520947364702225 3729939905640710523526669)
                  ·
                    refine ⟨1398727464615266446322501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3729939905640710523526669 1398727464615266446322501)
                    ·
                      rfl

theorem cell22_4086018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_4086018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086018 prefixEnd_4086018 := by exact prefixLift 4086018
  have htrace : WordTrace (prefixWord ++ tailWord_4086018) baseStart_4086018 baseEnd_4086018 := by
    simpa [prefixWord, tailWord_4086018, baseEnd_4086018] using wordTrace_append hprefix tailTrace_4086018
  have hstable : (prefixWord ++ tailWord_4086018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086018).length < 2 ^ (prefixWord ++ tailWord_4086018).sum := by decide
  have hdescent : baseEnd_4086018 < baseStart_4086018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086020 : List Nat := [2, 3, 2, 2, 3, 2, 2, 2, 4]
def baseStart_4086020 : Nat := 118140960795 + 4086020 * 2 ^ 59
def prefixEnd_4086020 : Nat := 4983230072969 + 3 ^ 40 * 4086020 * 2
def baseEnd_4086020 : Nat := 466242716418713035924165

theorem tailTrace_4086020 : CollatzResearch.WordTrace tailWord_4086020 prefixEnd_4086020 466242716418713035924165 := by
  unfold tailWord_4086020
  simp only [CollatzResearch.WordTrace]
  refine ⟨74514696328527425751747757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99352928438036567668997009 74514696328527425751747757)
  ·
    refine ⟨27943011123197784656905409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74514696328527425751747757 27943011123197784656905409)
    ·
      refine ⟨20957258342398338492679057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27943011123197784656905409 20957258342398338492679057)
      ·
        refine ⟨15717943756798753869509293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20957258342398338492679057 15717943756798753869509293)
        ·
          refine ⟨5894228908799532701065985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15717943756798753869509293 5894228908799532701065985)
          ·
            refine ⟨4420671681599649525799489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5894228908799532701065985 4420671681599649525799489)
            ·
              refine ⟨3315503761199737144349617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420671681599649525799489 3315503761199737144349617)
              ·
                refine ⟨2486627820899802858262213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3315503761199737144349617 2486627820899802858262213)
                ·
                  refine ⟨466242716418713035924165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486627820899802858262213 466242716418713035924165)
                  ·
                    rfl

theorem cell22_4086020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_4086020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086020 prefixEnd_4086020 := by exact prefixLift 4086020
  have htrace : WordTrace (prefixWord ++ tailWord_4086020) baseStart_4086020 baseEnd_4086020 := by
    simpa [prefixWord, tailWord_4086020, baseEnd_4086020] using wordTrace_append hprefix tailTrace_4086020
  have hstable : (prefixWord ++ tailWord_4086020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086020).length < 2 ^ (prefixWord ++ tailWord_4086020).sum := by decide
  have hdescent : baseEnd_4086020 < baseStart_4086020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086027 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 1, 8]
def baseStart_4086027 : Nat := 118140960795 + 4086027 * 2 ^ 59
def prefixEnd_4086027 : Nat := 4983230072969 + 3 ^ 40 * 4086027 * 2
def baseEnd_4086027 : Nat := 1398730545499193422847473

theorem tailTrace_4086027 : CollatzResearch.WordTrace tailWord_4086027 prefixEnd_4086027 1398730545499193422847473 := by
  unfold tailWord_4086027
  simp only [CollatzResearch.WordTrace]
  refine ⟨149029647968029491699000335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99353098645352994466000223 149029647968029491699000335)
  ·
    refine ⟨223544471952044237548500503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149029647968029491699000335 223544471952044237548500503)
    ·
      refine ⟨335316707928066356322750755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223544471952044237548500503 335316707928066356322750755)
      ·
        refine ⟨502975061892099534484126133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335316707928066356322750755 502975061892099534484126133)
        ·
          refine ⟨47153912052384331357886825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 502975061892099534484126133 47153912052384331357886825)
          ·
            refine ⟨35365434039288248518415119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47153912052384331357886825 35365434039288248518415119)
            ·
              refine ⟨53048151058932372777622679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35365434039288248518415119 53048151058932372777622679)
              ·
                refine ⟨79572226588398559166434019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53048151058932372777622679 79572226588398559166434019)
                ·
                  refine ⟨119358339882597838749651029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79572226588398559166434019 119358339882597838749651029)
                  ·
                    refine ⟨1398730545499193422847473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119358339882597838749651029 1398730545499193422847473)
                    ·
                      rfl

theorem cell22_4086027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_4086027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086027 prefixEnd_4086027 := by exact prefixLift 4086027
  have htrace : WordTrace (prefixWord ++ tailWord_4086027) baseStart_4086027 baseEnd_4086027 := by
    simpa [prefixWord, tailWord_4086027, baseEnd_4086027] using wordTrace_append hprefix tailTrace_4086027
  have hstable : (prefixWord ++ tailWord_4086027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086027).length < 2 ^ (prefixWord ++ tailWord_4086027).sum := by decide
  have hdescent : baseEnd_4086027 < baseStart_4086027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086074 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_4086074 : Nat := 118140960795 + 4086074 * 2 ^ 59
def prefixEnd_4086074 : Nat := 4983230072969 + 3 ^ 40 * 4086074 * 2
def baseEnd_4086074 : Nat := 1398746634559700966922329

theorem tailTrace_4086074 : CollatzResearch.WordTrace tailWord_4086074 prefixEnd_4086074 1398746634559700966922329 := by
  unfold tailWord_4086074
  simp only [CollatzResearch.WordTrace]
  refine ⟨37257840549714804681490319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99354241465906145817307517 37257840549714804681490319)
  ·
    refine ⟨55886760824572207022235479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37257840549714804681490319 55886760824572207022235479)
    ·
      refine ⟨83830141236858310533353219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55886760824572207022235479 83830141236858310533353219)
      ·
        refine ⟨125745211855287465800029829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83830141236858310533353219 125745211855287465800029829)
        ·
          refine ⟨23577227222866399837505593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125745211855287465800029829 23577227222866399837505593)
          ·
            refine ⟨17682920417149799878129195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23577227222866399837505593 17682920417149799878129195)
            ·
              refine ⟨26524380625724699817193793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17682920417149799878129195 26524380625724699817193793)
              ·
                refine ⟨19893285469293524862895345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26524380625724699817193793 19893285469293524862895345)
                ·
                  refine ⟨14919964101970143647171509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19893285469293524862895345 14919964101970143647171509)
                  ·
                    refine ⟨1398746634559700966922329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14919964101970143647171509 1398746634559700966922329)
                    ·
                      rfl

theorem cell22_4086074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_4086074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086074 prefixEnd_4086074 := by exact prefixLift 4086074
  have htrace : WordTrace (prefixWord ++ tailWord_4086074) baseStart_4086074 baseEnd_4086074 := by
    simpa [prefixWord, tailWord_4086074, baseEnd_4086074] using wordTrace_append hprefix tailTrace_4086074
  have hstable : (prefixWord ++ tailWord_4086074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086074).length < 2 ^ (prefixWord ++ tailWord_4086074).sum := by decide
  have hdescent : baseEnd_4086074 < baseStart_4086074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086153 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 2, 3]
def baseStart_4086153 : Nat := 118140960795 + 4086153 * 2 ^ 59
def prefixEnd_4086153 : Nat := 4983230072969 + 3 ^ 40 * 4086153 * 2
def baseEnd_4086153 : Nat := 1398773677874171094197087

theorem tailTrace_4086153 : CollatzResearch.WordTrace tailWord_4086153 prefixEnd_4086153 1398773677874171094197087 := by
  unfold tailWord_4086153
  simp only [CollatzResearch.WordTrace]
  refine ⟨149034243565573015218087113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99356162377048676812058075 149034243565573015218087113)
  ·
    refine ⟨111775682674179761413565335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149034243565573015218087113 111775682674179761413565335)
    ·
      refine ⟨167663524011269642120348003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111775682674179761413565335 167663524011269642120348003)
      ·
        refine ⟨251495286016904463180522005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167663524011269642120348003 251495286016904463180522005)
        ·
          refine ⟨11788841532042396711586969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251495286016904463180522005 11788841532042396711586969)
          ·
            refine ⟨8841631149031797533690227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11788841532042396711586969 8841631149031797533690227)
            ·
              refine ⟨13262446723547696300535341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8841631149031797533690227 13262446723547696300535341)
              ·
                refine ⟨4973417521330386112700753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13262446723547696300535341 4973417521330386112700753)
                ·
                  refine ⟨3730063140997789584525565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4973417521330386112700753 3730063140997789584525565)
                  ·
                    refine ⟨1398773677874171094197087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3730063140997789584525565 1398773677874171094197087)
                    ·
                      rfl

theorem cell22_4086153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 3].length) (baseStart_4086153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086153 prefixEnd_4086153 := by exact prefixLift 4086153
  have htrace : WordTrace (prefixWord ++ tailWord_4086153) baseStart_4086153 baseEnd_4086153 := by
    simpa [prefixWord, tailWord_4086153, baseEnd_4086153] using wordTrace_append hprefix tailTrace_4086153
  have hstable : (prefixWord ++ tailWord_4086153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086153).length < 2 ^ (prefixWord ++ tailWord_4086153).sum := by decide
  have hdescent : baseEnd_4086153 < baseStart_4086153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086168 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 2, 4]
def baseStart_4086168 : Nat := 118140960795 + 4086168 * 2 ^ 59
def prefixEnd_4086168 : Nat := 4983230072969 + 3 ^ 40 * 4086168 * 2
def baseEnd_4086168 : Nat := 1398778812680716055072041

theorem tailTrace_4086168 : CollatzResearch.WordTrace tailWord_4086168 prefixEnd_4086168 1398778812680716055072041 := by
  unfold tailWord_4086168
  simp only [CollatzResearch.WordTrace]
  refine ⟨74517395330259336389941579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99356527107012448519922105 74517395330259336389941579)
  ·
    refine ⟨111776092995389004584912369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74517395330259336389941579 111776092995389004584912369)
    ·
      refine ⟨83832069746541753438684277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111776092995389004584912369 83832069746541753438684277)
      ·
        refine ⟨7859256538738289384876651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83832069746541753438684277 7859256538738289384876651)
        ·
          refine ⟨11788884808107434077314977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7859256538738289384876651 11788884808107434077314977)
          ·
            refine ⟨8841663606080575557986233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11788884808107434077314977 8841663606080575557986233)
            ·
              refine ⟨6631247704560431668489675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8841663606080575557986233 6631247704560431668489675)
              ·
                refine ⟨9946871556840647502734513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631247704560431668489675 9946871556840647502734513)
                ·
                  refine ⟨7460153667630485627050885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9946871556840647502734513 7460153667630485627050885)
                  ·
                    refine ⟨1398778812680716055072041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7460153667630485627050885 1398778812680716055072041)
                    ·
                      rfl

theorem cell22_4086168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_4086168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086168 prefixEnd_4086168 := by exact prefixLift 4086168
  have htrace : WordTrace (prefixWord ++ tailWord_4086168) baseStart_4086168 baseEnd_4086168 := by
    simpa [prefixWord, tailWord_4086168, baseEnd_4086168] using wordTrace_append hprefix tailTrace_4086168
  have hstable : (prefixWord ++ tailWord_4086168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086168).length < 2 ^ (prefixWord ++ tailWord_4086168).sum := by decide
  have hdescent : baseEnd_4086168 < baseStart_4086168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086189 : List Nat := [1, 5, 2, 2, 3, 1, 2, 2, 4]
def baseStart_4086189 : Nat := 118140960795 + 4086189 * 2 ^ 59
def prefixEnd_4086189 : Nat := 4983230072969 + 3 ^ 40 * 4086189 * 2
def baseEnd_4086189 : Nat := 466262000469959666765659

theorem tailTrace_4086189 : CollatzResearch.WordTrace tailWord_4086189 prefixEnd_4086189 466262000469959666765659 := by
  unfold tailWord_4086189
  simp only [CollatzResearch.WordTrace]
  refine ⟨149035556593442593366397621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99357037728961728910931747 149035556593442593366397621)
  ·
    refine ⟨13972083430635243128099777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149035556593442593366397621 13972083430635243128099777)
    ·
      refine ⟨10479062572976432346074833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13972083430635243128099777 10479062572976432346074833)
      ·
        refine ⟨7859296929732324259556125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10479062572976432346074833 7859296929732324259556125)
        ·
          refine ⟨2947236348649621597333547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7859296929732324259556125 2947236348649621597333547)
          ·
            refine ⟨4420854522974432396000321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947236348649621597333547 4420854522974432396000321)
            ·
              refine ⟨3315640892230824297000241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420854522974432396000321 3315640892230824297000241)
              ·
                refine ⟨2486730669173118222750181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3315640892230824297000241 2486730669173118222750181)
                ·
                  refine ⟨466262000469959666765659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486730669173118222750181 466262000469959666765659)
                  ·
                    rfl

theorem cell22_4086189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_4086189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086189 prefixEnd_4086189 := by exact prefixLift 4086189
  have htrace : WordTrace (prefixWord ++ tailWord_4086189) baseStart_4086189 baseEnd_4086189 := by
    simpa [prefixWord, tailWord_4086189, baseEnd_4086189] using wordTrace_append hprefix tailTrace_4086189
  have hstable : (prefixWord ++ tailWord_4086189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086189).length < 2 ^ (prefixWord ++ tailWord_4086189).sum := by decide
  have hdescent : baseEnd_4086189 < baseStart_4086189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086245 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 5]
def baseStart_4086245 : Nat := 118140960795 + 4086245 * 2 ^ 59
def prefixEnd_4086245 : Nat := 4983230072969 + 3 ^ 40 * 4086245 * 2
def baseEnd_4086245 : Nat := 466268390451437840298935

theorem tailTrace_4086245 : CollatzResearch.WordTrace tailWord_4086245 prefixEnd_4086245 466268390451437840298935 := by
  unfold tailWord_4086245
  simp only [CollatzResearch.WordTrace]
  refine ⟨149037599081239714930436189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99358399387493143286957459 149037599081239714930436189)
  ·
    refine ⟨55889099655464893098913571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149037599081239714930436189 55889099655464893098913571)
    ·
      refine ⟨83833649483197339648370357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55889099655464893098913571 83833649483197339648370357)
      ·
        refine ⟨7859404639049750592034721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83833649483197339648370357 7859404639049750592034721)
        ·
          refine ⟨5894553479287312944026041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7859404639049750592034721 5894553479287312944026041)
          ·
            refine ⟨4420915109465484708019531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5894553479287312944026041 4420915109465484708019531)
            ·
              refine ⟨6631372664198227062029297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420915109465484708019531 6631372664198227062029297)
              ·
                refine ⟨4973529498148670296521973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6631372664198227062029297 4973529498148670296521973)
                ·
                  refine ⟨466268390451437840298935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4973529498148670296521973 466268390451437840298935)
                  ·
                    rfl

theorem cell22_4086245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_4086245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086245 prefixEnd_4086245 := by exact prefixLift 4086245
  have htrace : WordTrace (prefixWord ++ tailWord_4086245) baseStart_4086245 baseEnd_4086245 := by
    simpa [prefixWord, tailWord_4086245, baseEnd_4086245] using wordTrace_append hprefix tailTrace_4086245
  have hstable : (prefixWord ++ tailWord_4086245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086245).length < 2 ^ (prefixWord ++ tailWord_4086245).sum := by decide
  have hdescent : baseEnd_4086245 < baseStart_4086245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086256 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 6]
def baseStart_4086256 : Nat := 118140960795 + 4086256 * 2 ^ 59
def prefixEnd_4086256 : Nat := 4983230072969 + 3 ^ 40 * 4086256 * 2
def baseEnd_4086256 : Nat := 466269645626371052957257

theorem tailTrace_4086256 : CollatzResearch.WordTrace tailWord_4086256 prefixEnd_4086256 466269645626371052957257 := by
  unfold tailWord_4086256
  simp only [CollatzResearch.WordTrace]
  refine ⟨74519000142099931904543311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99358666856133242539391081 74519000142099931904543311)
  ·
    refine ⟨111778500213149897856814967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74519000142099931904543311 111778500213149897856814967)
    ·
      refine ⟨167667750319724846785222451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111778500213149897856814967 167667750319724846785222451)
      ·
        refine ⟨251501625479587270177833677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167667750319724846785222451 251501625479587270177833677)
        ·
          refine ⟨94313109554845226316687629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251501625479587270177833677 94313109554845226316687629)
          ·
            refine ⟨35367416083066959868757861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94313109554845226316687629 35367416083066959868757861)
            ·
              refine ⟨6631390515575054975392099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35367416083066959868757861 6631390515575054975392099)
              ·
                refine ⟨9947085773362582463088149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631390515575054975392099 9947085773362582463088149)
                ·
                  refine ⟨466269645626371052957257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9947085773362582463088149 466269645626371052957257)
                  ·
                    rfl

theorem cell22_4086256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_4086256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086256 prefixEnd_4086256 := by exact prefixLift 4086256
  have htrace : WordTrace (prefixWord ++ tailWord_4086256) baseStart_4086256 baseEnd_4086256 := by
    simpa [prefixWord, tailWord_4086256, baseEnd_4086256] using wordTrace_append hprefix tailTrace_4086256
  have hstable : (prefixWord ++ tailWord_4086256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086256).length < 2 ^ (prefixWord ++ tailWord_4086256).sum := by decide
  have hdescent : baseEnd_4086256 < baseStart_4086256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086301 : List Nat := [1, 4, 2, 2, 1, 2, 10]
def baseStart_4086301 : Nat := 118140960795 + 4086301 * 2 ^ 59
def prefixEnd_4086301 : Nat := 4983230072969 + 3 ^ 40 * 4086301 * 2
def baseEnd_4086301 : Nat := 51808308936990668203579

theorem tailTrace_4086301 : CollatzResearch.WordTrace tailWord_4086301 prefixEnd_4086301 51808308936990668203579 := by
  unfold tailWord_4086301
  simp only [CollatzResearch.WordTrace]
  refine ⟨149039641569036836494474757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99359761046024557662983171 149039641569036836494474757)
  ·
    refine ⟨27944932794194406842714017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149039641569036836494474757 27944932794194406842714017)
    ·
      refine ⟨20958699595645805132035513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27944932794194406842714017 20958699595645805132035513)
      ·
        refine ⟨15719024696734353849026635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20958699595645805132035513 15719024696734353849026635)
        ·
          refine ⟨23578537045101530773539953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15719024696734353849026635 23578537045101530773539953)
          ·
            refine ⟨17683902783826148080154965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23578537045101530773539953 17683902783826148080154965)
            ·
              refine ⟨51808308936990668203579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17683902783826148080154965 51808308936990668203579)
              ·
                rfl

theorem cell22_4086301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 10].length) (baseStart_4086301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086301 prefixEnd_4086301 := by exact prefixLift 4086301
  have htrace : WordTrace (prefixWord ++ tailWord_4086301) baseStart_4086301 baseEnd_4086301 := by
    simpa [prefixWord, tailWord_4086301, baseEnd_4086301] using wordTrace_append hprefix tailTrace_4086301
  have hstable : (prefixWord ++ tailWord_4086301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086301).length < 2 ^ (prefixWord ++ tailWord_4086301).sum := by decide
  have hdescent : baseEnd_4086301 < baseStart_4086301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086378 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_4086378 : Nat := 118140960795 + 4086378 * 2 ^ 59
def prefixEnd_4086378 : Nat := 4983230072969 + 3 ^ 40 * 4086378 * 2
def baseEnd_4086378 : Nat := 1398850699972345507321397

theorem tailTrace_4086378 : CollatzResearch.WordTrace tailWord_4086378 prefixEnd_4086378 1398850699972345507321397 := by
  unfold tailWord_4086378
  simp only [CollatzResearch.WordTrace]
  refine ⟨37260612497439469661256947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99361633326505252430018525 37260612497439469661256947)
  ·
    refine ⟨55890918746159204491885421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37260612497439469661256947 55890918746159204491885421)
    ·
      refine ⟨20959094529809701684457033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55890918746159204491885421 20959094529809701684457033)
      ·
        refine ⟨15719320897357276263342775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20959094529809701684457033 15719320897357276263342775)
        ·
          refine ⟨23578981346035914395014163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15719320897357276263342775 23578981346035914395014163)
          ·
            refine ⟨35368472019053871592521245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23578981346035914395014163 35368472019053871592521245)
            ·
              refine ⟨13263177007145201847195467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35368472019053871592521245 13263177007145201847195467)
              ·
                refine ⟨19894765510717802770793201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13263177007145201847195467 19894765510717802770793201)
                ·
                  refine ⟨14921074133038352078094901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19894765510717802770793201 14921074133038352078094901)
                  ·
                    refine ⟨1398850699972345507321397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14921074133038352078094901 1398850699972345507321397)
                    ·
                      rfl

theorem cell22_4086378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_4086378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086378 prefixEnd_4086378 := by exact prefixLift 4086378
  have htrace : WordTrace (prefixWord ++ tailWord_4086378) baseStart_4086378 baseEnd_4086378 := by
    simpa [prefixWord, tailWord_4086378, baseEnd_4086378] using wordTrace_append hprefix tailTrace_4086378
  have hstable : (prefixWord ++ tailWord_4086378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086378).length < 2 ^ (prefixWord ++ tailWord_4086378).sum := by decide
  have hdescent : baseEnd_4086378 < baseStart_4086378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086391 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 8]
def baseStart_4086391 : Nat := 118140960795 + 4086391 * 2 ^ 59
def prefixEnd_4086391 : Nat := 4983230072969 + 3 ^ 40 * 4086391 * 2
def baseEnd_4086391 : Nat := 466285050046005935582119

theorem tailTrace_4086391 : CollatzResearch.WordTrace tailWord_4086391 prefixEnd_4086391 466285050046005935582119 := by
  unfold tailWord_4086391
  simp only [CollatzResearch.WordTrace]
  refine ⟨149042924138710781865251027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99361949425807187910167351 149042924138710781865251027)
  ·
    refine ⟨223564386208066172797876541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149042924138710781865251027 223564386208066172797876541)
    ·
      refine ⟨83836644828024814799203703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223564386208066172797876541 83836644828024814799203703)
      ·
        refine ⟨125754967242037222198805555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83836644828024814799203703 125754967242037222198805555)
        ·
          refine ⟨188632450863055833298208333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125754967242037222198805555 188632450863055833298208333)
          ·
            refine ⟨70737169073645937486828125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188632450863055833298208333 70737169073645937486828125)
            ·
              refine ⟨26526438402617226557560547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70737169073645937486828125 26526438402617226557560547)
              ·
                refine ⟨39789657603925839836340821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26526438402617226557560547 39789657603925839836340821)
                ·
                  refine ⟨466285050046005935582119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39789657603925839836340821 466285050046005935582119)
                  ·
                    rfl

theorem cell22_4086391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 8].length) (baseStart_4086391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086391 prefixEnd_4086391 := by exact prefixLift 4086391
  have htrace : WordTrace (prefixWord ++ tailWord_4086391) baseStart_4086391 baseEnd_4086391 := by
    simpa [prefixWord, tailWord_4086391, baseEnd_4086391] using wordTrace_append hprefix tailTrace_4086391
  have hstable : (prefixWord ++ tailWord_4086391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086391).length < 2 ^ (prefixWord ++ tailWord_4086391).sum := by decide
  have hdescent : baseEnd_4086391 < baseStart_4086391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086393 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 3, 4]
def baseStart_4086393 : Nat := 118140960795 + 4086393 * 2 ^ 59
def prefixEnd_4086393 : Nat := 4983230072969 + 3 ^ 40 * 4086393 * 2
def baseEnd_4086393 : Nat := 1398855834778890468196351

theorem tailTrace_4086393 : CollatzResearch.WordTrace tailWord_4086393 prefixEnd_4086393 1398855834778890468196351 := by
  unfold tailWord_4086393
  simp only [CollatzResearch.WordTrace]
  refine ⟨149042997084703536206823833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99361998056469024137882555 149042997084703536206823833)
  ·
    refine ⟨111782247813527652155117875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149042997084703536206823833 111782247813527652155117875)
    ·
      refine ⟨167673371720291478232676813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111782247813527652155117875 167673371720291478232676813)
      ·
        refine ⟨62877514395109304337253805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167673371720291478232676813 62877514395109304337253805)
        ·
          refine ⟨23579067898165989126470177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62877514395109304337253805 23579067898165989126470177)
          ·
            refine ⟨17684300923624491844852633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23579067898165989126470177 17684300923624491844852633)
            ·
              refine ⟨13263225692718368883639475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17684300923624491844852633 13263225692718368883639475)
              ·
                refine ⟨19894838539077553325459213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13263225692718368883639475 19894838539077553325459213)
                ·
                  refine ⟨7460564452154082497047205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19894838539077553325459213 7460564452154082497047205)
                  ·
                    refine ⟨1398855834778890468196351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7460564452154082497047205 1398855834778890468196351)
                    ·
                      rfl

theorem cell22_4086393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_4086393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086393 prefixEnd_4086393 := by exact prefixLift 4086393
  have htrace : WordTrace (prefixWord ++ tailWord_4086393) baseStart_4086393 baseEnd_4086393 := by
    simpa [prefixWord, tailWord_4086393, baseEnd_4086393] using wordTrace_append hprefix tailTrace_4086393
  have hstable : (prefixWord ++ tailWord_4086393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086393).length < 2 ^ (prefixWord ++ tailWord_4086393).sum := by decide
  have hdescent : baseEnd_4086393 < baseStart_4086393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086528 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 7, 4]
def baseStart_4086528 : Nat := 118140960795 + 4086528 * 2 ^ 59
def prefixEnd_4086528 : Nat := 4983230072969 + 3 ^ 40 * 4086528 * 2
def baseEnd_4086528 : Nat := 1398902048037795116070937

theorem tailTrace_4086528 : CollatzResearch.WordTrace tailWord_4086528 prefixEnd_4086528 1398902048037795116070937 := by
  unfold tailWord_4086528
  simp only [CollatzResearch.WordTrace]
  refine ⟨74523960469607227131494119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99365280626142969508658825 74523960469607227131494119)
  ·
    refine ⟨111785940704410840697241179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74523960469607227131494119 111785940704410840697241179)
    ·
      refine ⟨167678911056616261045861769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111785940704410840697241179 167678911056616261045861769)
      ·
        refine ⟨125759183292462195784396327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167678911056616261045861769 125759183292462195784396327)
        ·
          refine ⟨188638774938693293676594491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125759183292462195784396327 188638774938693293676594491)
          ·
            refine ⟨282958162408039940514891737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188638774938693293676594491 282958162408039940514891737)
            ·
              refine ⟨212218621806029955386168803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282958162408039940514891737 212218621806029955386168803)
              ·
                refine ⟨318327932709044933079253205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212218621806029955386168803 318327932709044933079253205)
                ·
                  refine ⟨7460810922868240619044997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 318327932709044933079253205 7460810922868240619044997)
                  ·
                    refine ⟨1398902048037795116070937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7460810922868240619044997 1398902048037795116070937)
                    ·
                      rfl

theorem cell22_4086528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_4086528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086528 prefixEnd_4086528 := by exact prefixLift 4086528
  have htrace : WordTrace (prefixWord ++ tailWord_4086528) baseStart_4086528 baseEnd_4086528 := by
    simpa [prefixWord, tailWord_4086528, baseEnd_4086528] using wordTrace_append hprefix tailTrace_4086528
  have hstable : (prefixWord ++ tailWord_4086528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086528).length < 2 ^ (prefixWord ++ tailWord_4086528).sum := by decide
  have hdescent : baseEnd_4086528 < baseStart_4086528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086536 : List Nat := [2, 1, 3, 2, 2, 4, 2, 2, 1, 3]
def baseStart_4086536 : Nat := 118140960795 + 4086536 * 2 ^ 59
def prefixEnd_4086536 : Nat := 4983230072969 + 3 ^ 40 * 4086536 * 2
def baseEnd_4086536 : Nat := 1398904786601285761870913

theorem tailTrace_4086536 : CollatzResearch.WordTrace tailWord_4086536 prefixEnd_4086536 1398904786601285761870913 := by
  unfold tailWord_4086536
  simp only [CollatzResearch.WordTrace]
  refine ⟨74524106361592735814639731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99365475148790314419519641 74524106361592735814639731)
  ·
    refine ⟨111786159542389103721959597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74524106361592735814639731 111786159542389103721959597)
    ·
      refine ⟨41919809828395913895734849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111786159542389103721959597 41919809828395913895734849)
      ·
        refine ⟨31439857371296935421801137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41919809828395913895734849 31439857371296935421801137)
        ·
          refine ⟨23579893028472701566350853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31439857371296935421801137 23579893028472701566350853)
          ·
            refine ⟨4421229942838631543690785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23579893028472701566350853 4421229942838631543690785)
            ·
              refine ⟨3315922457128973657768089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4421229942838631543690785 3315922457128973657768089)
              ·
                refine ⟨2486941842846730243326067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3315922457128973657768089 2486941842846730243326067)
                ·
                  refine ⟨3730412764270095364989101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486941842846730243326067 3730412764270095364989101)
                  ·
                    refine ⟨1398904786601285761870913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3730412764270095364989101 1398904786601285761870913)
                    ·
                      rfl

theorem cell22_4086536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_4086536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086536 prefixEnd_4086536 := by exact prefixLift 4086536
  have htrace : WordTrace (prefixWord ++ tailWord_4086536) baseStart_4086536 baseEnd_4086536 := by
    simpa [prefixWord, tailWord_4086536, baseEnd_4086536] using wordTrace_append hprefix tailTrace_4086536
  have hstable : (prefixWord ++ tailWord_4086536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086536).length < 2 ^ (prefixWord ++ tailWord_4086536).sum := by decide
  have hdescent : baseEnd_4086536 < baseStart_4086536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086543 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 6]
def baseStart_4086543 : Nat := 118140960795 + 4086543 * 2 ^ 59
def prefixEnd_4086543 : Nat := 4983230072969 + 3 ^ 40 * 4086543 * 2
def baseEnd_4086543 : Nat := 466302394281446692315297

theorem tailTrace_4086543 : CollatzResearch.WordTrace tailWord_4086543 prefixEnd_4086543 466302394281446692315297 := by
  unfold tailWord_4086543
  simp only [CollatzResearch.WordTrace]
  refine ⟨149048468034160111824784283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99365645356106741216522855 149048468034160111824784283)
  ·
    refine ⟨223572702051240167737176425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149048468034160111824784283 223572702051240167737176425)
    ·
      refine ⟨167679526538430125802882319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223572702051240167737176425 167679526538430125802882319)
      ·
        refine ⟨251519289807645188704323479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167679526538430125802882319 251519289807645188704323479)
        ·
          refine ⟨377278934711467783056485219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251519289807645188704323479 377278934711467783056485219)
          ·
            refine ⟨565918402067201674584727829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377278934711467783056485219 565918402067201674584727829)
            ·
              refine ⟨26527425096900078496159117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 565918402067201674584727829 26527425096900078496159117)
              ·
                refine ⟨9947784411337529436059669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26527425096900078496159117 9947784411337529436059669)
                ·
                  refine ⟨466302394281446692315297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9947784411337529436059669 466302394281446692315297)
                  ·
                    rfl

theorem cell22_4086543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 6].length) (baseStart_4086543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086543 prefixEnd_4086543 := by exact prefixLift 4086543
  have htrace : WordTrace (prefixWord ++ tailWord_4086543) baseStart_4086543 baseEnd_4086543 := by
    simpa [prefixWord, tailWord_4086543, baseEnd_4086543] using wordTrace_append hprefix tailTrace_4086543
  have hstable : (prefixWord ++ tailWord_4086543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086543).length < 2 ^ (prefixWord ++ tailWord_4086543).sum := by decide
  have hdescent : baseEnd_4086543 < baseStart_4086543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086560 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 6]
def baseStart_4086560 : Nat := 118140960795 + 4086560 * 2 ^ 59
def prefixEnd_4086560 : Nat := 4983230072969 + 3 ^ 40 * 4086560 * 2
def baseEnd_4086560 : Nat := 466304334097252566423613

theorem tailTrace_4086560 : CollatzResearch.WordTrace tailWord_4086560 prefixEnd_4086560 466304334097252566423613 := by
  unfold tailWord_4086560
  simp only [CollatzResearch.WordTrace]
  refine ⟨74524544037549261864076567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99366058716732349152102089 74524544037549261864076567)
  ·
    refine ⟨111786816056323892796114851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74524544037549261864076567 111786816056323892796114851)
    ·
      refine ⟨167680224084485839194172277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111786816056323892796114851 167680224084485839194172277)
      ·
        refine ⟨15720021007920547424453651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167680224084485839194172277 15720021007920547424453651)
        ·
          refine ⟨23580031511880821136680477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15720021007920547424453651 23580031511880821136680477)
          ·
            refine ⟨8842511816955307926255179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23580031511880821136680477 8842511816955307926255179)
            ·
              refine ⟨13263767725432961889382769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8842511816955307926255179 13263767725432961889382769)
              ·
                refine ⟨9947825794074721417037077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13263767725432961889382769 9947825794074721417037077)
                ·
                  refine ⟨466304334097252566423613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9947825794074721417037077 466304334097252566423613)
                  ·
                    rfl

theorem cell22_4086560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_4086560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086560 prefixEnd_4086560 := by exact prefixLift 4086560
  have htrace : WordTrace (prefixWord ++ tailWord_4086560) baseStart_4086560 baseEnd_4086560 := by
    simpa [prefixWord, tailWord_4086560, baseEnd_4086560] using wordTrace_append hprefix tailTrace_4086560
  have hstable : (prefixWord ++ tailWord_4086560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086560).length < 2 ^ (prefixWord ++ tailWord_4086560).sum := by decide
  have hdescent : baseEnd_4086560 < baseStart_4086560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086577 : List Nat := [1, 2, 2, 3, 2, 1, 4, 3, 4]
def baseStart_4086577 : Nat := 118140960795 + 4086577 * 2 ^ 59
def prefixEnd_4086577 : Nat := 4983230072969 + 3 ^ 40 * 4086577 * 2
def baseEnd_4086577 : Nat := 466306273913058440531929

theorem tailTrace_4086577 : CollatzResearch.WordTrace tailWord_4086577 prefixEnd_4086577 466306273913058440531929 := by
  unfold tailWord_4086577
  simp only [CollatzResearch.WordTrace]
  refine ⟨149049708116036935631521985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99366472077357957087681323 149049708116036935631521985)
  ·
    refine ⟨111787281087027701723641489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149049708116036935631521985 111787281087027701723641489)
    ·
      refine ⟨83840460815270776292731117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111787281087027701723641489 83840460815270776292731117)
      ·
        refine ⟨31440172805726541109774169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83840460815270776292731117 31440172805726541109774169)
        ·
          refine ⟨23580129604294905832330627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31440172805726541109774169 23580129604294905832330627)
          ·
            refine ⟨35370194406442358748495941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23580129604294905832330627 35370194406442358748495941)
            ·
              refine ⟨6631911451207942265342989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35370194406442358748495941 6631911451207942265342989)
              ·
                refine ⟨2486966794202978349503621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6631911451207942265342989 2486966794202978349503621)
                ·
                  refine ⟨466306273913058440531929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486966794202978349503621 466306273913058440531929)
                  ·
                    rfl

theorem cell22_4086577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 4].length) (baseStart_4086577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086577 prefixEnd_4086577 := by exact prefixLift 4086577
  have htrace : WordTrace (prefixWord ++ tailWord_4086577) baseStart_4086577 baseEnd_4086577 := by
    simpa [prefixWord, tailWord_4086577, baseEnd_4086577] using wordTrace_append hprefix tailTrace_4086577
  have hstable : (prefixWord ++ tailWord_4086577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086577).length < 2 ^ (prefixWord ++ tailWord_4086577).sum := by decide
  have hdescent : baseEnd_4086577 < baseStart_4086577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086579 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 1, 4]
def baseStart_4086579 : Nat := 118140960795 + 4086579 * 2 ^ 59
def prefixEnd_4086579 : Nat := 4983230072969 + 3 ^ 40 * 4086579 * 2
def baseEnd_4086579 : Nat := 1398919506380047983045781

theorem tailTrace_4086579 : CollatzResearch.WordTrace tailWord_4086579 prefixEnd_4086579 1398919506380047983045781 := by
  unfold tailWord_4086579
  simp only [CollatzResearch.WordTrace]
  refine ⟨149049781062029689973094791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99366520708019793315396527 149049781062029689973094791)
  ·
    refine ⟨223574671593044534959642187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149049781062029689973094791 223574671593044534959642187)
    ·
      refine ⟨335362007389566802439463281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223574671593044534959642187 335362007389566802439463281)
      ·
        refine ⟨251521505542175101829597461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335362007389566802439463281 251521505542175101829597461)
        ·
          refine ⟨11790070572289457898262381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251521505542175101829597461 11790070572289457898262381)
          ·
            refine ⟨4421276464608546711848393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11790070572289457898262381 4421276464608546711848393)
            ·
              refine ⟨3315957348456410033886295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4421276464608546711848393 3315957348456410033886295)
              ·
                refine ⟨4973936022684615050829443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315957348456410033886295 4973936022684615050829443)
                ·
                  refine ⟨7460904034026922576244165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973936022684615050829443 7460904034026922576244165)
                  ·
                    refine ⟨1398919506380047983045781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7460904034026922576244165 1398919506380047983045781)
                    ·
                      rfl

theorem cell22_4086579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 4].length) (baseStart_4086579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086579 prefixEnd_4086579 := by exact prefixLift 4086579
  have htrace : WordTrace (prefixWord ++ tailWord_4086579) baseStart_4086579 baseEnd_4086579 := by
    simpa [prefixWord, tailWord_4086579, baseEnd_4086579] using wordTrace_append hprefix tailTrace_4086579
  have hstable : (prefixWord ++ tailWord_4086579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086579).length < 2 ^ (prefixWord ++ tailWord_4086579).sum := by decide
  have hdescent : baseEnd_4086579 < baseStart_4086579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086609 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 1, 5]
def baseStart_4086609 : Nat := 118140960795 + 4086609 * 2 ^ 59
def prefixEnd_4086609 : Nat := 4983230072969 + 3 ^ 40 * 4086609 * 2
def baseEnd_4086609 : Nat := 1398929775993137904795689

theorem tailTrace_4086609 : CollatzResearch.WordTrace tailWord_4086609 prefixEnd_4086609 1398929775993137904795689 := by
  unfold tailWord_4086609
  simp only [CollatzResearch.WordTrace]
  refine ⟨149050875251921005096686881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99367250167947336731124587 149050875251921005096686881)
  ·
    refine ⟨111788156438940753822515161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149050875251921005096686881 111788156438940753822515161)
    ·
      refine ⟨83841117329205565366886371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111788156438940753822515161 83841117329205565366886371)
      ·
        refine ⟨125761675993808348050329557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83841117329205565366886371 125761675993808348050329557)
        ·
          refine ⟨2947539281104883157429599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 125761675993808348050329557 2947539281104883157429599)
          ·
            refine ⟨4421308921657324736144399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947539281104883157429599 4421308921657324736144399)
            ·
              refine ⟨6631963382485987104216599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421308921657324736144399 6631963382485987104216599)
              ·
                refine ⟨9947945073728980656324899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631963382485987104216599 9947945073728980656324899)
                ·
                  refine ⟨14921917610593470984487349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9947945073728980656324899 14921917610593470984487349)
                  ·
                    refine ⟨1398929775993137904795689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14921917610593470984487349 1398929775993137904795689)
                    ·
                      rfl

theorem cell22_4086609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_4086609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086609 prefixEnd_4086609 := by exact prefixLift 4086609
  have htrace : WordTrace (prefixWord ++ tailWord_4086609) baseStart_4086609 baseEnd_4086609 := by
    simpa [prefixWord, tailWord_4086609, baseEnd_4086609] using wordTrace_append hprefix tailTrace_4086609
  have hstable : (prefixWord ++ tailWord_4086609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086609).length < 2 ^ (prefixWord ++ tailWord_4086609).sum := by decide
  have hdescent : baseEnd_4086609 < baseStart_4086609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086650 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_4086650 : Nat := 118140960795 + 4086650 * 2 ^ 59
def prefixEnd_4086650 : Nat := 4983230072969 + 3 ^ 40 * 4086650 * 2
def baseEnd_4086650 : Nat := 466314603710342488173521

theorem tailTrace_4086650 : CollatzResearch.WordTrace tailWord_4086650 prefixEnd_4086650 466314603710342488173521 := by
  unfold tailWord_4086650
  simp only [CollatzResearch.WordTrace]
  refine ⟨37263092661193117274732351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99368247096514979399286269 37263092661193117274732351)
  ·
    refine ⟨55894638991789675912098527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37263092661193117274732351 55894638991789675912098527)
    ·
      refine ⟨83841958487684513868147791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55894638991789675912098527 83841958487684513868147791)
      ·
        refine ⟨125762937731526770802221687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83841958487684513868147791 125762937731526770802221687)
        ·
          refine ⟨188644406597290156203332531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125762937731526770802221687 188644406597290156203332531)
          ·
            refine ⟨282966609895935234304998797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188644406597290156203332531 282966609895935234304998797)
            ·
              refine ⟨106112478710975712864374549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282966609895935234304998797 106112478710975712864374549)
              ·
                refine ⟨4974022439576986540517557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106112478710975712864374549 4974022439576986540517557)
                ·
                  refine ⟨466314603710342488173521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974022439576986540517557 466314603710342488173521)
                  ·
                    rfl

theorem cell22_4086650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_4086650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086650 prefixEnd_4086650 := by exact prefixLift 4086650
  have htrace : WordTrace (prefixWord ++ tailWord_4086650) baseStart_4086650 baseEnd_4086650 := by
    simpa [prefixWord, tailWord_4086650, baseEnd_4086650] using wordTrace_append hprefix tailTrace_4086650
  have hstable : (prefixWord ++ tailWord_4086650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086650).length < 2 ^ (prefixWord ++ tailWord_4086650).sum := by decide
  have hdescent : baseEnd_4086650 < baseStart_4086650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086667 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 5]
def baseStart_4086667 : Nat := 118140960795 + 4086667 * 2 ^ 59
def prefixEnd_4086667 : Nat := 4983230072969 + 3 ^ 40 * 4086667 * 2
def baseEnd_4086667 : Nat := 466316543526148362281837

theorem tailTrace_4086667 : CollatzResearch.WordTrace tailWord_4086667 prefixEnd_4086667 466316543526148362281837 := by
  unfold tailWord_4086667
  simp only [CollatzResearch.WordTrace]
  refine ⟨149052990685710881002298255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99368660457140587334865503 149052990685710881002298255)
  ·
    refine ⟨223579486028566321503447383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149052990685710881002298255 223579486028566321503447383)
    ·
      refine ⟨335369229042849482255171075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223579486028566321503447383 335369229042849482255171075)
      ·
        refine ⟨503053843564274223382756613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335369229042849482255171075 503053843564274223382756613)
        ·
          refine ⟨94322595668301416884266865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503053843564274223382756613 94322595668301416884266865)
          ·
            refine ⟨70741946751226062663200149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94322595668301416884266865 70741946751226062663200149)
            ·
              refine ⟨3316028753963721687337507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70741946751226062663200149 3316028753963721687337507)
              ·
                refine ⟨4974043130945582531006261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316028753963721687337507 4974043130945582531006261)
                ·
                  refine ⟨466316543526148362281837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974043130945582531006261 466316543526148362281837)
                  ·
                    rfl

theorem cell22_4086667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 5].length) (baseStart_4086667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086667 prefixEnd_4086667 := by exact prefixLift 4086667
  have htrace : WordTrace (prefixWord ++ tailWord_4086667) baseStart_4086667 baseEnd_4086667 := by
    simpa [prefixWord, tailWord_4086667, baseEnd_4086667] using wordTrace_append hprefix tailTrace_4086667
  have hstable : (prefixWord ++ tailWord_4086667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086667).length < 2 ^ (prefixWord ++ tailWord_4086667).sum := by decide
  have hdescent : baseEnd_4086667 < baseStart_4086667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086701 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 5]
def baseStart_4086701 : Nat := 118140960795 + 4086701 * 2 ^ 59
def prefixEnd_4086701 : Nat := 4983230072969 + 3 ^ 40 * 4086701 * 2
def baseEnd_4086701 : Nat := 466320423157760110498469

theorem tailTrace_4086701 : CollatzResearch.WordTrace tailWord_4086701 prefixEnd_4086701 466320423157760110498469 := by
  unfold tailWord_4086701
  simp only [CollatzResearch.WordTrace]
  refine ⟨149054230767587704809035957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99369487178391803206023971 149054230767587704809035957)
  ·
    refine ⟨13973834134461347325847121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149054230767587704809035957 13973834134461347325847121)
    ·
      refine ⟨10480375600846010494385341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13973834134461347325847121 10480375600846010494385341)
      ·
        refine ⟨3930140850317253935394503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10480375600846010494385341 3930140850317253935394503)
        ·
          refine ⟨5895211275475880903091755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930140850317253935394503 5895211275475880903091755)
          ·
            refine ⟨8842816913213821354637633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5895211275475880903091755 8842816913213821354637633)
            ·
              refine ⟨6632112684910366015978225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8842816913213821354637633 6632112684910366015978225)
              ·
                refine ⟨4974084513682774511983669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6632112684910366015978225 4974084513682774511983669)
                ·
                  refine ⟨466320423157760110498469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974084513682774511983669 466320423157760110498469)
                  ·
                    rfl

theorem cell22_4086701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_4086701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086701 prefixEnd_4086701 := by exact prefixLift 4086701
  have htrace : WordTrace (prefixWord ++ tailWord_4086701) baseStart_4086701 baseEnd_4086701 := by
    simpa [prefixWord, tailWord_4086701, baseEnd_4086701] using wordTrace_append hprefix tailTrace_4086701
  have hstable : (prefixWord ++ tailWord_4086701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086701).length < 2 ^ (prefixWord ++ tailWord_4086701).sum := by decide
  have hdescent : baseEnd_4086701 < baseStart_4086701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086705 : List Nat := [1, 2, 2, 4, 4, 1, 2, 2, 1, 3]
def baseStart_4086705 : Nat := 118140960795 + 4086705 * 2 ^ 59
def prefixEnd_4086705 : Nat := 4983230072969 + 3 ^ 40 * 4086705 * 2
def baseEnd_4086705 : Nat := 1398962638755025654395395

theorem tailTrace_4086705 : CollatzResearch.WordTrace tailWord_4086705 prefixEnd_4086705 1398962638755025654395395 := by
  unfold tailWord_4086705
  simp only [CollatzResearch.WordTrace]
  refine ⟨149054376659573213492181569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99369584439715475661454379 149054376659573213492181569)
  ·
    refine ⟨111790782494679910119136177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149054376659573213492181569 111790782494679910119136177)
    ·
      refine ⟨83843086871009932589352133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111790782494679910119136177 83843086871009932589352133)
      ·
        refine ⟨15720578788314362360503525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83843086871009932589352133 15720578788314362360503525)
        ·
          refine ⟨2947608522808942942594411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15720578788314362360503525 2947608522808942942594411)
          ·
            refine ⟨4421412784213414413891617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947608522808942942594411 4421412784213414413891617)
            ·
              refine ⟨3316059588160060810418713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4421412784213414413891617 3316059588160060810418713)
              ·
                refine ⟨2487044691120045607814035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3316059588160060810418713 2487044691120045607814035)
                ·
                  refine ⟨3730567036680068411721053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487044691120045607814035 3730567036680068411721053)
                  ·
                    refine ⟨1398962638755025654395395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3730567036680068411721053 1398962638755025654395395)
                    ·
                      rfl

theorem cell22_4086705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_4086705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086705 prefixEnd_4086705 := by exact prefixLift 4086705
  have htrace : WordTrace (prefixWord ++ tailWord_4086705) baseStart_4086705 baseEnd_4086705 := by
    simpa [prefixWord, tailWord_4086705, baseEnd_4086705] using wordTrace_append hprefix tailTrace_4086705
  have hstable : (prefixWord ++ tailWord_4086705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086705).length < 2 ^ (prefixWord ++ tailWord_4086705).sum := by decide
  have hdescent : baseEnd_4086705 < baseStart_4086705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086823 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 3, 3]
def baseStart_4086823 : Nat := 118140960795 + 4086823 * 2 ^ 59
def prefixEnd_4086823 : Nat := 4983230072969 + 3 ^ 40 * 4086823 * 2
def baseEnd_4086823 : Nat := 1399003032566512679945033

theorem tailTrace_4086823 : CollatzResearch.WordTrace tailWord_4086823 prefixEnd_4086823 1399003032566512679945033 := by
  unfold tailWord_4086823
  simp only [CollatzResearch.WordTrace]
  refine ⟨149058680473145719644977123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99372453648763813096651415 149058680473145719644977123)
  ·
    refine ⟨223588020709718579467465685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149058680473145719644977123 223588020709718579467465685)
    ·
      refine ⟨5240344235384029206268727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 223588020709718579467465685 5240344235384029206268727)
      ·
        refine ⟨7860516353076043809403091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5240344235384029206268727 7860516353076043809403091)
        ·
          refine ⟨11790774529614065714104637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7860516353076043809403091 11790774529614065714104637)
          ·
            refine ⟨4421540448605274642789239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11790774529614065714104637 4421540448605274642789239)
            ·
              refine ⟨6632310672907911964183859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421540448605274642789239 6632310672907911964183859)
              ·
                refine ⟨9948466009361867946275789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632310672907911964183859 9948466009361867946275789)
                ·
                  refine ⟨3730674753510700479853421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9948466009361867946275789 3730674753510700479853421)
                  ·
                    refine ⟨1399003032566512679945033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3730674753510700479853421 1399003032566512679945033)
                    ·
                      rfl

theorem cell22_4086823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_4086823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086823 prefixEnd_4086823 := by exact prefixLift 4086823
  have htrace : WordTrace (prefixWord ++ tailWord_4086823) baseStart_4086823 baseEnd_4086823 := by
    simpa [prefixWord, tailWord_4086823, baseEnd_4086823] using wordTrace_append hprefix tailTrace_4086823
  have hstable : (prefixWord ++ tailWord_4086823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086823).length < 2 ^ (prefixWord ++ tailWord_4086823).sum := by decide
  have hdescent : baseEnd_4086823 < baseStart_4086823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086832 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 3, 4]
def baseStart_4086832 : Nat := 118140960795 + 4086832 * 2 ^ 59
def prefixEnd_4086832 : Nat := 4983230072969 + 3 ^ 40 * 4086832 * 2
def baseEnd_4086832 : Nat := 1399006113450439656470005

theorem tailTrace_4086832 : CollatzResearch.WordTrace tailWord_4086832 prefixEnd_4086832 1399006113450439656470005 := by
  unfold tailWord_4086832
  simp only [CollatzResearch.WordTrace]
  refine ⟨74529504365056557091027375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99372672486742076121369833 74529504365056557091027375)
  ·
    refine ⟨111794256547584835636541063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74529504365056557091027375 111794256547584835636541063)
    ·
      refine ⟨167691384821377253454811595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111794256547584835636541063 167691384821377253454811595)
      ·
        refine ⟨251537077232065880182217393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167691384821377253454811595 251537077232065880182217393)
        ·
          refine ⟨188652807924049410136663045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251537077232065880182217393 188652807924049410136663045)
          ·
            refine ⟨35372401485759264400624321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188652807924049410136663045 35372401485759264400624321)
            ·
              refine ⟨26529301114319448300468241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35372401485759264400624321 26529301114319448300468241)
              ·
                refine ⟨19896975835739586225351181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26529301114319448300468241 19896975835739586225351181)
                ·
                  refine ⟨7461365938402344834506693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19896975835739586225351181 7461365938402344834506693)
                  ·
                    refine ⟨1399006113450439656470005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7461365938402344834506693 1399006113450439656470005)
                    ·
                      rfl

theorem cell22_4086832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_4086832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086832 prefixEnd_4086832 := by exact prefixLift 4086832
  have htrace : WordTrace (prefixWord ++ tailWord_4086832) baseStart_4086832 baseEnd_4086832 := by
    simpa [prefixWord, tailWord_4086832, baseEnd_4086832] using wordTrace_append hprefix tailTrace_4086832
  have hstable : (prefixWord ++ tailWord_4086832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086832).length < 2 ^ (prefixWord ++ tailWord_4086832).sum := by decide
  have hdescent : baseEnd_4086832 < baseStart_4086832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086836 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 5]
def baseStart_4086836 : Nat := 118140960795 + 4086836 * 2 ^ 59
def prefixEnd_4086836 : Nat := 4983230072969 + 3 ^ 40 * 4086836 * 2
def baseEnd_4086836 : Nat := 466335827577394993123331

theorem tailTrace_4086836 : CollatzResearch.WordTrace tailWord_4086836 prefixEnd_4086836 466335827577394993123331 := by
  unfold tailWord_4086836
  simp only [CollatzResearch.WordTrace]
  refine ⟨74529577311049311432600181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99372769748065748576800241 74529577311049311432600181)
  ·
    refine ⟨6987147872910872946806267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74529577311049311432600181 6987147872910872946806267)
    ·
      refine ⟨10480721809366309420209401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6987147872910872946806267 10480721809366309420209401)
      ·
        refine ⟨7860541357024732065157051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10480721809366309420209401 7860541357024732065157051)
        ·
          refine ⟨11790812035537098097735577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7860541357024732065157051 11790812035537098097735577)
          ·
            refine ⟨8843109026652823573301683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11790812035537098097735577 8843109026652823573301683)
            ·
              refine ⟨13264663539979235359952525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8843109026652823573301683 13264663539979235359952525)
              ·
                refine ⟨4974248827492213259982197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13264663539979235359952525 4974248827492213259982197)
                ·
                  refine ⟨466335827577394993123331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974248827492213259982197 466335827577394993123331)
                  ·
                    rfl

theorem cell22_4086836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_4086836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086836 prefixEnd_4086836 := by exact prefixLift 4086836
  have htrace : WordTrace (prefixWord ++ tailWord_4086836) baseStart_4086836 baseEnd_4086836 := by
    simpa [prefixWord, tailWord_4086836, baseEnd_4086836] using wordTrace_append hprefix tailTrace_4086836
  have hstable : (prefixWord ++ tailWord_4086836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086836).length < 2 ^ (prefixWord ++ tailWord_4086836).sum := by decide
  have hdescent : baseEnd_4086836 < baseStart_4086836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086881 : List Nat := [1, 2, 3, 1, 1, 2, 6, 2, 4]
def baseStart_4086881 : Nat := 118140960795 + 4086881 * 2 ^ 59
def prefixEnd_4086881 : Nat := 4983230072969 + 3 ^ 40 * 4086881 * 2
def baseEnd_4086881 : Nat := 466340962383939953998285

theorem tailTrace_4086881 : CollatzResearch.WordTrace tailWord_4086881 prefixEnd_4086881 466340962383939953998285 := by
  unfold tailWord_4086881
  simp only [CollatzResearch.WordTrace]
  refine ⟨149060795906935595550588497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99373863937957063700392331 149060795906935595550588497)
  ·
    refine ⟨111795596930201696662941373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149060795906935595550588497 111795596930201696662941373)
    ·
      refine ⟨41923348848825636248603015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111795596930201696662941373 41923348848825636248603015)
      ·
        refine ⟨62885023273238454372904523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41923348848825636248603015 62885023273238454372904523)
        ·
          refine ⟨94327534909857681559356785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62885023273238454372904523 94327534909857681559356785)
          ·
            refine ⟨70745651182393261169517589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94327534909857681559356785 70745651182393261169517589)
            ·
              refine ⟨3316202399174684117321137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70745651182393261169517589 3316202399174684117321137)
              ·
                refine ⟨2487151799381013087990853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3316202399174684117321137 2487151799381013087990853)
                ·
                  refine ⟨466340962383939953998285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2487151799381013087990853 466340962383939953998285)
                  ·
                    rfl

theorem cell22_4086881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 4].length) (baseStart_4086881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086881 prefixEnd_4086881 := by exact prefixLift 4086881
  have htrace : WordTrace (prefixWord ++ tailWord_4086881) baseStart_4086881 baseEnd_4086881 := by
    simpa [prefixWord, tailWord_4086881, baseEnd_4086881] using wordTrace_append hprefix tailTrace_4086881
  have hstable : (prefixWord ++ tailWord_4086881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086881).length < 2 ^ (prefixWord ++ tailWord_4086881).sum := by decide
  have hdescent : baseEnd_4086881 < baseStart_4086881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086909 : List Nat := [1, 4, 1, 1, 3, 1, 5, 6]
def baseStart_4086909 : Nat := 118140960795 + 4086909 * 2 ^ 59
def prefixEnd_4086909 : Nat := 4983230072969 + 3 ^ 40 * 4086909 * 2
def baseEnd_4086909 : Nat := 155448052458226346921641

theorem tailTrace_4086909 : CollatzResearch.WordTrace tailWord_4086909 prefixEnd_4086909 155448052458226346921641 := by
  unfold tailWord_4086909
  simp only [CollatzResearch.WordTrace]
  refine ⟨149061817150834156332607781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99374544767222770888405187 149061817150834156332607781)
  ·
    refine ⟨27949090715781404312363959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149061817150834156332607781 27949090715781404312363959)
    ·
      refine ⟨41923636073672106468545939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27949090715781404312363959 41923636073672106468545939)
      ·
        refine ⟨62885454110508159702818909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41923636073672106468545939 62885454110508159702818909)
        ·
          refine ⟨23582045291440559888557091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62885454110508159702818909 23582045291440559888557091)
          ·
            refine ⟨35373067937160839832835637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23582045291440559888557091 35373067937160839832835637)
            ·
              refine ⟨3316225119108828734328341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35373067937160839832835637 3316225119108828734328341)
              ·
                refine ⟨155448052458226346921641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3316225119108828734328341 155448052458226346921641)
                ·
                  rfl

theorem cell22_4086909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 6].length) (baseStart_4086909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086909 prefixEnd_4086909 := by exact prefixLift 4086909
  have htrace : WordTrace (prefixWord ++ tailWord_4086909) baseStart_4086909 baseEnd_4086909 := by
    simpa [prefixWord, tailWord_4086909, baseEnd_4086909] using wordTrace_append hprefix tailTrace_4086909
  have hstable : (prefixWord ++ tailWord_4086909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086909).length < 2 ^ (prefixWord ++ tailWord_4086909).sum := by decide
  have hdescent : baseEnd_4086909 < baseStart_4086909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086941 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_4086941 : Nat := 118140960795 + 4086941 * 2 ^ 59
def prefixEnd_4086941 : Nat := 4983230072969 + 3 ^ 40 * 4086941 * 2
def baseEnd_4086941 : Nat := 1399043426377999705494671

theorem tailTrace_4086941 : CollatzResearch.WordTrace tailWord_4086941 prefixEnd_4086941 1399043426377999705494671 := by
  unfold tailWord_4086941
  simp only [CollatzResearch.WordTrace]
  refine ⟨149062984286718225797772677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99375322857812150531848451 149062984286718225797772677)
  ·
    refine ⟨27949309553759667337082377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149062984286718225797772677 27949309553759667337082377)
    ·
      refine ⟨20961982165319750502811783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27949309553759667337082377 20961982165319750502811783)
      ·
        refine ⟨31442973247979625754217675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20961982165319750502811783 31442973247979625754217675)
        ·
          refine ⟨47164459871969438631326513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31442973247979625754217675 47164459871969438631326513)
          ·
            refine ⟨35373344903977078973494885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47164459871969438631326513 35373344903977078973494885)
            ·
              refine ⟨6632502169495702307530291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35373344903977078973494885 6632502169495702307530291)
              ·
                refine ⟨9948753254243553461295437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632502169495702307530291 9948753254243553461295437)
                ·
                  refine ⟨3730782470341332547985789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9948753254243553461295437 3730782470341332547985789)
                  ·
                    refine ⟨1399043426377999705494671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3730782470341332547985789 1399043426377999705494671)
                    ·
                      rfl

theorem cell22_4086941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_4086941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086941 prefixEnd_4086941 := by exact prefixLift 4086941
  have htrace : WordTrace (prefixWord ++ tailWord_4086941) baseStart_4086941 baseEnd_4086941 := by
    simpa [prefixWord, tailWord_4086941, baseEnd_4086941] using wordTrace_append hprefix tailTrace_4086941
  have hstable : (prefixWord ++ tailWord_4086941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086941).length < 2 ^ (prefixWord ++ tailWord_4086941).sum := by decide
  have hdescent : baseEnd_4086941 < baseStart_4086941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086999 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 6]
def baseStart_4086999 : Nat := 118140960795 + 4086999 * 2 ^ 59
def prefixEnd_4086999 : Nat := 4983230072969 + 3 ^ 40 * 4086999 * 2
def baseEnd_4086999 : Nat := 466354426987768962514831

theorem tailTrace_4086999 : CollatzResearch.WordTrace tailWord_4086999 prefixEnd_4086999 466354426987768962514831 := by
  unfold tailWord_4086999
  simp only [CollatzResearch.WordTrace]
  refine ⟨149065099720508101703384051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99376733147005401135589367 149065099720508101703384051)
  ·
    refine ⟨223597649580762152555076077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149065099720508101703384051 223597649580762152555076077)
    ·
      refine ⟨83849118592785807208153529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223597649580762152555076077 83849118592785807208153529)
      ·
        refine ⟨62886838944589355406115147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83849118592785807208153529 62886838944589355406115147)
        ·
          refine ⟨94330258416884033109172721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62886838944589355406115147 94330258416884033109172721)
          ·
            refine ⟨70747693812663024831879541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94330258416884033109172721 70747693812663024831879541)
            ·
              refine ⟨6632596294937158577988707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70747693812663024831879541 6632596294937158577988707)
              ·
                refine ⟨9948894442405737866983061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632596294937158577988707 9948894442405737866983061)
                ·
                  refine ⟨466354426987768962514831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9948894442405737866983061 466354426987768962514831)
                  ·
                    rfl

theorem cell22_4086999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 6].length) (baseStart_4086999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4086999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4086999 prefixEnd_4086999 := by exact prefixLift 4086999
  have htrace : WordTrace (prefixWord ++ tailWord_4086999) baseStart_4086999 baseEnd_4086999 := by
    simpa [prefixWord, tailWord_4086999, baseEnd_4086999] using wordTrace_append hprefix tailTrace_4086999
  have hstable : (prefixWord ++ tailWord_4086999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086999).length < 2 ^ (prefixWord ++ tailWord_4086999).sum := by decide
  have hdescent : baseEnd_4086999 < baseStart_4086999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087005 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 5]
def baseStart_4087005 : Nat := 118140960795 + 4087005 * 2 ^ 59
def prefixEnd_4087005 : Nat := 4983230072969 + 3 ^ 40 * 4087005 * 2
def baseEnd_4087005 : Nat := 466355111628641623964825

theorem tailTrace_4087005 : CollatzResearch.WordTrace tailWord_4087005 prefixEnd_4087005 466355111628641623964825 := by
  unfold tailWord_4087005
  simp only [CollatzResearch.WordTrace]
  refine ⟨149065318558486364728102469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99376879038990909818734979 149065318558486364728102469)
  ·
    refine ⟨27949747229716193386519213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149065318558486364728102469 27949747229716193386519213)
    ·
      refine ⟨10481155211143572519944705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27949747229716193386519213 10481155211143572519944705)
      ·
        refine ⟨7860866408357679389958529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10481155211143572519944705 7860866408357679389958529)
        ·
          refine ⟨5895649806268259542468897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7860866408357679389958529 5895649806268259542468897)
          ·
            refine ⟨4421737354701194656851673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5895649806268259542468897 4421737354701194656851673)
            ·
              refine ⟨3316303016025895992638755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4421737354701194656851673 3316303016025895992638755)
              ·
                refine ⟨4974454524038843988958133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316303016025895992638755 4974454524038843988958133)
                ·
                  refine ⟨466355111628641623964825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974454524038843988958133 466355111628641623964825)
                  ·
                    rfl

theorem cell22_4087005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_4087005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087005 prefixEnd_4087005 := by exact prefixLift 4087005
  have htrace : WordTrace (prefixWord ++ tailWord_4087005) baseStart_4087005 baseEnd_4087005 := by
    simpa [prefixWord, tailWord_4087005, baseEnd_4087005] using wordTrace_append hprefix tailTrace_4087005
  have hstable : (prefixWord ++ tailWord_4087005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087005).length < 2 ^ (prefixWord ++ tailWord_4087005).sum := by decide
  have hdescent : baseEnd_4087005 < baseStart_4087005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087018 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 1, 4]
def baseStart_4087018 : Nat := 118140960795 + 4087018 * 2 ^ 59
def prefixEnd_4087018 : Nat := 4983230072969 + 3 ^ 40 * 4087018 * 2
def baseEnd_4087018 : Nat := 1399069785051597171319435

theorem tailTrace_4087018 : CollatzResearch.WordTrace tailWord_4087018 prefixEnd_4087018 1399069785051597171319435 := by
  unfold tailWord_4087018
  simp only [CollatzResearch.WordTrace]
  refine ⟨37266448176859816987081427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99377195138292845298883805 37266448176859816987081427)
  ·
    refine ⟨55899672265289725480622141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37266448176859816987081427 55899672265289725480622141)
    ·
      refine ⟨20962377099483647055233303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55899672265289725480622141 20962377099483647055233303)
      ·
        refine ⟨31443565649225470582849955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20962377099483647055233303 31443565649225470582849955)
        ·
          refine ⟨47165348473838205874274933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31443565649225470582849955 47165348473838205874274933)
          ·
            refine ⟨4421751419422331800713275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47165348473838205874274933 4421751419422331800713275)
            ·
              refine ⟨6632627129133497701069913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421751419422331800713275 6632627129133497701069913)
              ·
                refine ⟨4974470346850123275802435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6632627129133497701069913 4974470346850123275802435)
                ·
                  refine ⟨7461705520275184913703653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974470346850123275802435 7461705520275184913703653)
                  ·
                    refine ⟨1399069785051597171319435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7461705520275184913703653 1399069785051597171319435)
                    ·
                      rfl

theorem cell22_4087018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_4087018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087018 prefixEnd_4087018 := by exact prefixLift 4087018
  have htrace : WordTrace (prefixWord ++ tailWord_4087018) baseStart_4087018 baseEnd_4087018 := by
    simpa [prefixWord, tailWord_4087018, baseEnd_4087018] using wordTrace_append hprefix tailTrace_4087018
  have hstable : (prefixWord ++ tailWord_4087018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087018).length < 2 ^ (prefixWord ++ tailWord_4087018).sum := by decide
  have hdescent : baseEnd_4087018 < baseStart_4087018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087044 : List Nat := [2, 3, 2, 2, 2, 11]
def baseStart_4087044 : Nat := 118140960795 + 4087044 * 2 ^ 59
def prefixEnd_4087044 : Nat := 4983230072969 + 3 ^ 40 * 4087044 * 2
def baseEnd_4087044 : Nat := 17272576362752367532955

theorem tailTrace_4087044 : CollatzResearch.WordTrace tailWord_4087044 prefixEnd_4087044 17272576362752367532955 := by
  unfold tailWord_4087044
  simp only [CollatzResearch.WordTrace]
  refine ⟨74533370502672537194386093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99377827336896716259181457 74533370502672537194386093)
  ·
    refine ⟨27950013938502201447894785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74533370502672537194386093 27950013938502201447894785)
    ·
      refine ⟨20962510453876651085921089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27950013938502201447894785 20962510453876651085921089)
      ·
        refine ⟨15721882840407488314440817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20962510453876651085921089 15721882840407488314440817)
        ·
          refine ⟨11791412130305616235830613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15721882840407488314440817 11791412130305616235830613)
          ·
            refine ⟨17272576362752367532955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11791412130305616235830613 17272576362752367532955)
            ·
              rfl

theorem cell22_4087044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 11].length) (baseStart_4087044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087044 prefixEnd_4087044 := by exact prefixLift 4087044
  have htrace : WordTrace (prefixWord ++ tailWord_4087044) baseStart_4087044 baseEnd_4087044 := by
    simpa [prefixWord, tailWord_4087044, baseEnd_4087044] using wordTrace_append hprefix tailTrace_4087044
  have hstable : (prefixWord ++ tailWord_4087044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087044).length < 2 ^ (prefixWord ++ tailWord_4087044).sum := by decide
  have hdescent : baseEnd_4087044 < baseStart_4087044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087104 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_4087104 : Nat := 118140960795 + 4087104 * 2 ^ 59
def prefixEnd_4087104 : Nat := 4983230072969 + 3 ^ 40 * 4087104 * 2
def baseEnd_4087104 : Nat := 1399099224609121613669171

theorem tailTrace_4087104 : CollatzResearch.WordTrace tailWord_4087104 prefixEnd_4087104 1399099224609121613669171 := by
  unfold tailWord_4087104
  simp only [CollatzResearch.WordTrace]
  refine ⟨74534464692563852317978183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99379286256751803090637577 74534464692563852317978183)
  ·
    refine ⟨111801697038845778476967275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74534464692563852317978183 111801697038845778476967275)
    ·
      refine ⟨167702545558268667715450913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111801697038845778476967275 167702545558268667715450913)
      ·
        refine ⟨125776909168701500786588185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167702545558268667715450913 125776909168701500786588185)
        ·
          refine ⟨94332681876526125589941139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125776909168701500786588185 94332681876526125589941139)
          ·
            refine ⟨141499022814789188384911709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94332681876526125589941139 141499022814789188384911709)
            ·
              refine ⟨53062133555545945644341891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141499022814789188384911709 53062133555545945644341891)
              ·
                refine ⟨79593200333318918466512837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53062133555545945644341891 79593200333318918466512837)
                ·
                  refine ⟨14923725062497297212471157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79593200333318918466512837 14923725062497297212471157)
                  ·
                    refine ⟨1399099224609121613669171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14923725062497297212471157 1399099224609121613669171)
                    ·
                      rfl

theorem cell22_4087104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_4087104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087104 prefixEnd_4087104 := by exact prefixLift 4087104
  have htrace : WordTrace (prefixWord ++ tailWord_4087104) baseStart_4087104 baseEnd_4087104 := by
    simpa [prefixWord, tailWord_4087104, baseEnd_4087104] using wordTrace_append hprefix tailTrace_4087104
  have hstable : (prefixWord ++ tailWord_4087104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087104).length < 2 ^ (prefixWord ++ tailWord_4087104).sum := by decide
  have hdescent : baseEnd_4087104 < baseStart_4087104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087144 : List Nat := [2, 1, 4, 2, 4, 1, 1, 3, 1, 3]
def baseStart_4087144 : Nat := 118140960795 + 4087144 * 2 ^ 59
def prefixEnd_4087144 : Nat := 4983230072969 + 3 ^ 40 * 4087144 * 2
def baseEnd_4087144 : Nat := 1399112917426574842669049

theorem tailTrace_4087144 : CollatzResearch.WordTrace tailWord_4087144 prefixEnd_4087144 1399112917426574842669049 := by
  unfold tailWord_4087144
  simp only [CollatzResearch.WordTrace]
  refine ⟨74535194152491395733706243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99380258869988527644941657 74535194152491395733706243)
  ·
    refine ⟨111802791228737093600559365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74535194152491395733706243 111802791228737093600559365)
    ·
      refine ⟨20963023355388205050104881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111802791228737093600559365 20963023355388205050104881)
      ·
        refine ⟨15722267516541153787578661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20963023355388205050104881 15722267516541153787578661)
        ·
          refine ⟨2947925159351466335170999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15722267516541153787578661 2947925159351466335170999)
          ·
            refine ⟨4421887739027199502756499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947925159351466335170999 4421887739027199502756499)
            ·
              refine ⟨6632831608540799254134749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421887739027199502756499 6632831608540799254134749)
              ·
                refine ⟨2487311853202799720300531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6632831608540799254134749 2487311853202799720300531)
                ·
                  refine ⟨3730967779804199580450797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487311853202799720300531 3730967779804199580450797)
                  ·
                    refine ⟨1399112917426574842669049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3730967779804199580450797 1399112917426574842669049)
                    ·
                      rfl

theorem cell22_4087144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_4087144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087144 prefixEnd_4087144 := by exact prefixLift 4087144
  have htrace : WordTrace (prefixWord ++ tailWord_4087144) baseStart_4087144 baseEnd_4087144 := by
    simpa [prefixWord, tailWord_4087144, baseEnd_4087144] using wordTrace_append hprefix tailTrace_4087144
  have hstable : (prefixWord ++ tailWord_4087144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087144).length < 2 ^ (prefixWord ++ tailWord_4087144).sum := by decide
  have hdescent : baseEnd_4087144 < baseStart_4087144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087303 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 6]
def baseStart_4087303 : Nat := 118140960795 + 4087303 * 2 ^ 59
def prefixEnd_4087303 : Nat := 4983230072969 + 3 ^ 40 * 4087303 * 2
def baseEnd_4087303 : Nat := 466389115458650475981187

theorem tailTrace_4087303 : CollatzResearch.WordTrace tailWord_4087303 prefixEnd_4087303 466389115458650475981187 := by
  unfold tailWord_4087303
  simp only [CollatzResearch.WordTrace]
  refine ⟨149076187511406761622450563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99384125007604507748300375 149076187511406761622450563)
  ·
    refine ⟨223614281267110142433675845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149076187511406761622450563 223614281267110142433675845)
    ·
      refine ⟨41927677737583151706314221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223614281267110142433675845 41927677737583151706314221)
      ·
        refine ⟨15722879151593681889867833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41927677737583151706314221 15722879151593681889867833)
        ·
          refine ⟨11792159363695261417400875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15722879151593681889867833 11792159363695261417400875)
          ·
            refine ⟨17688239045542892126101313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11792159363695261417400875 17688239045542892126101313)
            ·
              refine ⟨13266179284157169094575985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17688239045542892126101313 13266179284157169094575985)
              ·
                refine ⟨9949634463117876820931989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13266179284157169094575985 9949634463117876820931989)
                ·
                  refine ⟨466389115458650475981187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9949634463117876820931989 466389115458650475981187)
                  ·
                    rfl

theorem cell22_4087303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 6].length) (baseStart_4087303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087303 prefixEnd_4087303 := by exact prefixLift 4087303
  have htrace : WordTrace (prefixWord ++ tailWord_4087303) baseStart_4087303 baseEnd_4087303 := by
    simpa [prefixWord, tailWord_4087303, baseEnd_4087303] using wordTrace_append hprefix tailTrace_4087303
  have hstable : (prefixWord ++ tailWord_4087303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087303).length < 2 ^ (prefixWord ++ tailWord_4087303).sum := by decide
  have hdescent : baseEnd_4087303 < baseStart_4087303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087352 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 2, 3]
def baseStart_4087352 : Nat := 118140960795 + 4087352 * 2 ^ 59
def prefixEnd_4087352 : Nat := 4983230072969 + 3 ^ 40 * 4087352 * 2
def baseEnd_4087352 : Nat := 1399184120077331633468411

theorem tailTrace_4087352 : CollatzResearch.WordTrace tailWord_4087352 prefixEnd_4087352 1399184120077331633468411 := by
  unfold tailWord_4087352
  simp only [CollatzResearch.WordTrace]
  refine ⟨74538987344114621495492155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99385316458819495327322873 74538987344114621495492155)
  ·
    refine ⟨111808481016171932243238233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74538987344114621495492155 111808481016171932243238233)
    ·
      refine ⟨83856360762128949182428675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111808481016171932243238233 83856360762128949182428675)
      ·
        refine ⟨125784541143193423773643013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83856360762128949182428675 125784541143193423773643013)
        ·
          refine ⟨23584601464348766957558065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125784541143193423773643013 23584601464348766957558065)
          ·
            refine ⟨17688451098261575218168549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23584601464348766957558065 17688451098261575218168549)
            ·
              refine ⟨3316584580924045353406603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17688451098261575218168549 3316584580924045353406603)
              ·
                refine ⟨4974876871386068030109905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316584580924045353406603 4974876871386068030109905)
                ·
                  refine ⟨3731157653539551022582429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4974876871386068030109905 3731157653539551022582429)
                  ·
                    refine ⟨1399184120077331633468411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731157653539551022582429 1399184120077331633468411)
                    ·
                      rfl

theorem cell22_4087352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_4087352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087352 prefixEnd_4087352 := by exact prefixLift 4087352
  have htrace : WordTrace (prefixWord ++ tailWord_4087352) baseStart_4087352 baseEnd_4087352 := by
    simpa [prefixWord, tailWord_4087352, baseEnd_4087352] using wordTrace_append hprefix tailTrace_4087352
  have hstable : (prefixWord ++ tailWord_4087352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087352).length < 2 ^ (prefixWord ++ tailWord_4087352).sum := by decide
  have hdescent : baseEnd_4087352 < baseStart_4087352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087382 : List Nat := [5, 2, 2, 2, 1, 10]
def baseStart_4087382 : Nat := 118140960795 + 4087382 * 2 ^ 59
def prefixEnd_4087382 : Nat := 4983230072969 + 3 ^ 40 * 4087382 * 2
def baseEnd_4087382 : Nat := 17274004810992858706399

theorem tailTrace_4087382 : CollatzResearch.WordTrace tailWord_4087382 prefixEnd_4087382 17274004810992858706399 := by
  unfold tailWord_4087382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9317441804882534882161025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99386045918747038743050933 9317441804882534882161025)
  ·
    refine ⟨6988081353661901161620769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9317441804882534882161025 6988081353661901161620769)
    ·
      refine ⟨5241061015246425871215577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6988081353661901161620769 5241061015246425871215577)
      ·
        refine ⟨3930795761434819403411683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5241061015246425871215577 3930795761434819403411683)
        ·
          refine ⟨5896193642152229105117525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930795761434819403411683 5896193642152229105117525)
          ·
            refine ⟨17274004810992858706399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5896193642152229105117525 17274004810992858706399)
            ·
              rfl

theorem cell22_4087382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 10].length) (baseStart_4087382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087382 prefixEnd_4087382 := by exact prefixLift 4087382
  have htrace : WordTrace (prefixWord ++ tailWord_4087382) baseStart_4087382 baseEnd_4087382 := by
    simpa [prefixWord, tailWord_4087382, baseEnd_4087382] using wordTrace_append hprefix tailTrace_4087382
  have hstable : (prefixWord ++ tailWord_4087382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087382).length < 2 ^ (prefixWord ++ tailWord_4087382).sum := by decide
  have hdescent : baseEnd_4087382 < baseStart_4087382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087408 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 1, 7]
def baseStart_4087408 : Nat := 118140960795 + 4087408 * 2 ^ 59
def prefixEnd_4087408 : Nat := 4983230072969 + 3 ^ 40 * 4087408 * 2
def baseEnd_4087408 : Nat := 1399203290021766154068239

theorem tailTrace_4087408 : CollatzResearch.WordTrace tailWord_4087408 prefixEnd_4087408 1399203290021766154068239 := by
  unfold tailWord_4087408
  simp only [CollatzResearch.WordTrace]
  refine ⟨74540008588013182277511439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99386678117350909703348585 74540008588013182277511439)
  ·
    refine ⟨111810012882019773416267159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74540008588013182277511439 111810012882019773416267159)
    ·
      refine ⟨167715019323029660124400739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111810012882019773416267159 167715019323029660124400739)
      ·
        refine ⟨251572528984544490186601109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167715019323029660124400739 251572528984544490186601109)
        ·
          refine ⟨11792462296150522977496927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251572528984544490186601109 11792462296150522977496927)
          ·
            refine ⟨17688693444225784466245391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11792462296150522977496927 17688693444225784466245391)
            ·
              refine ⟨26533040166338676699368087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17688693444225784466245391 26533040166338676699368087)
              ·
                refine ⟨39799560249508015049052131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26533040166338676699368087 39799560249508015049052131)
                ·
                  refine ⟨59699340374262022573578197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39799560249508015049052131 59699340374262022573578197)
                  ·
                    refine ⟨1399203290021766154068239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59699340374262022573578197 1399203290021766154068239)
                    ·
                      rfl

theorem cell22_4087408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_4087408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087408 prefixEnd_4087408 := by exact prefixLift 4087408
  have htrace : WordTrace (prefixWord ++ tailWord_4087408) baseStart_4087408 baseEnd_4087408 := by
    simpa [prefixWord, tailWord_4087408, baseEnd_4087408] using wordTrace_append hprefix tailTrace_4087408
  have hstable : (prefixWord ++ tailWord_4087408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087408).length < 2 ^ (prefixWord ++ tailWord_4087408).sum := by decide
  have hdescent : baseEnd_4087408 < baseStart_4087408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087410 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_4087410 : Nat := 118140960795 + 4087410 * 2 ^ 59
def prefixEnd_4087410 : Nat := 4983230072969 + 3 ^ 40 * 4087410 * 2
def baseEnd_4087410 : Nat := 466401324887546271839411

theorem tailTrace_4087410 : CollatzResearch.WordTrace tailWord_4087410 prefixEnd_4087410 466401324887546271839411 := by
  unfold tailWord_4087410
  simp only [CollatzResearch.WordTrace]
  refine ⟨37270022530504779724148921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99386726748012745931063789 37270022530504779724148921)
  ·
    refine ⟨27952516897878584793111691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37270022530504779724148921 27952516897878584793111691)
    ·
      refine ⟨41928775346817877189667537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27952516897878584793111691 41928775346817877189667537)
      ·
        refine ⟨31446581510113407892250653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41928775346817877189667537 31446581510113407892250653)
        ·
          refine ⟨11792468066292527959593995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31446581510113407892250653 11792468066292527959593995)
          ·
            refine ⟨17688702099438791939390993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11792468066292527959593995 17688702099438791939390993)
            ·
              refine ⟨13266526574579093954543245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17688702099438791939390993 13266526574579093954543245)
              ·
                refine ⟨4974947465467160232953717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13266526574579093954543245 4974947465467160232953717)
                ·
                  refine ⟨466401324887546271839411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974947465467160232953717 466401324887546271839411)
                  ·
                    rfl

theorem cell22_4087410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_4087410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087410 prefixEnd_4087410 := by exact prefixLift 4087410
  have htrace : WordTrace (prefixWord ++ tailWord_4087410) baseStart_4087410 baseEnd_4087410 := by
    simpa [prefixWord, tailWord_4087410, baseEnd_4087410] using wordTrace_append hprefix tailTrace_4087410
  have hstable : (prefixWord ++ tailWord_4087410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087410).length < 2 ^ (prefixWord ++ tailWord_4087410).sum := by decide
  have hdescent : baseEnd_4087410 < baseStart_4087410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087444 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 5]
def baseStart_4087444 : Nat := 118140960795 + 4087444 * 2 ^ 59
def prefixEnd_4087444 : Nat := 4983230072969 + 3 ^ 40 * 4087444 * 2
def baseEnd_4087444 : Nat := 466405204519158020056043

theorem tailTrace_4087444 : CollatzResearch.WordTrace tailWord_4087444 prefixEnd_4087444 466405204519158020056043 := by
  unfold tailWord_4087444
  simp only [CollatzResearch.WordTrace]
  refine ⟨74540665101947971351666693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99387553469263961802222257 74540665101947971351666693)
  ·
    refine ⟨13976374706615244628437505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74540665101947971351666693 13976374706615244628437505)
    ·
      refine ⟨10482281029961433471328129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13976374706615244628437505 10482281029961433471328129)
      ·
        refine ⟨7861710772471075103496097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10482281029961433471328129 7861710772471075103496097)
        ·
          refine ⟨5896283079353306327622073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7861710772471075103496097 5896283079353306327622073)
          ·
            refine ⟨4422212309514979745716555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5896283079353306327622073 4422212309514979745716555)
            ·
              refine ⟨6633318464272469618574833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4422212309514979745716555 6633318464272469618574833)
              ·
                refine ⟨4974988848204352213931125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6633318464272469618574833 4974988848204352213931125)
                ·
                  refine ⟨466405204519158020056043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974988848204352213931125 466405204519158020056043)
                  ·
                    rfl

theorem cell22_4087444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_4087444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087444 prefixEnd_4087444 := by exact prefixLift 4087444
  have htrace : WordTrace (prefixWord ++ tailWord_4087444) baseStart_4087444 baseEnd_4087444 := by
    simpa [prefixWord, tailWord_4087444, baseEnd_4087444] using wordTrace_append hprefix tailTrace_4087444
  have hstable : (prefixWord ++ tailWord_4087444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087444).length < 2 ^ (prefixWord ++ tailWord_4087444).sum := by decide
  have hdescent : baseEnd_4087444 < baseStart_4087444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087485 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_4087485 : Nat := 118140960795 + 4087485 * 2 ^ 59
def prefixEnd_4087485 : Nat := 4983230072969 + 3 ^ 40 * 4087485 * 2
def baseEnd_4087485 : Nat := 1399229648695363619893003

theorem tailTrace_4087485 : CollatzResearch.WordTrace tailWord_4087485 prefixEnd_4087485 1399229648695363619893003 := by
  unfold tailWord_4087485
  simp only [CollatzResearch.WordTrace]
  refine ⟨149082825596747406705575909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99388550397831604470383939 149082825596747406705575909)
  ·
    refine ⟨27953029799390138757295483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149082825596747406705575909 27953029799390138757295483)
    ·
      refine ⟨41929544699085208135943225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27953029799390138757295483 41929544699085208135943225)
      ·
        refine ⟨31447158524313906101957419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41929544699085208135943225 31447158524313906101957419)
        ·
          refine ⟨47170737786470859152936129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31447158524313906101957419 47170737786470859152936129)
          ·
            refine ⟨35378053339853144364702097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47170737786470859152936129 35378053339853144364702097)
            ·
              refine ⟨26533540004889858273526573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35378053339853144364702097 26533540004889858273526573)
              ·
                refine ⟨9950077501833696852572465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26533540004889858273526573 9950077501833696852572465)
                ·
                  refine ⟨7462558126375272639429349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9950077501833696852572465 7462558126375272639429349)
                  ·
                    refine ⟨1399229648695363619893003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7462558126375272639429349 1399229648695363619893003)
                    ·
                      rfl

theorem cell22_4087485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_4087485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087485 prefixEnd_4087485 := by exact prefixLift 4087485
  have htrace : WordTrace (prefixWord ++ tailWord_4087485) baseStart_4087485 baseEnd_4087485 := by
    simpa [prefixWord, tailWord_4087485, baseEnd_4087485] using wordTrace_append hprefix tailTrace_4087485
  have hstable : (prefixWord ++ tailWord_4087485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087485).length < 2 ^ (prefixWord ++ tailWord_4087485).sum := by decide
  have hdescent : baseEnd_4087485 < baseStart_4087485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087521 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 2, 3]
def baseStart_4087521 : Nat := 118140960795 + 4087521 * 2 ^ 59
def prefixEnd_4087521 : Nat := 4983230072969 + 3 ^ 40 * 4087521 * 2
def baseEnd_4087521 : Nat := 1399241972231071525992893

theorem tailTrace_4087521 : CollatzResearch.WordTrace tailWord_4087521 prefixEnd_4087521 1399241972231071525992893 := by
  unfold tailWord_4087521
  simp only [CollatzResearch.WordTrace]
  refine ⟨149084138624616984853886417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99389425749744656569257611 149084138624616984853886417)
  ·
    refine ⟨111813103968462738640414813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149084138624616984853886417 111813103968462738640414813)
    ·
      refine ⟨41929913988173526990155555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111813103968462738640414813 41929913988173526990155555)
      ·
        refine ⟨62894870982260290485233333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41929913988173526990155555 62894870982260290485233333)
        ·
          refine ⟨5896394154586902232990625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62894870982260290485233333 5896394154586902232990625)
          ·
            refine ⟨4422295615940176674742969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5896394154586902232990625 4422295615940176674742969)
            ·
              refine ⟨3316721711955132506057227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4422295615940176674742969 3316721711955132506057227)
              ·
                refine ⟨4975082567932698759085841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316721711955132506057227 4975082567932698759085841)
                ·
                  refine ⟨3731311925949524069314381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4975082567932698759085841 3731311925949524069314381)
                  ·
                    refine ⟨1399241972231071525992893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731311925949524069314381 1399241972231071525992893)
                    ·
                      rfl

theorem cell22_4087521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_4087521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087521 prefixEnd_4087521 := by exact prefixLift 4087521
  have htrace : WordTrace (prefixWord ++ tailWord_4087521) baseStart_4087521 baseEnd_4087521 := by
    simpa [prefixWord, tailWord_4087521, baseEnd_4087521] using wordTrace_append hprefix tailTrace_4087521
  have hstable : (prefixWord ++ tailWord_4087521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087521).length < 2 ^ (prefixWord ++ tailWord_4087521).sum := by decide
  have hdescent : baseEnd_4087521 < baseStart_4087521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087560 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_4087560 : Nat := 118140960795 + 4087560 * 2 ^ 59
def prefixEnd_4087560 : Nat := 4983230072969 + 3 ^ 40 * 4087560 * 2
def baseEnd_4087560 : Nat := 1399255322728088424267773

theorem tailTrace_4087560 : CollatzResearch.WordTrace tailWord_4087560 prefixEnd_4087560 1399255322728088424267773 := by
  unfold tailWord_4087560
  simp only [CollatzResearch.WordTrace]
  refine ⟨74542780535737847257278067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99390374047650463009704089 74542780535737847257278067)
  ·
    refine ⟨111814170803606770885917101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74542780535737847257278067 111814170803606770885917101)
    ·
      refine ⟨41930314051352539082218913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111814170803606770885917101 41930314051352539082218913)
      ·
        refine ⟨31447735538514404311664185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41930314051352539082218913 31447735538514404311664185)
        ·
          refine ⟨23585801653885803233748139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31447735538514404311664185 23585801653885803233748139)
          ·
            refine ⟨35378702480828704850622209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23585801653885803233748139 35378702480828704850622209)
            ·
              refine ⟨26534026860621528637966657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35378702480828704850622209 26534026860621528637966657)
              ·
                refine ⟨19900520145466146478474993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26534026860621528637966657 19900520145466146478474993)
                ·
                  refine ⟨14925390109099609858856245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19900520145466146478474993 14925390109099609858856245)
                  ·
                    refine ⟨1399255322728088424267773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14925390109099609858856245 1399255322728088424267773)
                    ·
                      rfl

theorem cell22_4087560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_4087560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087560 prefixEnd_4087560 := by exact prefixLift 4087560
  have htrace : WordTrace (prefixWord ++ tailWord_4087560) baseStart_4087560 baseEnd_4087560 := by
    simpa [prefixWord, tailWord_4087560, baseEnd_4087560] using wordTrace_append hprefix tailTrace_4087560
  have hstable : (prefixWord ++ tailWord_4087560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087560).length < 2 ^ (prefixWord ++ tailWord_4087560).sum := by decide
  have hdescent : baseEnd_4087560 < baseStart_4087560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087562 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_4087562 : Nat := 118140960795 + 4087562 * 2 ^ 59
def prefixEnd_4087562 : Nat := 4983230072969 + 3 ^ 40 * 4087562 * 2
def baseEnd_4087562 : Nat := 466418669122987028572589

theorem tailTrace_4087562 : CollatzResearch.WordTrace tailWord_4087562 prefixEnd_4087562 466418669122987028572589 := by
  unfold tailWord_4087562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37271408504367112214032235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99390422678312299237419293 37271408504367112214032235)
  ·
    refine ⟨55907112756550668321048353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37271408504367112214032235 55907112756550668321048353)
    ·
      refine ⟨41930334567413001240786265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55907112756550668321048353 41930334567413001240786265)
      ·
        refine ⟨31447750925559750930589699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41930334567413001240786265 31447750925559750930589699)
        ·
          refine ⟨47171626388339626395884549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31447750925559750930589699 47171626388339626395884549)
          ·
            refine ⟨8844679947813679949228353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47171626388339626395884549 8844679947813679949228353)
            ·
              refine ⟨6633509960860259961921265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8844679947813679949228353 6633509960860259961921265)
              ·
                refine ⟨4975132470645194971440949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6633509960860259961921265 4975132470645194971440949)
                ·
                  refine ⟨466418669122987028572589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4975132470645194971440949 466418669122987028572589)
                  ·
                    rfl

theorem cell22_4087562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_4087562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087562 prefixEnd_4087562 := by exact prefixLift 4087562
  have htrace : WordTrace (prefixWord ++ tailWord_4087562) baseStart_4087562 baseEnd_4087562 := by
    simpa [prefixWord, tailWord_4087562, baseEnd_4087562] using wordTrace_append hprefix tailTrace_4087562
  have hstable : (prefixWord ++ tailWord_4087562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087562).length < 2 ^ (prefixWord ++ tailWord_4087562).sum := by decide
  have hdescent : baseEnd_4087562 < baseStart_4087562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087566 : List Nat := [4, 1, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_4087566 : Nat := 118140960795 + 4087566 * 2 ^ 59
def prefixEnd_4087566 : Nat := 4983230072969 + 3 ^ 40 * 4087566 * 2
def baseEnd_4087566 : Nat := 1399257376650706408617755

theorem tailTrace_4087566 : CollatzResearch.WordTrace tailWord_4087566 prefixEnd_4087566 1399257376650706408617755 := by
  unfold tailWord_4087566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18635722488681744692409319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99390519939635971692849701 18635722488681744692409319)
  ·
    refine ⟨27953583733022617038613979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18635722488681744692409319 27953583733022617038613979)
    ·
      refine ⟨41930375599533925557920969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27953583733022617038613979 41930375599533925557920969)
      ·
        refine ⟨31447781699650444168440727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41930375599533925557920969 31447781699650444168440727)
        ·
          refine ⟨47171672549475666252661091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31447781699650444168440727 47171672549475666252661091)
          ·
            refine ⟨70757508824213499378991637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47171672549475666252661091 70757508824213499378991637)
            ·
              refine ⟨3316758226135007783390233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70757508824213499378991637 3316758226135007783390233)
              ·
                refine ⟨2487568669601255837542675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3316758226135007783390233 2487568669601255837542675)
                ·
                  refine ⟨3731353004401883756314013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487568669601255837542675 3731353004401883756314013)
                  ·
                    refine ⟨1399257376650706408617755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731353004401883756314013 1399257376650706408617755)
                    ·
                      rfl

theorem cell22_4087566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_4087566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087566 prefixEnd_4087566 := by exact prefixLift 4087566
  have htrace : WordTrace (prefixWord ++ tailWord_4087566) baseStart_4087566 baseEnd_4087566 := by
    simpa [prefixWord, tailWord_4087566, baseEnd_4087566] using wordTrace_append hprefix tailTrace_4087566
  have hstable : (prefixWord ++ tailWord_4087566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087566).length < 2 ^ (prefixWord ++ tailWord_4087566).sum := by decide
  have hdescent : baseEnd_4087566 < baseStart_4087566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087592 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4087592 : Nat := 118140960795 + 4087592 * 2 ^ 59
def prefixEnd_4087592 : Nat := 4983230072969 + 3 ^ 40 * 4087592 * 2
def baseEnd_4087592 : Nat := 1399266276982051007467675

theorem tailTrace_4087592 : CollatzResearch.WordTrace tailWord_4087592 prefixEnd_4087592 1399266276982051007467675 := by
  unfold tailWord_4087592
  simp only [CollatzResearch.WordTrace]
  refine ⟨74543364103679881989860515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99391152138239842653147353 74543364103679881989860515)
  ·
    refine ⟨111815046155519822984790773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74543364103679881989860515 111815046155519822984790773)
    ·
      refine ⟨10482660577079983404824135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111815046155519822984790773 10482660577079983404824135)
      ·
        refine ⟨15723990865619975107236203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10482660577079983404824135 15723990865619975107236203)
        ·
          refine ⟨23585986298429962660854305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15723990865619975107236203 23585986298429962660854305)
          ·
            refine ⟨17689489723822471995640729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23585986298429962660854305 17689489723822471995640729)
            ·
              refine ⟨13267117292866853996730547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17689489723822471995640729 13267117292866853996730547)
              ·
                refine ⟨19900675939300280995095821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13267117292866853996730547 19900675939300280995095821)
                ·
                  refine ⟨7462753477237605373160933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19900675939300280995095821 7462753477237605373160933)
                  ·
                    refine ⟨1399266276982051007467675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7462753477237605373160933 1399266276982051007467675)
                    ·
                      rfl

theorem cell22_4087592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4087592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087592 prefixEnd_4087592 := by exact prefixLift 4087592
  have htrace : WordTrace (prefixWord ++ tailWord_4087592) baseStart_4087592 baseEnd_4087592 := by
    simpa [prefixWord, tailWord_4087592, baseEnd_4087592] using wordTrace_append hprefix tailTrace_4087592
  have hstable : (prefixWord ++ tailWord_4087592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087592).length < 2 ^ (prefixWord ++ tailWord_4087592).sum := by decide
  have hdescent : baseEnd_4087592 < baseStart_4087592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087639 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 1, 5]
def baseStart_4087639 : Nat := 118140960795 + 4087639 * 2 ^ 59
def prefixEnd_4087639 : Nat := 4983230072969 + 3 ^ 40 * 4087639 * 2
def baseEnd_4087639 : Nat := 1399282366042558551542531

theorem tailTrace_4087639 : CollatzResearch.WordTrace tailWord_4087639 prefixEnd_4087639 1399282366042558551542531 := by
  unfold tailWord_4087639
  simp only [CollatzResearch.WordTrace]
  refine ⟨149088442438189491006681971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99392294958792994004454647 149088442438189491006681971)
  ·
    refine ⟨223632663657284236510022957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149088442438189491006681971 223632663657284236510022957)
    ·
      refine ⟨83862248871481588691258609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223632663657284236510022957 83862248871481588691258609)
      ·
        refine ⟨62896686653611191518443957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83862248871481588691258609 62896686653611191518443957)
        ·
          refine ⟨5896564373776049204854121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62896686653611191518443957 5896564373776049204854121)
          ·
            refine ⟨4422423280332036903640591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5896564373776049204854121 4422423280332036903640591)
            ·
              refine ⟨6633634920498055355460887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4422423280332036903640591 6633634920498055355460887)
              ·
                refine ⟨9950452380747083033191331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6633634920498055355460887 9950452380747083033191331)
                ·
                  refine ⟨14925678571120624549786997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9950452380747083033191331 14925678571120624549786997)
                  ·
                    refine ⟨1399282366042558551542531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14925678571120624549786997 1399282366042558551542531)
                    ·
                      rfl

theorem cell22_4087639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_4087639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087639 prefixEnd_4087639 := by exact prefixLift 4087639
  have htrace : WordTrace (prefixWord ++ tailWord_4087639) baseStart_4087639 baseEnd_4087639 := by
    simpa [prefixWord, tailWord_4087639, baseEnd_4087639] using wordTrace_append hprefix tailTrace_4087639
  have hstable : (prefixWord ++ tailWord_4087639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087639).length < 2 ^ (prefixWord ++ tailWord_4087639).sum := by decide
  have hdescent : baseEnd_4087639 < baseStart_4087639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087652 : List Nat := [2, 3, 1, 1, 5, 1, 1, 8]
def baseStart_4087652 : Nat := 118140960795 + 4087652 * 2 ^ 59
def prefixEnd_4087652 : Nat := 4983230072969 + 3 ^ 40 * 4087652 * 2
def baseEnd_4087652 : Nat := 155476312912025650107499

theorem tailTrace_4087652 : CollatzResearch.WordTrace tailWord_4087652 prefixEnd_4087652 155476312912025650107499 := by
  unfold tailWord_4087652
  simp only [CollatzResearch.WordTrace]
  refine ⟨74544458293571197113452605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99392611058094929484603473 74544458293571197113452605)
  ·
    refine ⟨27954171860089198917544727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74544458293571197113452605 27954171860089198917544727)
    ·
      refine ⟨41931257790133798376317091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27954171860089198917544727 41931257790133798376317091)
      ·
        refine ⟨62896886685200697564475637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41931257790133798376317091 62896886685200697564475637)
        ·
          refine ⟨5896583126737565396669591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62896886685200697564475637 5896583126737565396669591)
          ·
            refine ⟨8844874690106348095004387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896583126737565396669591 8844874690106348095004387)
            ·
              refine ⟨13267312035159522142506581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8844874690106348095004387 13267312035159522142506581)
              ·
                refine ⟨155476312912025650107499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13267312035159522142506581 155476312912025650107499)
                ·
                  rfl

theorem cell22_4087652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 8].length) (baseStart_4087652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087652 prefixEnd_4087652 := by exact prefixLift 4087652
  have htrace : WordTrace (prefixWord ++ tailWord_4087652) baseStart_4087652 baseEnd_4087652 := by
    simpa [prefixWord, tailWord_4087652, baseEnd_4087652] using wordTrace_append hprefix tailTrace_4087652
  have hstable : (prefixWord ++ tailWord_4087652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087652).length < 2 ^ (prefixWord ++ tailWord_4087652).sum := by decide
  have hdescent : baseEnd_4087652 < baseStart_4087652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087658 : List Nat := [3, 1, 3, 4, 1, 2, 1, 3, 4]
def baseStart_4087658 : Nat := 118140960795 + 4087658 * 2 ^ 59
def prefixEnd_4087658 : Nat := 4983230072969 + 3 ^ 40 * 4087658 * 2
def baseEnd_4087658 : Nat := 466429623376949611772491

theorem tailTrace_4087658 : CollatzResearch.WordTrace tailWord_4087658 prefixEnd_4087658 466429623376949611772491 := by
  unfold tailWord_4087658
  simp only [CollatzResearch.WordTrace]
  refine ⟨37272283856280164312905907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99392756950080438167749085 37272283856280164312905907)
  ·
    refine ⟨55908425784420246469358861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37272283856280164312905907 55908425784420246469358861)
    ·
      refine ⟨20965659669157592426009573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55908425784420246469358861 20965659669157592426009573)
      ·
        refine ⟨3931061187967048579876795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20965659669157592426009573 3931061187967048579876795)
        ·
          refine ⟨5896591781950572869815193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931061187967048579876795 5896591781950572869815193)
          ·
            refine ⟨4422443836462929652361395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5896591781950572869815193 4422443836462929652361395)
            ·
              refine ⟨6633665754694394478542093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4422443836462929652361395 6633665754694394478542093)
              ·
                refine ⟨2487624658010397929453285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6633665754694394478542093 2487624658010397929453285)
                ·
                  refine ⟨466429623376949611772491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2487624658010397929453285 466429623376949611772491)
                  ·
                    rfl

theorem cell22_4087658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_4087658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087658 prefixEnd_4087658 := by exact prefixLift 4087658
  have htrace : WordTrace (prefixWord ++ tailWord_4087658) baseStart_4087658 baseEnd_4087658 := by
    simpa [prefixWord, tailWord_4087658, baseEnd_4087658] using wordTrace_append hprefix tailTrace_4087658
  have hstable : (prefixWord ++ tailWord_4087658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087658).length < 2 ^ (prefixWord ++ tailWord_4087658).sum := by decide
  have hdescent : baseEnd_4087658 < baseStart_4087658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087680 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 7]
def baseStart_4087680 : Nat := 118140960795 + 4087680 * 2 ^ 59
def prefixEnd_4087680 : Nat := 4983230072969 + 3 ^ 40 * 4087680 * 2
def baseEnd_4087680 : Nat := 466432133726816037089135

theorem tailTrace_4087680 : CollatzResearch.WordTrace tailWord_4087680 prefixEnd_4087680 466432133726816037089135 := by
  unfold tailWord_4087680
  simp only [CollatzResearch.WordTrace]
  refine ⟨74544968915520477504462247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99393291887360636672616329 74544968915520477504462247)
  ·
    refine ⟨111817453373280716256693371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74544968915520477504462247 111817453373280716256693371)
    ·
      refine ⟨167726180059921074385040057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111817453373280716256693371 167726180059921074385040057)
      ·
        refine ⟨125794635044940805788780043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167726180059921074385040057 125794635044940805788780043)
        ·
          refine ⟨188691952567411208683170065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125794635044940805788780043 188691952567411208683170065)
          ·
            refine ⟨141518964425558406512377549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188691952567411208683170065 141518964425558406512377549)
            ·
              refine ⟨53069611659584402442141581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141518964425558406512377549 53069611659584402442141581)
              ·
                refine ⟨19901104372344150915803093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53069611659584402442141581 19901104372344150915803093)
                ·
                  refine ⟨466432133726816037089135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19901104372344150915803093 466432133726816037089135)
                  ·
                    rfl

theorem cell22_4087680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_4087680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087680 prefixEnd_4087680 := by exact prefixLift 4087680
  have htrace : WordTrace (prefixWord ++ tailWord_4087680) baseStart_4087680 baseEnd_4087680 := by
    simpa [prefixWord, tailWord_4087680, baseEnd_4087680] using wordTrace_append hprefix tailTrace_4087680
  have hstable : (prefixWord ++ tailWord_4087680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087680).length < 2 ^ (prefixWord ++ tailWord_4087680).sum := by decide
  have hdescent : baseEnd_4087680 < baseStart_4087680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087684 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_4087684 : Nat := 118140960795 + 4087684 * 2 ^ 59
def prefixEnd_4087684 : Nat := 4983230072969 + 3 ^ 40 * 4087684 * 2
def baseEnd_4087684 : Nat := 1399297770462193434167393

theorem tailTrace_4087684 : CollatzResearch.WordTrace tailWord_4087684 prefixEnd_4087684 1399297770462193434167393 := by
  unfold tailWord_4087684
  simp only [CollatzResearch.WordTrace]
  refine ⟨74545041861513231846035053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99393389148684309128046737 74545041861513231846035053)
  ·
    refine ⟨27954390698067461942263145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74545041861513231846035053 27954390698067461942263145)
    ·
      refine ⟨20965793023550596456697359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27954390698067461942263145 20965793023550596456697359)
      ·
        refine ⟨31448689535325894685046039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20965793023550596456697359 31448689535325894685046039)
        ·
          refine ⟨47173034302988842027569059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31448689535325894685046039 47173034302988842027569059)
          ·
            refine ⟨70759551454483263041353589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47173034302988842027569059 70759551454483263041353589)
            ·
              refine ⟨6633707948857805910126899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70759551454483263041353589 6633707948857805910126899)
              ·
                refine ⟨9950561923286708865190349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6633707948857805910126899 9950561923286708865190349)
                ·
                  refine ⟨3731460721232515824446381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9950561923286708865190349 3731460721232515824446381)
                  ·
                    refine ⟨1399297770462193434167393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731460721232515824446381 1399297770462193434167393)
                    ·
                      rfl

theorem cell22_4087684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_4087684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087684 prefixEnd_4087684 := by exact prefixLift 4087684
  have htrace : WordTrace (prefixWord ++ tailWord_4087684) baseStart_4087684 baseEnd_4087684 := by
    simpa [prefixWord, tailWord_4087684, baseEnd_4087684] using wordTrace_append hprefix tailTrace_4087684
  have hstable : (prefixWord ++ tailWord_4087684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087684).length < 2 ^ (prefixWord ++ tailWord_4087684).sum := by decide
  have hdescent : baseEnd_4087684 < baseStart_4087684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087690 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 2, 3]
def baseStart_4087690 : Nat := 118140960795 + 4087690 * 2 ^ 59
def prefixEnd_4087690 : Nat := 4983230072969 + 3 ^ 40 * 4087690 * 2
def baseEnd_4087690 : Nat := 1399299824384811418517375

theorem tailTrace_4087690 : CollatzResearch.WordTrace tailWord_4087690 prefixEnd_4087690 1399299824384811418517375 := by
  unfold tailWord_4087690
  simp only [CollatzResearch.WordTrace]
  refine ⟨37272575640251181679197131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99393535040669817811192349 37272575640251181679197131)
  ·
    refine ⟨55908863460376772518795697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37272575640251181679197131 55908863460376772518795697)
    ·
      refine ⟨41931647595282579389096773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55908863460376772518795697 41931647595282579389096773)
      ·
        refine ⟨7862183924115483635455645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41931647595282579389096773 7862183924115483635455645)
        ·
          refine ⟨2948318971543306363295867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7862183924115483635455645 2948318971543306363295867)
          ·
            refine ⟨4422478457314959544943801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948318971543306363295867 4422478457314959544943801)
            ·
              refine ⟨3316858842986219658707851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4422478457314959544943801 3316858842986219658707851)
              ·
                refine ⟨4975288264479329488061777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316858842986219658707851 4975288264479329488061777)
                ·
                  refine ⟨3731466198359497116046333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4975288264479329488061777 3731466198359497116046333)
                  ·
                    refine ⟨1399299824384811418517375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731466198359497116046333 1399299824384811418517375)
                    ·
                      rfl

theorem cell22_4087690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_4087690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087690 prefixEnd_4087690 := by exact prefixLift 4087690
  have htrace : WordTrace (prefixWord ++ tailWord_4087690) baseStart_4087690 baseEnd_4087690 := by
    simpa [prefixWord, tailWord_4087690, baseEnd_4087690] using wordTrace_append hprefix tailTrace_4087690
  have hstable : (prefixWord ++ tailWord_4087690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087690).length < 2 ^ (prefixWord ++ tailWord_4087690).sum := by decide
  have hdescent : baseEnd_4087690 < baseStart_4087690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087695 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 8, 5]
def baseStart_4087695 : Nat := 118140960795 + 4087695 * 2 ^ 59
def prefixEnd_4087695 : Nat := 4983230072969 + 3 ^ 40 * 4087695 * 2
def baseEnd_4087695 : Nat := 1399301535986993072142359

theorem tailTrace_4087695 : CollatzResearch.WordTrace tailWord_4087695 prefixEnd_4087695 1399301535986993072142359 := by
  unfold tailWord_4087695
  simp only [CollatzResearch.WordTrace]
  refine ⟨149090484925986612570720539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99393656617324408380480359 149090484925986612570720539)
  ·
    refine ⟨223635727388979918856080809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149090484925986612570720539 223635727388979918856080809)
    ·
      refine ⟨167726795541734939142060607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223635727388979918856080809 167726795541734939142060607)
      ·
        refine ⟨251590193312602408713090911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167726795541734939142060607 251590193312602408713090911)
        ·
          refine ⟨377385289968903613069636367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251590193312602408713090911 377385289968903613069636367)
          ·
            refine ⟨566077934953355419604454551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377385289968903613069636367 566077934953355419604454551)
            ·
              refine ⟨849116902430033129406681827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566077934953355419604454551 849116902430033129406681827)
              ·
                refine ⟨1273675353645049694110022741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849116902430033129406681827 1273675353645049694110022741)
                ·
                  refine ⟨14925883050527926102851829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1273675353645049694110022741 14925883050527926102851829)
                  ·
                    refine ⟨1399301535986993072142359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14925883050527926102851829 1399301535986993072142359)
                    ·
                      rfl

theorem cell22_4087695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_4087695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087695 prefixEnd_4087695 := by exact prefixLift 4087695
  have htrace : WordTrace (prefixWord ++ tailWord_4087695) baseStart_4087695 baseEnd_4087695 := by
    simpa [prefixWord, tailWord_4087695, baseEnd_4087695] using wordTrace_append hprefix tailTrace_4087695
  have hstable : (prefixWord ++ tailWord_4087695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087695).length < 2 ^ (prefixWord ++ tailWord_4087695).sum := by decide
  have hdescent : baseEnd_4087695 < baseStart_4087695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087778 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4087778 : Nat := 118140960795 + 4087778 * 2 ^ 59
def prefixEnd_4087778 : Nat := 4983230072969 + 3 ^ 40 * 4087778 * 2
def baseEnd_4087778 : Nat := 1399329948583208522317105

theorem tailTrace_4087778 : CollatzResearch.WordTrace tailWord_4087778 prefixEnd_4087778 1399329948583208522317105 := by
  unfold tailWord_4087778
  simp only [CollatzResearch.WordTrace]
  refine ⟨37273378046171479436497997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99395674789790611830661325 37273378046171479436497997)
  ·
    refine ⟨13977516767314304788686749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37273378046171479436497997 13977516767314304788686749)
    ·
      refine ⟨5241568787742864295757531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13977516767314304788686749 5241568787742864295757531)
      ·
        refine ⟨7862353181614296443636297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5241568787742864295757531 7862353181614296443636297)
        ·
          refine ⟨5896764886210722332727223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7862353181614296443636297 5896764886210722332727223)
          ·
            refine ⟨8845147329316083499090835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896764886210722332727223 8845147329316083499090835)
            ·
              refine ⟨13267720993974125248636253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8845147329316083499090835 13267720993974125248636253)
              ·
                refine ⟨4975395372740296968238595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13267720993974125248636253 4975395372740296968238595)
                ·
                  refine ⟨7463093059110445452357893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4975395372740296968238595 7463093059110445452357893)
                  ·
                    refine ⟨1399329948583208522317105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7463093059110445452357893 1399329948583208522317105)
                    ·
                      rfl

theorem cell22_4087778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4087778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087778 prefixEnd_4087778 := by exact prefixLift 4087778
  have htrace : WordTrace (prefixWord ++ tailWord_4087778) baseStart_4087778 baseEnd_4087778 := by
    simpa [prefixWord, tailWord_4087778, baseEnd_4087778] using wordTrace_append hprefix tailTrace_4087778
  have hstable : (prefixWord ++ tailWord_4087778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087778).length < 2 ^ (prefixWord ++ tailWord_4087778).sum := by decide
  have hdescent : baseEnd_4087778 < baseStart_4087778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087819 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 3, 3]
def baseStart_4087819 : Nat := 118140960795 + 4087819 * 2 ^ 59
def prefixEnd_4087819 : Nat := 4983230072969 + 3 ^ 40 * 4087819 * 2
def baseEnd_4087819 : Nat := 1399343983721098082041979

theorem tailTrace_4087819 : CollatzResearch.WordTrace tailWord_4087819 prefixEnd_4087819 1399343983721098082041979 := by
  unfold tailWord_4087819
  simp only [CollatzResearch.WordTrace]
  refine ⟨149095007577537381748234511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99396671718358254498823007 149095007577537381748234511)
  ·
    refine ⟨223642511366306072622351767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149095007577537381748234511 223642511366306072622351767)
    ·
      refine ⟨335463767049459108933527651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223642511366306072622351767 335463767049459108933527651)
      ·
        refine ⟨503195650574188663400291477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335463767049459108933527651 503195650574188663400291477)
        ·
          refine ⟨23587296120665093596888663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 503195650574188663400291477 23587296120665093596888663)
          ·
            refine ⟨35380944180997640395332995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23587296120665093596888663 35380944180997640395332995)
            ·
              refine ⟨53071416271496460592999493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35380944180997640395332995 53071416271496460592999493)
              ·
                refine ⟨9950890550905586361187405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53071416271496460592999493 9950890550905586361187405)
                ·
                  refine ⟨3731583956589594885445277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9950890550905586361187405 3731583956589594885445277)
                  ·
                    refine ⟨1399343983721098082041979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731583956589594885445277 1399343983721098082041979)
                    ·
                      rfl

theorem cell22_4087819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 3].length) (baseStart_4087819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087819 prefixEnd_4087819 := by exact prefixLift 4087819
  have htrace : WordTrace (prefixWord ++ tailWord_4087819) baseStart_4087819 baseEnd_4087819 := by
    simpa [prefixWord, tailWord_4087819, baseEnd_4087819] using wordTrace_append hprefix tailTrace_4087819
  have hstable : (prefixWord ++ tailWord_4087819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087819).length < 2 ^ (prefixWord ++ tailWord_4087819).sum := by decide
  have hdescent : baseEnd_4087819 < baseStart_4087819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087832 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 9]
def baseStart_4087832 : Nat := 118140960795 + 4087832 * 2 ^ 59
def prefixEnd_4087832 : Nat := 4983230072969 + 3 ^ 40 * 4087832 * 2
def baseEnd_4087832 : Nat := 466449477962256793822313

theorem tailTrace_4087832 : CollatzResearch.WordTrace tailWord_4087832 prefixEnd_4087832 466449477962256793822313 := by
  unfold tailWord_4087832
  simp only [CollatzResearch.WordTrace]
  refine ⟨74547740863245142484228875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99396987817660189978971833 74547740863245142484228875)
  ·
    refine ⟨111821611294867713726343313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74547740863245142484228875 111821611294867713726343313)
    ·
      refine ⟨83866208471150785294757485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111821611294867713726343313 83866208471150785294757485)
      ·
        refine ⟨31449828176681544485534057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83866208471150785294757485 31449828176681544485534057)
        ·
          refine ⟨23587371132511158364150543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31449828176681544485534057 23587371132511158364150543)
          ·
            refine ⟨35381056698766737546225815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23587371132511158364150543 35381056698766737546225815)
            ·
              refine ⟨53071585048150106319338723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35381056698766737546225815 53071585048150106319338723)
              ·
                refine ⟨79607377572225159479008085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53071585048150106319338723 79607377572225159479008085)
                ·
                  refine ⟨466449477962256793822313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79607377572225159479008085 466449477962256793822313)
                  ·
                    rfl

theorem cell22_4087832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_4087832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087832 prefixEnd_4087832 := by exact prefixLift 4087832
  have htrace : WordTrace (prefixWord ++ tailWord_4087832) baseStart_4087832 baseEnd_4087832 := by
    simpa [prefixWord, tailWord_4087832, baseEnd_4087832] using wordTrace_append hprefix tailTrace_4087832
  have hstable : (prefixWord ++ tailWord_4087832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087832).length < 2 ^ (prefixWord ++ tailWord_4087832).sum := by decide
  have hdescent : baseEnd_4087832 < baseStart_4087832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087877 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 8]
def baseStart_4087877 : Nat := 118140960795 + 4087877 * 2 ^ 59
def prefixEnd_4087877 : Nat := 4983230072969 + 3 ^ 40 * 4087877 * 2
def baseEnd_4087877 : Nat := 466454612768801754697267

theorem tailTrace_4087877 : CollatzResearch.WordTrace tailWord_4087877 prefixEnd_4087877 466454612768801754697267 := by
  unfold tailWord_4087877
  simp only [CollatzResearch.WordTrace]
  refine ⟨149097123011327257653845885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99398082007551505102563923 149097123011327257653845885)
  ·
    refine ⟨55911421129247721620192207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149097123011327257653845885 55911421129247721620192207)
    ·
      refine ⟨83867131693871582430288311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55911421129247721620192207 83867131693871582430288311)
      ·
        refine ⟨125800697540807373645432467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83867131693871582430288311 125800697540807373645432467)
        ·
          refine ⟨188701046311211060468148701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125800697540807373645432467 188701046311211060468148701)
          ·
            refine ⟨70762892366704147675555763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188701046311211060468148701 70762892366704147675555763)
            ·
              refine ⟨106144338550056221513333645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70762892366704147675555763 106144338550056221513333645)
              ·
                refine ⟨39804126956271083067500117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106144338550056221513333645 39804126956271083067500117)
                ·
                  refine ⟨466454612768801754697267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39804126956271083067500117 466454612768801754697267)
                  ·
                    rfl

theorem cell22_4087877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_4087877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087877 prefixEnd_4087877 := by exact prefixLift 4087877
  have htrace : WordTrace (prefixWord ++ tailWord_4087877) baseStart_4087877 baseEnd_4087877 := by
    simpa [prefixWord, tailWord_4087877, baseEnd_4087877] using wordTrace_append hprefix tailTrace_4087877
  have hstable : (prefixWord ++ tailWord_4087877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087877).length < 2 ^ (prefixWord ++ tailWord_4087877).sum := by decide
  have hdescent : baseEnd_4087877 < baseStart_4087877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087879 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 3, 4]
def baseStart_4087879 : Nat := 118140960795 + 4087879 * 2 ^ 59
def prefixEnd_4087879 : Nat := 4983230072969 + 3 ^ 40 * 4087879 * 2
def baseEnd_4087879 : Nat := 1399364522947277925541795

theorem tailTrace_4087879 : CollatzResearch.WordTrace tailWord_4087879 prefixEnd_4087879 1399364522947277925541795 := by
  unfold tailWord_4087879
  simp only [CollatzResearch.WordTrace]
  refine ⟨149097195957320011995418691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99398130638213341330279127 149097195957320011995418691)
  ·
    refine ⟨223645793935980017993128037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149097195957320011995418691 223645793935980017993128037)
    ·
      refine ⟨41933586362996253373711507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223645793935980017993128037 41933586362996253373711507)
      ·
        refine ⟨62900379544494380060567261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41933586362996253373711507 62900379544494380060567261)
        ·
          refine ⟨23587642329185392522712723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62900379544494380060567261 23587642329185392522712723)
          ·
            refine ⟨35381463493778088784069085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23587642329185392522712723 35381463493778088784069085)
            ·
              refine ⟨13268048810166783294025907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35381463493778088784069085 13268048810166783294025907)
              ·
                refine ⟨19902073215250174941038861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13268048810166783294025907 19902073215250174941038861)
                ·
                  refine ⟨7463277455718815602889573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19902073215250174941038861 7463277455718815602889573)
                  ·
                    refine ⟨1399364522947277925541795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7463277455718815602889573 1399364522947277925541795)
                    ·
                      rfl

theorem cell22_4087879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_4087879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087879 prefixEnd_4087879 := by exact prefixLift 4087879
  have htrace : WordTrace (prefixWord ++ tailWord_4087879) baseStart_4087879 baseEnd_4087879 := by
    simpa [prefixWord, tailWord_4087879, baseEnd_4087879] using wordTrace_append hprefix tailTrace_4087879
  have hstable : (prefixWord ++ tailWord_4087879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087879).length < 2 ^ (prefixWord ++ tailWord_4087879).sum := by decide
  have hdescent : baseEnd_4087879 < baseStart_4087879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087911 : List Nat := [1, 1, 5, 1, 1, 2, 3, 4, 4]
def baseStart_4087911 : Nat := 118140960795 + 4087911 * 2 ^ 59
def prefixEnd_4087911 : Nat := 4983230072969 + 3 ^ 40 * 4087911 * 2
def baseEnd_4087911 : Nat := 466458492400413502913899

theorem tailTrace_4087911 : CollatzResearch.WordTrace tailWord_4087911 prefixEnd_4087911 466458492400413502913899 := by
  unfold tailWord_4087911
  simp only [CollatzResearch.WordTrace]
  refine ⟨149098363093204081460583587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99398908728802720973722391 149098363093204081460583587)
  ·
    refine ⟨223647544639806122190875381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149098363093204081460583587 223647544639806122190875381)
    ·
      refine ⟨20966957309981823955394567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223647544639806122190875381 20966957309981823955394567)
      ·
        refine ⟨31450435964972735933091851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20966957309981823955394567 31450435964972735933091851)
        ·
          refine ⟨47175653947459103899637777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31450435964972735933091851 47175653947459103899637777)
          ·
            refine ⟨35381740460594327924728333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47175653947459103899637777 35381740460594327924728333)
            ·
              refine ⟨13268152672722872971773125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35381740460594327924728333 13268152672722872971773125)
              ·
                refine ⟨2487778626135538682207461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13268152672722872971773125 2487778626135538682207461)
                ·
                  refine ⟨466458492400413502913899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2487778626135538682207461 466458492400413502913899)
                  ·
                    rfl

theorem cell22_4087911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 4].length) (baseStart_4087911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087911 prefixEnd_4087911 := by exact prefixLift 4087911
  have htrace : WordTrace (prefixWord ++ tailWord_4087911) baseStart_4087911 baseEnd_4087911 := by
    simpa [prefixWord, tailWord_4087911, baseEnd_4087911] using wordTrace_append hprefix tailTrace_4087911
  have hstable : (prefixWord ++ tailWord_4087911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087911).length < 2 ^ (prefixWord ++ tailWord_4087911).sum := by decide
  have hdescent : baseEnd_4087911 < baseStart_4087911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087926 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_4087926 : Nat := 118140960795 + 4087926 * 2 ^ 59
def prefixEnd_4087926 : Nat := 4983230072969 + 3 ^ 40 * 4087926 * 2
def baseEnd_4087926 : Nat := 1399380612007785469616651

theorem tailTrace_4087926 : CollatzResearch.WordTrace tailWord_4087926 prefixEnd_4087926 1399380612007785469616651 := by
  unfold tailWord_4087926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9318681886759358688898727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99399273458766492681586421 9318681886759358688898727)
  ·
    refine ⟨13978022830139038033348091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9318681886759358688898727 13978022830139038033348091)
    ·
      refine ⟨20967034245208557050022137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13978022830139038033348091 20967034245208557050022137)
      ·
        refine ⟨15725275683906417787516603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20967034245208557050022137 15725275683906417787516603)
        ·
          refine ⟨23587913525859626681274905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15725275683906417787516603 23587913525859626681274905)
          ·
            refine ⟨17690935144394720010956179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23587913525859626681274905 17690935144394720010956179)
            ·
              refine ⟨26536402716592080016434269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17690935144394720010956179 26536402716592080016434269)
              ·
                refine ⟨9951151018722030006162851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26536402716592080016434269 9951151018722030006162851)
                ·
                  refine ⟨14926726528083045009244277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9951151018722030006162851 14926726528083045009244277)
                  ·
                    refine ⟨1399380612007785469616651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14926726528083045009244277 1399380612007785469616651)
                    ·
                      rfl

theorem cell22_4087926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_4087926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087926 prefixEnd_4087926 := by exact prefixLift 4087926
  have htrace : WordTrace (prefixWord ++ tailWord_4087926) baseStart_4087926 baseEnd_4087926 := by
    simpa [prefixWord, tailWord_4087926, baseEnd_4087926] using wordTrace_append hprefix tailTrace_4087926
  have hstable : (prefixWord ++ tailWord_4087926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087926).length < 2 ^ (prefixWord ++ tailWord_4087926).sum := by decide
  have hdescent : baseEnd_4087926 < baseStart_4087926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087941 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_4087941 : Nat := 118140960795 + 4087941 * 2 ^ 59
def prefixEnd_4087941 : Nat := 4983230072969 + 3 ^ 40 * 4087941 * 2
def baseEnd_4087941 : Nat := 1399385746814330430491605

theorem tailTrace_4087941 : CollatzResearch.WordTrace tailWord_4087941 prefixEnd_4087941 1399385746814330430491605 := by
  unfold tailWord_4087941
  simp only [CollatzResearch.WordTrace]
  refine ⟨149099457283095396584175677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99399638188730264389450451 149099457283095396584175677)
  ·
    refine ⟨55912296481160773719065879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149099457283095396584175677 55912296481160773719065879)
    ·
      refine ⟨83868444721741160578598819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55912296481160773719065879 83868444721741160578598819)
      ·
        refine ⟨125802667082611740867898229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83868444721741160578598819 125802667082611740867898229)
        ·
          refine ⟨11794000038994850706365459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125802667082611740867898229 11794000038994850706365459)
          ·
            refine ⟨17691000058492276059548189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11794000038994850706365459 17691000058492276059548189)
            ·
              refine ⟨6634125021934603522330571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17691000058492276059548189 6634125021934603522330571)
              ·
                refine ⟨9951187532901905283495857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634125021934603522330571 9951187532901905283495857)
                ·
                  refine ⟨7463390649676428962621893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9951187532901905283495857 7463390649676428962621893)
                  ·
                    refine ⟨1399385746814330430491605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7463390649676428962621893 1399385746814330430491605)
                    ·
                      rfl

theorem cell22_4087941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_4087941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087941 prefixEnd_4087941 := by exact prefixLift 4087941
  have htrace : WordTrace (prefixWord ++ tailWord_4087941) baseStart_4087941 baseEnd_4087941 := by
    simpa [prefixWord, tailWord_4087941, baseEnd_4087941] using wordTrace_append hprefix tailTrace_4087941
  have hstable : (prefixWord ++ tailWord_4087941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087941).length < 2 ^ (prefixWord ++ tailWord_4087941).sum := by decide
  have hdescent : baseEnd_4087941 < baseStart_4087941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087960 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 2, 3]
def baseStart_4087960 : Nat := 118140960795 + 4087960 * 2 ^ 59
def prefixEnd_4087960 : Nat := 4983230072969 + 3 ^ 40 * 4087960 * 2
def baseEnd_4087960 : Nat := 1399392250902620714266547

theorem tailTrace_4087960 : CollatzResearch.WordTrace tailWord_4087960 prefixEnd_4087960 1399392250902620714266547 := by
  unfold tailWord_4087960
  simp only [CollatzResearch.WordTrace]
  refine ⟨74550075135013281414558667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99400100180017708552744889 74550075135013281414558667)
  ·
    refine ⟨111825112702519922121838001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74550075135013281414558667 111825112702519922121838001)
    ·
      refine ⟨83868834526889941591378501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111825112702519922121838001 83868834526889941591378501)
      ·
        refine ⟨15725406473791864048383469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83868834526889941591378501 15725406473791864048383469)
        ·
          refine ⟨5897027427671949018143801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15725406473791864048383469 5897027427671949018143801)
          ·
            refine ⟨4422770570753961763607851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5897027427671949018143801 4422770570753961763607851)
            ·
              refine ⟨6634155856130942645411777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4422770570753961763607851 6634155856130942645411777)
              ·
                refine ⟨4975616892098206984058833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6634155856130942645411777 4975616892098206984058833)
                ·
                  refine ⟨3731712669073655238044125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4975616892098206984058833 3731712669073655238044125)
                  ·
                    refine ⟨1399392250902620714266547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731712669073655238044125 1399392250902620714266547)
                    ·
                      rfl

theorem cell22_4087960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_4087960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4087960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4087960 prefixEnd_4087960 := by exact prefixLift 4087960
  have htrace : WordTrace (prefixWord ++ tailWord_4087960) baseStart_4087960 baseEnd_4087960 := by
    simpa [prefixWord, tailWord_4087960, baseEnd_4087960] using wordTrace_append hprefix tailTrace_4087960
  have hstable : (prefixWord ++ tailWord_4087960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087960).length < 2 ^ (prefixWord ++ tailWord_4087960).sum := by decide
  have hdescent : baseEnd_4087960 < baseStart_4087960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088022 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_4088022 : Nat := 118140960795 + 4088022 * 2 ^ 59
def prefixEnd_4088022 : Nat := 4983230072969 + 3 ^ 40 * 4088022 * 2
def baseEnd_4088022 : Nat := 1399413474769673219216357

theorem tailTrace_4088022 : CollatzResearch.WordTrace tailWord_4088022 prefixEnd_4088022 1399413474769673219216357 := by
  unfold tailWord_4088022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9318900724737621713617145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99401607730534631611916213 9318900724737621713617145)
  ·
    refine ⟨6989175543553216285212859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9318900724737621713617145 6989175543553216285212859)
    ·
      refine ⟨10483763315329824427819289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6989175543553216285212859 10483763315329824427819289)
      ·
        refine ⟨7862822486497368320864467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10483763315329824427819289 7862822486497368320864467)
        ·
          refine ⟨11794233729746052481296701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7862822486497368320864467 11794233729746052481296701)
          ·
            refine ⟨4422837648654769680486263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11794233729746052481296701 4422837648654769680486263)
            ·
              refine ⟨6634256472982154520729395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4422837648654769680486263 6634256472982154520729395)
              ·
                refine ⟨9951384709473231781094093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634256472982154520729395 9951384709473231781094093)
                ·
                  refine ⟨3731769266052461917910285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9951384709473231781094093 3731769266052461917910285)
                  ·
                    refine ⟨1399413474769673219216357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731769266052461917910285 1399413474769673219216357)
                    ·
                      rfl

theorem cell22_4088022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_4088022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088022 prefixEnd_4088022 := by exact prefixLift 4088022
  have htrace : WordTrace (prefixWord ++ tailWord_4088022) baseStart_4088022 baseEnd_4088022 := by
    simpa [prefixWord, tailWord_4088022, baseEnd_4088022] using wordTrace_append hprefix tailTrace_4088022
  have hstable : (prefixWord ++ tailWord_4088022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088022).length < 2 ^ (prefixWord ++ tailWord_4088022).sum := by decide
  have hdescent : baseEnd_4088022 < baseStart_4088022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088061 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_4088061 : Nat := 118140960795 + 4088061 * 2 ^ 59
def prefixEnd_4088061 : Nat := 4983230072969 + 3 ^ 40 * 4088061 * 2
def baseEnd_4088061 : Nat := 1399426825266690117491237

theorem tailTrace_4088061 : CollatzResearch.WordTrace tailWord_4088061 prefixEnd_4088061 1399426825266690117491237 := by
  unfold tailWord_4088061
  simp only [CollatzResearch.WordTrace]
  refine ⟨149103834042660657078544037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99402556028440438052362691 149103834042660657078544037)
  ·
    refine ⟨27956968882998873202227007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149103834042660657078544037 27956968882998873202227007)
    ·
      refine ⟨41935453324498309803340511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27956968882998873202227007 41935453324498309803340511)
      ·
        refine ⟨62903179986747464705010767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41935453324498309803340511 62903179986747464705010767)
        ·
          refine ⟨94354769980121197057516151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62903179986747464705010767 94354769980121197057516151)
          ·
            refine ⟨141532154970181795586274227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94354769980121197057516151 141532154970181795586274227)
            ·
              refine ⟨212298232455272693379411341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141532154970181795586274227 212298232455272693379411341)
              ·
                refine ⟨79611837170727260017279253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212298232455272693379411341 79611837170727260017279253)
                ·
                  refine ⟨3731804867377840313309965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79611837170727260017279253 3731804867377840313309965)
                  ·
                    refine ⟨1399426825266690117491237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731804867377840313309965 1399426825266690117491237)
                    ·
                      rfl

theorem cell22_4088061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_4088061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088061 prefixEnd_4088061 := by exact prefixLift 4088061
  have htrace : WordTrace (prefixWord ++ tailWord_4088061) baseStart_4088061 baseEnd_4088061 := by
    simpa [prefixWord, tailWord_4088061, baseEnd_4088061] using wordTrace_append hprefix tailTrace_4088061
  have hstable : (prefixWord ++ tailWord_4088061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088061).length < 2 ^ (prefixWord ++ tailWord_4088061).sum := by decide
  have hdescent : baseEnd_4088061 < baseStart_4088061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088076 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_4088076 : Nat := 118140960795 + 4088076 * 2 ^ 59
def prefixEnd_4088076 : Nat := 4983230072969 + 3 ^ 40 * 4088076 * 2
def baseEnd_4088076 : Nat := 1399431960073235078366191

theorem tailTrace_4088076 : CollatzResearch.WordTrace tailWord_4088076 prefixEnd_4088076 1399431960073235078366191 := by
  unfold tailWord_4088076
  simp only [CollatzResearch.WordTrace]
  refine ⟨74552190568803157320170041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99402920758404209760226721 74552190568803157320170041)
  ·
    refine ⟨55914142926602367990127531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74552190568803157320170041 55914142926602367990127531)
    ·
      refine ⟨83871214389903551985191297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55914142926602367990127531 83871214389903551985191297)
      ·
        refine ⟨62903410792427663988893473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83871214389903551985191297 62903410792427663988893473)
        ·
          refine ⟨47177558094320747991670105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62903410792427663988893473 47177558094320747991670105)
          ·
            refine ⟨35383168570740560993752579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47177558094320747991670105 35383168570740560993752579)
            ·
              refine ⟨53074752856110841490628869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35383168570740560993752579 53074752856110841490628869)
              ·
                refine ⟨9951516160520782779492913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53074752856110841490628869 9951516160520782779492913)
                ·
                  refine ⟨7463637120390587084619685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9951516160520782779492913 7463637120390587084619685)
                  ·
                    refine ⟨1399431960073235078366191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7463637120390587084619685 1399431960073235078366191)
                    ·
                      rfl

theorem cell22_4088076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_4088076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088076 prefixEnd_4088076 := by exact prefixLift 4088076
  have htrace : WordTrace (prefixWord ++ tailWord_4088076) baseStart_4088076 baseEnd_4088076 := by
    simpa [prefixWord, tailWord_4088076, baseEnd_4088076] using wordTrace_append hprefix tailTrace_4088076
  have hstable : (prefixWord ++ tailWord_4088076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088076).length < 2 ^ (prefixWord ++ tailWord_4088076).sum := by decide
  have hdescent : baseEnd_4088076 < baseStart_4088076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088110 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_4088110 : Nat := 118140960795 + 4088110 * 2 ^ 59
def prefixEnd_4088110 : Nat := 4983230072969 + 3 ^ 40 * 4088110 * 2
def baseEnd_4088110 : Nat := 1399443598968070323016087

theorem tailTrace_4088110 : CollatzResearch.WordTrace tailWord_4088110 prefixEnd_4088110 1399443598968070323016087 := by
  unfold tailWord_4088110
  simp only [CollatzResearch.WordTrace]
  refine ⟨18638202652435392305884723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99403747479655425631385189 18638202652435392305884723)
  ·
    refine ⟨27957303978653088458827085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18638202652435392305884723 27957303978653088458827085)
    ·
      refine ⟨10483988991994908172060157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27957303978653088458827085 10483988991994908172060157)
      ·
        refine ⟨3931495871998090564522559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10483988991994908172060157 3931495871998090564522559)
        ·
          refine ⟨5897243807997135846783839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931495871998090564522559 5897243807997135846783839)
          ·
            refine ⟨8845865711995703770175759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5897243807997135846783839 8845865711995703770175759)
            ·
              refine ⟨13268798567993555655263639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8845865711995703770175759 13268798567993555655263639)
              ·
                refine ⟨19903197851990333482895459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13268798567993555655263639 19903197851990333482895459)
                ·
                  refine ⟨29854796777985500224343189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19903197851990333482895459 29854796777985500224343189)
                  ·
                    refine ⟨1399443598968070323016087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29854796777985500224343189 1399443598968070323016087)
                    ·
                      rfl

theorem cell22_4088110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_4088110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088110 prefixEnd_4088110 := by exact prefixLift 4088110
  have htrace : WordTrace (prefixWord ++ tailWord_4088110) baseStart_4088110 baseEnd_4088110 := by
    simpa [prefixWord, tailWord_4088110, baseEnd_4088110] using wordTrace_append hprefix tailTrace_4088110
  have hstable : (prefixWord ++ tailWord_4088110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088110).length < 2 ^ (prefixWord ++ tailWord_4088110).sum := by decide
  have hdescent : baseEnd_4088110 < baseStart_4088110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088129 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 2, 3]
def baseStart_4088129 : Nat := 118140960795 + 4088129 * 2 ^ 59
def prefixEnd_4088129 : Nat := 4983230072969 + 3 ^ 40 * 4088129 * 2
def baseEnd_4088129 : Nat := 1399450103056360606791029

theorem tailTrace_4088129 : CollatzResearch.WordTrace tailWord_4088129 prefixEnd_4088129 1399450103056360606791029 := by
  unfold tailWord_4088129
  simp only [CollatzResearch.WordTrace]
  refine ⟨149106314206414304692019441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99404209470942869794679627 149106314206414304692019441)
  ·
    refine ⟨111829735654810728519014581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149106314206414304692019441 111829735654810728519014581)
    ·
      refine ⟨10484037717638505798657617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111829735654810728519014581 10484037717638505798657617)
      ·
        refine ⟨7863028288228879348993213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10484037717638505798657617 7863028288228879348993213)
        ·
          refine ⟨2948635608085829755872455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7863028288228879348993213 2948635608085829755872455)
          ·
            refine ⟨4422953412128744633808683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948635608085829755872455 4422953412128744633808683)
            ·
              refine ⟨6634430118193116950713025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4422953412128744633808683 6634430118193116950713025)
              ·
                refine ⟨4975822588644837713034769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6634430118193116950713025 4975822588644837713034769)
                ·
                  refine ⟨3731866941483628284776077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4975822588644837713034769 3731866941483628284776077)
                  ·
                    refine ⟨1399450103056360606791029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731866941483628284776077 1399450103056360606791029)
                    ·
                      rfl

theorem cell22_4088129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_4088129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088129 prefixEnd_4088129 := by exact prefixLift 4088129
  have htrace : WordTrace (prefixWord ++ tailWord_4088129) baseStart_4088129 baseEnd_4088129 := by
    simpa [prefixWord, tailWord_4088129, baseEnd_4088129] using wordTrace_append hprefix tailTrace_4088129
  have hstable : (prefixWord ++ tailWord_4088129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088129).length < 2 ^ (prefixWord ++ tailWord_4088129).sum := by decide
  have hdescent : baseEnd_4088129 < baseStart_4088129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088140 : List Nat := [2, 2, 1, 3, 2, 1, 1, 6, 1, 3]
def baseStart_4088140 : Nat := 118140960795 + 4088140 * 2 ^ 59
def prefixEnd_4088140 : Nat := 4983230072969 + 3 ^ 40 * 4088140 * 2
def baseEnd_4088140 : Nat := 1399453868581160244765995

theorem tailTrace_4088140 : CollatzResearch.WordTrace tailWord_4088140 prefixEnd_4088140 1399453868581160244765995 := by
  unfold tailWord_4088140
  simp only [CollatzResearch.WordTrace]
  refine ⟨74553357704687226785334937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99404476939582969047113249 74553357704687226785334937)
  ·
    refine ⟨55915018278515420089001203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74553357704687226785334937 55915018278515420089001203)
    ·
      refine ⟨83872527417773130133501805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55915018278515420089001203 83872527417773130133501805)
      ·
        refine ⟨31452197781664923800063177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83872527417773130133501805 31452197781664923800063177)
        ·
          refine ⟨23589148336248692850047383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31452197781664923800063177 23589148336248692850047383)
          ·
            refine ⟨35383722504373039275071075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23589148336248692850047383 35383722504373039275071075)
            ·
              refine ⟨53075583756559558912606613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35383722504373039275071075 53075583756559558912606613)
              ·
                refine ⟨2487917988588729324028435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53075583756559558912606613 2487917988588729324028435)
                ·
                  refine ⟨3731876982883093986042653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487917988588729324028435 3731876982883093986042653)
                  ·
                    refine ⟨1399453868581160244765995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731876982883093986042653 1399453868581160244765995)
                    ·
                      rfl

theorem cell22_4088140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_4088140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088140 prefixEnd_4088140 := by exact prefixLift 4088140
  have htrace : WordTrace (prefixWord ++ tailWord_4088140) baseStart_4088140 baseEnd_4088140 := by
    simpa [prefixWord, tailWord_4088140, baseEnd_4088140] using wordTrace_append hprefix tailTrace_4088140
  have hstable : (prefixWord ++ tailWord_4088140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088140).length < 2 ^ (prefixWord ++ tailWord_4088140).sum := by decide
  have hdescent : baseEnd_4088140 < baseStart_4088140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088151 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 2, 5]
def baseStart_4088151 : Nat := 118140960795 + 4088151 * 2 ^ 59
def prefixEnd_4088151 : Nat := 4983230072969 + 3 ^ 40 * 4088151 * 2
def baseEnd_4088151 : Nat := 1399457634105959882740961

theorem tailTrace_4088151 : CollatzResearch.WordTrace tailWord_4088151 prefixEnd_4088151 1399457634105959882740961 := by
  unfold tailWord_4088151
  simp only [CollatzResearch.WordTrace]
  refine ⟨149107116612334602449320307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99404744408223068299546871 149107116612334602449320307)
  ·
    refine ⟨223660674918501903673980461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149107116612334602449320307 223660674918501903673980461)
    ·
      refine ⟨83872753094438213877742673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223660674918501903673980461 83872753094438213877742673)
      ·
        refine ⟨62904564820828660408307005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83872753094438213877742673 62904564820828660408307005)
        ·
          refine ⟨23589211807810747653115127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62904564820828660408307005 23589211807810747653115127)
          ·
            refine ⟨35383817711716121479672691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23589211807810747653115127 35383817711716121479672691)
            ·
              refine ⟨53075726567574182219509037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35383817711716121479672691 53075726567574182219509037)
              ·
                refine ⟨19903397462840318332315889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53075726567574182219509037 19903397462840318332315889)
                ·
                  refine ⟨14927548097130238749236917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19903397462840318332315889 14927548097130238749236917)
                  ·
                    refine ⟨1399457634105959882740961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14927548097130238749236917 1399457634105959882740961)
                    ·
                      rfl

theorem cell22_4088151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_4088151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088151 prefixEnd_4088151 := by exact prefixLift 4088151
  have htrace : WordTrace (prefixWord ++ tailWord_4088151) baseStart_4088151 baseEnd_4088151 := by
    simpa [prefixWord, tailWord_4088151, baseEnd_4088151] using wordTrace_append hprefix tailTrace_4088151
  have hstable : (prefixWord ++ tailWord_4088151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088151).length < 2 ^ (prefixWord ++ tailWord_4088151).sum := by decide
  have hdescent : baseEnd_4088151 < baseStart_4088151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088228 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_4088228 : Nat := 118140960795 + 4088228 * 2 ^ 59
def prefixEnd_4088228 : Nat := 4983230072969 + 3 ^ 40 * 4088228 * 2
def baseEnd_4088228 : Nat := 1399483992779557348565725

theorem tailTrace_4088228 : CollatzResearch.WordTrace tailWord_4088228 prefixEnd_4088228 1399483992779557348565725 := by
  unfold tailWord_4088228
  simp only [CollatzResearch.WordTrace]
  refine ⟨74554962516527822299936669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99406616688703763066582225 74554962516527822299936669)
  ·
    refine ⟨27958110943697933362476251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74554962516527822299936669 27958110943697933362476251)
    ·
      refine ⟨41937166415546900043714377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27958110943697933362476251 41937166415546900043714377)
      ·
        refine ⟨31452874811660175032785783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41937166415546900043714377 31452874811660175032785783)
        ·
          refine ⟨47179312217490262549178675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31452874811660175032785783 47179312217490262549178675)
          ·
            refine ⟨70768968326235393823768013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47179312217490262549178675 70768968326235393823768013)
            ·
              refine ⟨26538363122338272683913005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70768968326235393823768013 26538363122338272683913005)
              ·
                refine ⟨9951886170876852256467377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26538363122338272683913005 9951886170876852256467377)
                ·
                  refine ⟨7463914628157639192350533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9951886170876852256467377 7463914628157639192350533)
                  ·
                    refine ⟨1399483992779557348565725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7463914628157639192350533 1399483992779557348565725)
                    ·
                      rfl

theorem cell22_4088228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_4088228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088228 prefixEnd_4088228 := by exact prefixLift 4088228
  have htrace : WordTrace (prefixWord ++ tailWord_4088228) baseStart_4088228 baseEnd_4088228 := by
    simpa [prefixWord, tailWord_4088228, baseEnd_4088228] using wordTrace_append hprefix tailTrace_4088228
  have hstable : (prefixWord ++ tailWord_4088228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088228).length < 2 ^ (prefixWord ++ tailWord_4088228).sum := by decide
  have hdescent : baseEnd_4088228 < baseStart_4088228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088271 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 9]
def baseStart_4088271 : Nat := 118140960795 + 4088271 * 2 ^ 59
def prefixEnd_4088271 : Nat := 4983230072969 + 3 ^ 40 * 4088271 * 2
def baseEnd_4088271 : Nat := 466499570852773189913531

theorem tailTrace_4088271 : CollatzResearch.WordTrace tailWord_4088271 prefixEnd_4088271 466499570852773189913531 := by
  unfold tailWord_4088271
  simp only [CollatzResearch.WordTrace]
  refine ⟨149111493371899862943688667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99407662247933241962459111 149111493371899862943688667)
  ·
    refine ⟨223667240057849794415533001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149111493371899862943688667 223667240057849794415533001)
    ·
      refine ⟨167750430043387345811649751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223667240057849794415533001 167750430043387345811649751)
      ·
        refine ⟨251625645065081018717474627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167750430043387345811649751 251625645065081018717474627)
        ·
          refine ⟨377438467597621528076211941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251625645065081018717474627 377438467597621528076211941)
          ·
            refine ⟨70769712674554036514289739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377438467597621528076211941 70769712674554036514289739)
            ·
              refine ⟨106154569011831054771434609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70769712674554036514289739 106154569011831054771434609)
              ·
                refine ⟨79615926758873291078575957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106154569011831054771434609 79615926758873291078575957)
                ·
                  refine ⟨466499570852773189913531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79615926758873291078575957 466499570852773189913531)
                  ·
                    rfl

theorem cell22_4088271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 9].length) (baseStart_4088271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088271 prefixEnd_4088271 := by exact prefixLift 4088271
  have htrace : WordTrace (prefixWord ++ tailWord_4088271) baseStart_4088271 baseEnd_4088271 := by
    simpa [prefixWord, tailWord_4088271, baseEnd_4088271] using wordTrace_append hprefix tailTrace_4088271
  have hstable : (prefixWord ++ tailWord_4088271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088271).length < 2 ^ (prefixWord ++ tailWord_4088271).sum := by decide
  have hdescent : baseEnd_4088271 < baseStart_4088271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088309 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 3, 3]
def baseStart_4088309 : Nat := 118140960795 + 4088309 * 2 ^ 59
def prefixEnd_4088309 : Nat := 4983230072969 + 3 ^ 40 * 4088309 * 2
def baseEnd_4088309 : Nat := 1399511720734900137290477

theorem tailTrace_4088309 : CollatzResearch.WordTrace tailWord_4088309 prefixEnd_4088309 1399511720734900137290477 := by
  unfold tailWord_4088309
  simp only [CollatzResearch.WordTrace]
  refine ⟨149112879345762195433571981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99408586230508130289047987 149112879345762195433571981)
  ·
    refine ⟨55917329754660823287589493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149112879345762195433571981 55917329754660823287589493)
    ·
      refine ⟨5242249664499452183211515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55917329754660823287589493 5242249664499452183211515)
      ·
        refine ⟨7863374496749178274817273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5242249664499452183211515 7863374496749178274817273)
        ·
          refine ⟨5897530872561883706112955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7863374496749178274817273 5897530872561883706112955)
          ·
            refine ⟨8846296308842825559169433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5897530872561883706112955 8846296308842825559169433)
            ·
              refine ⟨6634722231632119169377075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8846296308842825559169433 6634722231632119169377075)
              ·
                refine ⟨9952083347448178754065613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634722231632119169377075 9952083347448178754065613)
                ·
                  refine ⟨3732031255293067032774605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9952083347448178754065613 3732031255293067032774605)
                  ·
                    refine ⟨1399511720734900137290477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3732031255293067032774605 1399511720734900137290477)
                    ·
                      rfl

theorem cell22_4088309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_4088309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088309 prefixEnd_4088309 := by exact prefixLift 4088309
  have htrace : WordTrace (prefixWord ++ tailWord_4088309) baseStart_4088309 baseEnd_4088309 := by
    simpa [prefixWord, tailWord_4088309, baseEnd_4088309] using wordTrace_append hprefix tailTrace_4088309
  have hstable : (prefixWord ++ tailWord_4088309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088309).length < 2 ^ (prefixWord ++ tailWord_4088309).sum := by decide
  have hdescent : baseEnd_4088309 < baseStart_4088309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088326 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4088326 : Nat := 118140960795 + 4088326 * 2 ^ 59
def prefixEnd_4088326 : Nat := 4983230072969 + 3 ^ 40 * 4088326 * 2
def baseEnd_4088326 : Nat := 1399517540182317759615425

theorem tailTrace_4088326 : CollatzResearch.WordTrace tailWord_4088326 prefixEnd_4088326 1399517540182317759615425 := by
  unfold tailWord_4088326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4659796855834393979279401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99408999591133738224627221 4659796855834393979279401)
  ·
    refine ⟨3494847641875795484459551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4659796855834393979279401 3494847641875795484459551)
    ·
      refine ⟨5242271462813693226689327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3494847641875795484459551 5242271462813693226689327)
      ·
        refine ⟨7863407194220539840033991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5242271462813693226689327 7863407194220539840033991)
        ·
          refine ⟨11795110791330809760050987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7863407194220539840033991 11795110791330809760050987)
          ·
            refine ⟨17692666186996214640076481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11795110791330809760050987 17692666186996214640076481)
            ·
              refine ⟨13269499640247160980057361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17692666186996214640076481 13269499640247160980057361)
              ·
                refine ⟨9952124730185370735043021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13269499640247160980057361 9952124730185370735043021)
                ·
                  refine ⟨3732046773819514025641133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9952124730185370735043021 3732046773819514025641133)
                  ·
                    refine ⟨1399517540182317759615425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3732046773819514025641133 1399517540182317759615425)
                    ·
                      rfl

theorem cell22_4088326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4088326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088326 prefixEnd_4088326 := by exact prefixLift 4088326
  have htrace : WordTrace (prefixWord ++ tailWord_4088326) baseStart_4088326 baseEnd_4088326 := by
    simpa [prefixWord, tailWord_4088326, baseEnd_4088326] using wordTrace_append hprefix tailTrace_4088326
  have hstable : (prefixWord ++ tailWord_4088326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088326).length < 2 ^ (prefixWord ++ tailWord_4088326).sum := by decide
  have hdescent : baseEnd_4088326 < baseStart_4088326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088343 : List Nat := [1, 1, 3, 6, 2, 1, 1, 3, 1, 3]
def baseStart_4088343 : Nat := 118140960795 + 4088343 * 2 ^ 59
def prefixEnd_4088343 : Nat := 4983230072969 + 3 ^ 40 * 4088343 * 2
def baseEnd_4088343 : Nat := 1399523359629735381940373

theorem tailTrace_4088343 : CollatzResearch.WordTrace tailWord_4088343 prefixEnd_4088343 1399523359629735381940373 := by
  unfold tailWord_4088343
  simp only [CollatzResearch.WordTrace]
  refine ⟨149114119427639019240309683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99409412951759346160206455 149114119427639019240309683)
  ·
    refine ⟨223671179141458528860464525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149114119427639019240309683 223671179141458528860464525)
    ·
      refine ⟨83876692178046948322674197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223671179141458528860464525 83876692178046948322674197)
      ·
        refine ⟨3931719945845950702625353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83876692178046948322674197 3931719945845950702625353)
        ·
          refine ⟨2948789959384463026969015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3931719945845950702625353 2948789959384463026969015)
          ·
            refine ⟨4423184939076694540453523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948789959384463026969015 4423184939076694540453523)
            ·
              refine ⟨6634777408615041810680285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423184939076694540453523 6634777408615041810680285)
              ·
                refine ⟨2488041528230640679005107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6634777408615041810680285 2488041528230640679005107)
                ·
                  refine ⟨3732062292345961018507661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488041528230640679005107 3732062292345961018507661)
                  ·
                    refine ⟨1399523359629735381940373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3732062292345961018507661 1399523359629735381940373)
                    ·
                      rfl

theorem cell22_4088343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_4088343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088343 prefixEnd_4088343 := by exact prefixLift 4088343
  have htrace : WordTrace (prefixWord ++ tailWord_4088343) baseStart_4088343 baseEnd_4088343 := by
    simpa [prefixWord, tailWord_4088343, baseEnd_4088343] using wordTrace_append hprefix tailTrace_4088343
  have hstable : (prefixWord ++ tailWord_4088343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088343).length < 2 ^ (prefixWord ++ tailWord_4088343).sum := by decide
  have hdescent : baseEnd_4088343 < baseStart_4088343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088378 : List Nat := [3, 1, 1, 1, 3, 3, 1, 9]
def baseStart_4088378 : Nat := 118140960795 + 4088378 * 2 ^ 59
def prefixEnd_4088378 : Nat := 4983230072969 + 3 ^ 40 * 4088378 * 2
def baseEnd_4088378 : Nat := 155503926760556328590585

theorem tailTrace_4088378 : CollatzResearch.WordTrace tailWord_4088378 prefixEnd_4088378 155503926760556328590585 := by
  unfold tailWord_4088378
  simp only [CollatzResearch.WordTrace]
  refine ⟨37278848995628055054458447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99410263988341480145222525 37278848995628055054458447)
  ·
    refine ⟨55918273493442082581687671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37278848995628055054458447 55918273493442082581687671)
    ·
      refine ⟨83877410240163123872531507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55918273493442082581687671 83877410240163123872531507)
      ·
        refine ⟨125816115360244685808797261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83877410240163123872531507 125816115360244685808797261)
        ·
          refine ⟨47181043260091757178298973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125816115360244685808797261 47181043260091757178298973)
          ·
            refine ⟨17692891222534408941862115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47181043260091757178298973 17692891222534408941862115)
            ·
              refine ⟨26539336833801613412793173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17692891222534408941862115 26539336833801613412793173)
              ·
                refine ⟨155503926760556328590585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26539336833801613412793173 155503926760556328590585)
                ·
                  rfl

theorem cell22_4088378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_4088378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088378 prefixEnd_4088378 := by exact prefixLift 4088378
  have htrace : WordTrace (prefixWord ++ tailWord_4088378) baseStart_4088378 baseEnd_4088378 := by
    simpa [prefixWord, tailWord_4088378, baseEnd_4088378] using wordTrace_append hprefix tailTrace_4088378
  have hstable : (prefixWord ++ tailWord_4088378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088378).length < 2 ^ (prefixWord ++ tailWord_4088378).sum := by decide
  have hdescent : baseEnd_4088378 < baseStart_4088378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088397 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_4088397 : Nat := 118140960795 + 4088397 * 2 ^ 59
def prefixEnd_4088397 : Nat := 4983230072969 + 3 ^ 40 * 4088397 * 2
def baseEnd_4088397 : Nat := 1399541844933297241090207

theorem tailTrace_4088397 : CollatzResearch.WordTrace tailWord_4088397 prefixEnd_4088397 1399541844933297241090207 := by
  unfold tailWord_4088397
  simp only [CollatzResearch.WordTrace]
  refine ⟨149116088969443386462775445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99410725979628924308516963 149116088969443386462775445)
  ·
    refine ⟨6989816670442658740442599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149116088969443386462775445 6989816670442658740442599)
    ·
      refine ⟨10484725005663988110663899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6989816670442658740442599 10484725005663988110663899)
      ·
        refine ⟨15727087508495982165995849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10484725005663988110663899 15727087508495982165995849)
        ·
          refine ⟨11795315631371986624496887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15727087508495982165995849 11795315631371986624496887)
          ·
            refine ⟨17692973447057979936745331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11795315631371986624496887 17692973447057979936745331)
            ·
              refine ⟨26539460170586969905117997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17692973447057979936745331 26539460170586969905117997)
              ·
                refine ⟨9952297563970113714419249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26539460170586969905117997 9952297563970113714419249)
                ·
                  refine ⟨7464223172977585285814437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9952297563970113714419249 7464223172977585285814437)
                  ·
                    refine ⟨1399541844933297241090207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7464223172977585285814437 1399541844933297241090207)
                    ·
                      rfl

theorem cell22_4088397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_4088397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088397 prefixEnd_4088397 := by exact prefixLift 4088397
  have htrace : WordTrace (prefixWord ++ tailWord_4088397) baseStart_4088397 baseEnd_4088397 := by
    simpa [prefixWord, tailWord_4088397, baseEnd_4088397] using wordTrace_append hprefix tailTrace_4088397
  have hstable : (prefixWord ++ tailWord_4088397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088397).length < 2 ^ (prefixWord ++ tailWord_4088397).sum := by decide
  have hdescent : baseEnd_4088397 < baseStart_4088397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088418 : List Nat := [3, 3, 2, 3, 1, 2, 2, 2, 4]
def baseStart_4088418 : Nat := 118140960795 + 4088418 * 2 ^ 59
def prefixEnd_4088418 : Nat := 4983230072969 + 3 ^ 40 * 4088418 * 2
def baseEnd_4088418 : Nat := 466516344554153395438381

theorem tailTrace_4088418 : CollatzResearch.WordTrace tailWord_4088418 prefixEnd_4088418 466516344554153395438381 := by
  unfold tailWord_4088418
  simp only [CollatzResearch.WordTrace]
  refine ⟨37279213725591826762322477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99411236601578204699526605 37279213725591826762322477)
  ·
    refine ⟨13979705147096935035870929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37279213725591826762322477 13979705147096935035870929)
    ·
      refine ⟨10484778860322701276903197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13979705147096935035870929 10484778860322701276903197)
      ·
        refine ⟨3931792072621012978838699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10484778860322701276903197 3931792072621012978838699)
        ·
          refine ⟨5897688108931519468258049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931792072621012978838699 5897688108931519468258049)
          ·
            refine ⟨4423266081698639601193537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5897688108931519468258049 4423266081698639601193537)
            ·
              refine ⟨3317449561273979700895153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4423266081698639601193537 3317449561273979700895153)
              ·
                refine ⟨2488087170955484775671365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317449561273979700895153 2488087170955484775671365)
                ·
                  refine ⟨466516344554153395438381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2488087170955484775671365 466516344554153395438381)
                  ·
                    rfl

theorem cell22_4088418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_4088418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088418 prefixEnd_4088418 := by exact prefixLift 4088418
  have htrace : WordTrace (prefixWord ++ tailWord_4088418) baseStart_4088418 baseEnd_4088418 := by
    simpa [prefixWord, tailWord_4088418, baseEnd_4088418] using wordTrace_append hprefix tailTrace_4088418
  have hstable : (prefixWord ++ tailWord_4088418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088418).length < 2 ^ (prefixWord ++ tailWord_4088418).sum := by decide
  have hdescent : baseEnd_4088418 < baseStart_4088418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088547 : List Nat := [1, 1, 1, 7, 1, 2, 2, 7]
def baseStart_4088547 : Nat := 118140960795 + 4088547 * 2 ^ 59
def prefixEnd_4088547 : Nat := 4983230072969 + 3 ^ 40 * 4088547 * 2
def baseEnd_4088547 : Nat := 155510354777638538871083

theorem tailTrace_4088547 : CollatzResearch.WordTrace tailWord_4088547 prefixEnd_4088547 155510354777638538871083 := by
  unfold tailWord_4088547
  simp only [CollatzResearch.WordTrace]
  refine ⟨149121559918899962080735895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99414373279266641387157263 149121559918899962080735895)
  ·
    refine ⟨223682339878349943121103843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149121559918899962080735895 223682339878349943121103843)
    ·
      refine ⟨335523509817524914681655765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223682339878349943121103843 335523509817524914681655765)
      ·
        refine ⟨7863832261348240187851307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 335523509817524914681655765 7863832261348240187851307)
        ·
          refine ⟨11795748392022360281776961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7863832261348240187851307 11795748392022360281776961)
          ·
            refine ⟨8846811294016770211332721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11795748392022360281776961 8846811294016770211332721)
            ·
              refine ⟨6635108470512577658499541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8846811294016770211332721 6635108470512577658499541)
              ·
                refine ⟨155510354777638538871083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6635108470512577658499541 155510354777638538871083)
                ·
                  rfl

theorem cell22_4088547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 7].length) (baseStart_4088547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088547 prefixEnd_4088547 := by exact prefixLift 4088547
  have htrace : WordTrace (prefixWord ++ tailWord_4088547) baseStart_4088547 baseEnd_4088547 := by
    simpa [prefixWord, tailWord_4088547, baseEnd_4088547] using wordTrace_append hprefix tailTrace_4088547
  have hstable : (prefixWord ++ tailWord_4088547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088547).length < 2 ^ (prefixWord ++ tailWord_4088547).sum := by decide
  have hdescent : baseEnd_4088547 < baseStart_4088547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088579 : List Nat := [1, 1, 1, 3, 2, 2, 1, 7, 1, 3]
def baseStart_4088579 : Nat := 118140960795 + 4088579 * 2 ^ 59
def prefixEnd_4088579 : Nat := 4983230072969 + 3 ^ 40 * 4088579 * 2
def baseEnd_4088579 : Nat := 1399604147252709433039649

theorem tailTrace_4088579 : CollatzResearch.WordTrace tailWord_4088579 prefixEnd_4088579 1399604147252709433039649 := by
  unfold tailWord_4088579
  simp only [CollatzResearch.WordTrace]
  refine ⟨149122727054784031545900791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99415151369856021030600527 149122727054784031545900791)
  ·
    refine ⟨223684090582176047318851187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149122727054784031545900791 223684090582176047318851187)
    ·
      refine ⟨335526135873264070978276781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223684090582176047318851187 335526135873264070978276781)
      ·
        refine ⟨125822300952474026616853793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335526135873264070978276781 125822300952474026616853793)
        ·
          refine ⟨94366725714355519962640345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125822300952474026616853793 94366725714355519962640345)
          ·
            refine ⟨70775044285766639971980259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94366725714355519962640345 70775044285766639971980259)
            ·
              refine ⟨106162566428649959957970389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70775044285766639971980259 106162566428649959957970389)
              ·
                refine ⟨2488185150671483436514931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106162566428649959957970389 2488185150671483436514931)
                ·
                  refine ⟨3732277726007225154772397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488185150671483436514931 3732277726007225154772397)
                  ·
                    refine ⟨1399604147252709433039649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3732277726007225154772397 1399604147252709433039649)
                    ·
                      rfl

theorem cell22_4088579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 1, 3].length) (baseStart_4088579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088579 prefixEnd_4088579 := by exact prefixLift 4088579
  have htrace : WordTrace (prefixWord ++ tailWord_4088579) baseStart_4088579 baseEnd_4088579 := by
    simpa [prefixWord, tailWord_4088579, baseEnd_4088579] using wordTrace_append hprefix tailTrace_4088579
  have hstable : (prefixWord ++ tailWord_4088579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088579).length < 2 ^ (prefixWord ++ tailWord_4088579).sum := by decide
  have hdescent : baseEnd_4088579 < baseStart_4088579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088607 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 2, 5]
def baseStart_4088607 : Nat := 118140960795 + 4088607 * 2 ^ 59
def prefixEnd_4088607 : Nat := 4983230072969 + 3 ^ 40 * 4088607 * 2
def baseEnd_4088607 : Nat := 1399613732224926693339563

theorem tailTrace_4088607 : CollatzResearch.WordTrace tailWord_4088607 prefixEnd_4088607 1399613732224926693339563 := by
  unfold tailWord_4088607
  simp only [CollatzResearch.WordTrace]
  refine ⟨149123748298682592327920075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99415832199121728218613383 149123748298682592327920075)
  ·
    refine ⟨223685622448023888491880113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149123748298682592327920075 223685622448023888491880113)
    ·
      refine ⟨167764216836017916368910085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223685622448023888491880113 167764216836017916368910085)
      ·
        refine ⟨31455790656753359319170641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167764216836017916368910085 31455790656753359319170641)
        ·
          refine ⟨23591842992565019489377981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31455790656753359319170641 23591842992565019489377981)
          ·
            refine ⟨8846941122211882308516743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23591842992565019489377981 8846941122211882308516743)
            ·
              refine ⟨13270411683317823462775115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8846941122211882308516743 13270411683317823462775115)
              ·
                refine ⟨19905617524976735194162673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13270411683317823462775115 19905617524976735194162673)
                ·
                  refine ⟨14929213143732551395622005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19905617524976735194162673 14929213143732551395622005)
                  ·
                    refine ⟨1399613732224926693339563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14929213143732551395622005 1399613732224926693339563)
                    ·
                      rfl

theorem cell22_4088607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_4088607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088607 prefixEnd_4088607 := by exact prefixLift 4088607
  have htrace : WordTrace (prefixWord ++ tailWord_4088607) baseStart_4088607 baseEnd_4088607 := by
    simpa [prefixWord, tailWord_4088607, baseEnd_4088607] using wordTrace_append hprefix tailTrace_4088607
  have hstable : (prefixWord ++ tailWord_4088607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088607).length < 2 ^ (prefixWord ++ tailWord_4088607).sum := by decide
  have hdescent : baseEnd_4088607 < baseStart_4088607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088630 : List Nat := [5, 1, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_4088630 : Nat := 118140960795 + 4088630 * 2 ^ 59
def prefixEnd_4088630 : Nat := 4983230072969 + 3 ^ 40 * 4088630 * 2
def baseEnd_4088630 : Nat := 1399621605594962300014493

theorem tailTrace_4088630 : CollatzResearch.WordTrace tailWord_4088630 prefixEnd_4088630 1399621605594962300014493 := by
  unfold tailWord_4088630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320286698599954203500459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99416391451732844837338229 9320286698599954203500459)
  ·
    refine ⟨13980430047899931305250689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9320286698599954203500459 13980430047899931305250689)
    ·
      refine ⟨10485322535924948478938017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13980430047899931305250689 10485322535924948478938017)
      ·
        refine ⟨7863991901943711359203513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10485322535924948478938017 7863991901943711359203513)
        ·
          refine ⟨5897993926457783519402635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7863991901943711359203513 5897993926457783519402635)
          ·
            refine ⟨8846990889686675279103953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5897993926457783519402635 8846990889686675279103953)
            ·
              refine ⟨6635243167265006459327965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8846990889686675279103953 6635243167265006459327965)
              ·
                refine ⟨2488216187724377422247987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6635243167265006459327965 2488216187724377422247987)
                ·
                  refine ⟨3732324281586566133371981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488216187724377422247987 3732324281586566133371981)
                  ·
                    refine ⟨1399621605594962300014493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3732324281586566133371981 1399621605594962300014493)
                    ·
                      rfl

theorem cell22_4088630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_4088630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088630 prefixEnd_4088630 := by exact prefixLift 4088630
  have htrace : WordTrace (prefixWord ++ tailWord_4088630) baseStart_4088630 baseEnd_4088630 := by
    simpa [prefixWord, tailWord_4088630, baseEnd_4088630] using wordTrace_append hprefix tailTrace_4088630
  have hstable : (prefixWord ++ tailWord_4088630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088630).length < 2 ^ (prefixWord ++ tailWord_4088630).sum := by decide
  have hdescent : baseEnd_4088630 < baseStart_4088630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088639 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 1, 4]
def baseStart_4088639 : Nat := 118140960795 + 4088639 * 2 ^ 59
def prefixEnd_4088639 : Nat := 4983230072969 + 3 ^ 40 * 4088639 * 2
def baseEnd_4088639 : Nat := 1399624686478889276539465

theorem tailTrace_4088639 : CollatzResearch.WordTrace tailWord_4088639 prefixEnd_4088639 1399624686478889276539465 := by
  unfold tailWord_4088639
  simp only [CollatzResearch.WordTrace]
  refine ⟨149124915434566661793084971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99416610289711107862056647 149124915434566661793084971)
  ·
    refine ⟨223687373151849992689627457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149124915434566661793084971 223687373151849992689627457)
    ·
      refine ⟨167765529863887494517220593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223687373151849992689627457 167765529863887494517220593)
      ·
        refine ⟨125824147397915620887915445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167765529863887494517220593 125824147397915620887915445)
        ·
          refine ⟨11796013818554589458242073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125824147397915620887915445 11796013818554589458242073)
          ·
            refine ⟨8847010363915942093681555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11796013818554589458242073 8847010363915942093681555)
            ·
              refine ⟨13270515545873913140522333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8847010363915942093681555 13270515545873913140522333)
              ·
                refine ⟨4976443329702717427695875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13270515545873913140522333 4976443329702717427695875)
                ·
                  refine ⟨7464664994554076141543813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976443329702717427695875 7464664994554076141543813)
                  ·
                    refine ⟨1399624686478889276539465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7464664994554076141543813 1399624686478889276539465)
                    ·
                      rfl

theorem cell22_4088639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_4088639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088639 prefixEnd_4088639 := by exact prefixLift 4088639
  have htrace : WordTrace (prefixWord ++ tailWord_4088639) baseStart_4088639 baseEnd_4088639 := by
    simpa [prefixWord, tailWord_4088639, baseEnd_4088639] using wordTrace_append hprefix tailTrace_4088639
  have hstable : (prefixWord ++ tailWord_4088639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088639).length < 2 ^ (prefixWord ++ tailWord_4088639).sum := by decide
  have hdescent : baseEnd_4088639 < baseStart_4088639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088956 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_4088956 : Nat := 118140960795 + 4088956 * 2 ^ 59
def prefixEnd_4088956 : Nat := 4983230072969 + 3 ^ 40 * 4088956 * 2
def baseEnd_4088956 : Nat := 1399733202057206116363493

theorem tailTrace_4088956 : CollatzResearch.WordTrace tailWord_4088956 prefixEnd_4088956 1399733202057206116363493 := by
  unfold tailWord_4088956
  simp only [CollatzResearch.WordTrace]
  refine ⟨74568238687209112466187361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99424318249612149954916481 74568238687209112466187361)
  ·
    refine ⟨55926179015406834349640521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74568238687209112466187361 55926179015406834349640521)
    ·
      refine ⟨41944634261555125762230391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55926179015406834349640521 41944634261555125762230391)
      ·
        refine ⟨62916951392332688643345587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41944634261555125762230391 62916951392332688643345587)
        ·
          refine ⟨94375427088499032965018381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62916951392332688643345587 94375427088499032965018381)
          ·
            refine ⟨35390785158187137361881893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94375427088499032965018381 35390785158187137361881893)
            ·
              refine ⟨6635772217160088255352855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35390785158187137361881893 6635772217160088255352855)
              ·
                refine ⟨9953658325740132383029283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6635772217160088255352855 9953658325740132383029283)
                ·
                  refine ⟨14930487488610198574543925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9953658325740132383029283 14930487488610198574543925)
                  ·
                    refine ⟨1399733202057206116363493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14930487488610198574543925 1399733202057206116363493)
                    ·
                      rfl

theorem cell22_4088956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_4088956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088956 prefixEnd_4088956 := by exact prefixLift 4088956
  have htrace : WordTrace (prefixWord ++ tailWord_4088956) baseStart_4088956 baseEnd_4088956 := by
    simpa [prefixWord, tailWord_4088956, baseEnd_4088956] using wordTrace_append hprefix tailTrace_4088956
  have hstable : (prefixWord ++ tailWord_4088956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088956).length < 2 ^ (prefixWord ++ tailWord_4088956).sum := by decide
  have hdescent : baseEnd_4088956 < baseStart_4088956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088986 : List Nat := [3, 1, 1, 5, 1, 2, 9]
def baseStart_4088986 : Nat := 118140960795 + 4088986 * 2 ^ 59
def prefixEnd_4088986 : Nat := 4983230072969 + 3 ^ 40 * 4088986 * 2
def baseEnd_4088986 : Nat := 51842350802603556967163

theorem tailTrace_4088986 : CollatzResearch.WordTrace tailWord_4088986 prefixEnd_4088986 51842350802603556967163 := by
  unfold tailWord_4088986
  simp only [CollatzResearch.WordTrace]
  refine ⟨37284392891077385013991703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99425047709539693370644541 37284392891077385013991703)
  ·
    refine ⟨55926589336616077520987555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37284392891077385013991703 55926589336616077520987555)
    ·
      refine ⟨83889884004924116281481333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55926589336616077520987555 83889884004924116281481333)
      ·
        refine ⟨7864676625461635901388875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83889884004924116281481333 7864676625461635901388875)
        ·
          refine ⟨11797014938192453852083313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7864676625461635901388875 11797014938192453852083313)
          ·
            refine ⟨8847761203644340389062485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11797014938192453852083313 8847761203644340389062485)
            ·
              refine ⟨51842350802603556967163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8847761203644340389062485 51842350802603556967163)
              ·
                rfl

theorem cell22_4088986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 9].length) (baseStart_4088986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088986 prefixEnd_4088986 := by exact prefixLift 4088986
  have htrace : WordTrace (prefixWord ++ tailWord_4088986) baseStart_4088986 baseEnd_4088986 := by
    simpa [prefixWord, tailWord_4088986, baseEnd_4088986] using wordTrace_append hprefix tailTrace_4088986
  have hstable : (prefixWord ++ tailWord_4088986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088986).length < 2 ^ (prefixWord ++ tailWord_4088986).sum := by decide
  have hdescent : baseEnd_4088986 < baseStart_4088986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088990 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_4088990 : Nat := 118140960795 + 4088990 * 2 ^ 59
def prefixEnd_4088990 : Nat := 4983230072969 + 3 ^ 40 * 4088990 * 2
def baseEnd_4088990 : Nat := 1399744840952041361013389

theorem tailTrace_4088990 : CollatzResearch.WordTrace tailWord_4088990 prefixEnd_4088990 1399744840952041361013389 := by
  unfold tailWord_4088990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18642214682036881092389053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99425144970863365826074949 18642214682036881092389053)
  ·
    refine ⟨6990830505763830409645895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18642214682036881092389053 6990830505763830409645895)
    ·
      refine ⟨10486245758645745614468843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6990830505763830409645895 10486245758645745614468843)
      ·
        refine ⟨15729368637968618421703265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10486245758645745614468843 15729368637968618421703265)
        ·
          refine ⟨11797026478476463816277449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15729368637968618421703265 11797026478476463816277449)
          ·
            refine ⟨8847769858857347862208087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11797026478476463816277449 8847769858857347862208087)
            ·
              refine ⟨13271654788286021793312131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8847769858857347862208087 13271654788286021793312131)
              ·
                refine ⟨19907482182429032689968197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13271654788286021793312131 19907482182429032689968197)
                ·
                  refine ⟨3732652909205443629369037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19907482182429032689968197 3732652909205443629369037)
                  ·
                    refine ⟨1399744840952041361013389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3732652909205443629369037 1399744840952041361013389)
                    ·
                      rfl

theorem cell22_4088990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_4088990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4088990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4088990 prefixEnd_4088990 := by exact prefixLift 4088990
  have htrace : WordTrace (prefixWord ++ tailWord_4088990) baseStart_4088990 baseEnd_4088990 := by
    simpa [prefixWord, tailWord_4088990, baseEnd_4088990] using wordTrace_append hprefix tailTrace_4088990
  have hstable : (prefixWord ++ tailWord_4088990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088990).length < 2 ^ (prefixWord ++ tailWord_4088990).sum := by decide
  have hdescent : baseEnd_4088990 < baseStart_4088990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089026 : List Nat := [3, 5, 1, 1, 3, 1, 1, 3, 4]
def baseStart_4089026 : Nat := 118140960795 + 4089026 * 2 ^ 59
def prefixEnd_4089026 : Nat := 4983230072969 + 3 ^ 40 * 4089026 * 2
def baseEnd_4089026 : Nat := 466585721495916422371093

theorem tailTrace_4089026 : CollatzResearch.WordTrace tailWord_4089026 prefixEnd_4089026 466585721495916422371093 := by
  unfold tailWord_4089026
  simp only [CollatzResearch.WordTrace]
  refine ⟨37284757621041156721855733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99426020322776417924948621 37284757621041156721855733)
  ·
    refine ⟨3495446026972608442673975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37284757621041156721855733 3495446026972608442673975)
    ·
      refine ⟨5243169040458912664010963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3495446026972608442673975 5243169040458912664010963)
      ·
        refine ⟨7864753560688368996016445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243169040458912664010963 7864753560688368996016445)
        ·
          refine ⟨2949282585258138373506167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7864753560688368996016445 2949282585258138373506167)
          ·
            refine ⟨4423923877887207560259251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949282585258138373506167 4423923877887207560259251)
            ·
              refine ⟨6635885816830811340388877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423923877887207560259251 6635885816830811340388877)
              ·
                refine ⟨2488457181311554252645829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6635885816830811340388877 2488457181311554252645829)
                ·
                  refine ⟨466585721495916422371093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2488457181311554252645829 466585721495916422371093)
                  ·
                    rfl

theorem cell22_4089026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_4089026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089026 prefixEnd_4089026 := by exact prefixLift 4089026
  have htrace : WordTrace (prefixWord ++ tailWord_4089026) baseStart_4089026 baseEnd_4089026 := by
    simpa [prefixWord, tailWord_4089026, baseEnd_4089026] using wordTrace_append hprefix tailTrace_4089026
  have hstable : (prefixWord ++ tailWord_4089026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089026).length < 2 ^ (prefixWord ++ tailWord_4089026).sum := by decide
  have hdescent : baseEnd_4089026 < baseStart_4089026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089037 : List Nat := [1, 6, 2, 2, 2, 1, 8]
def baseStart_4089037 : Nat := 118140960795 + 4089037 * 2 ^ 59
def prefixEnd_4089037 : Nat := 4983230072969 + 3 ^ 40 * 4089037 * 2
def baseEnd_4089037 : Nat := 51842997407872181669935

theorem tailTrace_4089037 : CollatzResearch.WordTrace tailWord_4089037 prefixEnd_4089037 51842997407872181669935 := by
  unfold tailWord_4089037
  simp only [CollatzResearch.WordTrace]
  refine ⟨149139431687124775766073365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99426287791416517177382243 149139431687124775766073365)
  ·
    refine ⟨6990910860333973864034689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149139431687124775766073365 6990910860333973864034689)
    ·
      refine ⟨5243183145250480398026017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6990910860333973864034689 5243183145250480398026017)
      ·
        refine ⟨3932387358937860298519513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5243183145250480398026017 3932387358937860298519513)
        ·
          refine ⟨2949290519203395223889635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3932387358937860298519513 2949290519203395223889635)
          ·
            refine ⟨4423935778805092835834453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949290519203395223889635 4423935778805092835834453)
            ·
              refine ⟨51842997407872181669935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4423935778805092835834453 51842997407872181669935)
              ·
                rfl

theorem cell22_4089037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 8].length) (baseStart_4089037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089037 prefixEnd_4089037 := by exact prefixLift 4089037
  have htrace : WordTrace (prefixWord ++ tailWord_4089037) baseStart_4089037 baseEnd_4089037 := by
    simpa [prefixWord, tailWord_4089037, baseEnd_4089037] using wordTrace_append hprefix tailTrace_4089037
  have hstable : (prefixWord ++ tailWord_4089037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089037).length < 2 ^ (prefixWord ++ tailWord_4089037).sum := by decide
  have hdescent : baseEnd_4089037 < baseStart_4089037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089091 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 3, 5]
def baseStart_4089091 : Nat := 118140960795 + 4089091 * 2 ^ 59
def prefixEnd_4089091 : Nat := 4983230072969 + 3 ^ 40 * 4089091 * 2
def baseEnd_4089091 : Nat := 1399779415316110764238079

theorem tailTrace_4089091 : CollatzResearch.WordTrace tailWord_4089091 prefixEnd_4089091 1399779415316110764238079 := by
  unfold tailWord_4089091
  simp only [CollatzResearch.WordTrace]
  refine ⟨149141401228929142988539127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99427600819286095325692751 149141401228929142988539127)
  ·
    refine ⟨223712101843393714482808691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149141401228929142988539127 223712101843393714482808691)
    ·
      refine ⟨335568152765090571724213037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223712101843393714482808691 335568152765090571724213037)
      ·
        refine ⟨125838057286908964396579889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335568152765090571724213037 125838057286908964396579889)
        ·
          refine ⟨94378542965181723297434917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125838057286908964396579889 94378542965181723297434917)
          ·
            refine ⟨17695976805971573118269047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94378542965181723297434917 17695976805971573118269047)
            ·
              refine ⟨26543965208957359677403571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17695976805971573118269047 26543965208957359677403571)
              ·
                refine ⟨39815947813436039516105357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26543965208957359677403571 39815947813436039516105357)
                ·
                  refine ⟨14930980430038514818539509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39815947813436039516105357 14930980430038514818539509)
                  ·
                    refine ⟨1399779415316110764238079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14930980430038514818539509 1399779415316110764238079)
                    ·
                      rfl

theorem cell22_4089091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_4089091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089091 prefixEnd_4089091 := by exact prefixLift 4089091
  have htrace : WordTrace (prefixWord ++ tailWord_4089091) baseStart_4089091 baseEnd_4089091 := by
    simpa [prefixWord, tailWord_4089091, baseEnd_4089091] using wordTrace_append hprefix tailTrace_4089091
  have hstable : (prefixWord ++ tailWord_4089091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089091).length < 2 ^ (prefixWord ++ tailWord_4089091).sum := by decide
  have hdescent : baseEnd_4089091 < baseStart_4089091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089093 : List Nat := [1, 3, 1, 1, 2, 1, 4, 5, 4]
def baseStart_4089093 : Nat := 118140960795 + 4089093 * 2 ^ 59
def prefixEnd_4089093 : Nat := 4983230072969 + 3 ^ 40 * 4089093 * 2
def baseEnd_4089093 : Nat := 466593366652327808562691

theorem tailTrace_4089093 : CollatzResearch.WordTrace tailWord_4089093 prefixEnd_4089093 466593366652327808562691 := by
  unfold tailWord_4089093
  simp only [CollatzResearch.WordTrace]
  refine ⟨149141474174921897330111933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99427649449947931553407955 149141474174921897330111933)
  ·
    refine ⟨55928052815595711498791975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149141474174921897330111933 55928052815595711498791975)
    ·
      refine ⟨83892079223393567248187963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55928052815595711498791975 83892079223393567248187963)
      ·
        refine ⟨125838118835090350872281945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83892079223393567248187963 125838118835090350872281945)
        ·
          refine ⟨94378589126317763154211459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125838118835090350872281945 94378589126317763154211459)
          ·
            refine ⟨141567883689476644731317189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94378589126317763154211459 141567883689476644731317189)
            ·
              refine ⟨26543978191776870887121973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141567883689476644731317189 26543978191776870887121973)
              ·
                refine ⟨2488497955479081645667685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26543978191776870887121973 2488497955479081645667685)
                ·
                  refine ⟨466593366652327808562691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2488497955479081645667685 466593366652327808562691)
                  ·
                    rfl

theorem cell22_4089093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_4089093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089093 prefixEnd_4089093 := by exact prefixLift 4089093
  have htrace : WordTrace (prefixWord ++ tailWord_4089093) baseStart_4089093 baseEnd_4089093 := by
    simpa [prefixWord, tailWord_4089093, baseEnd_4089093] using wordTrace_append hprefix tailTrace_4089093
  have hstable : (prefixWord ++ tailWord_4089093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089093).length < 2 ^ (prefixWord ++ tailWord_4089093).sum := by decide
  have hdescent : baseEnd_4089093 < baseStart_4089093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089125 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 2, 3]
def baseStart_4089125 : Nat := 118140960795 + 4089125 * 2 ^ 59
def prefixEnd_4089125 : Nat := 4983230072969 + 3 ^ 40 * 4089125 * 2
def baseEnd_4089125 : Nat := 1399791054210946008887975

theorem tailTrace_4089125 : CollatzResearch.WordTrace tailWord_4089125 prefixEnd_4089125 1399791054210946008887975 := by
  unfold tailWord_4089125
  simp only [CollatzResearch.WordTrace]
  refine ⟨149142641310805966795276829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99428427540537311196851219 149142641310805966795276829)
  ·
    refine ⟨55928490491552237548228811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149142641310805966795276829 55928490491552237548228811)
    ·
      refine ⟨83892735737328356322343217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55928490491552237548228811 83892735737328356322343217)
      ·
        refine ⟨62919551802996267241757413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83892735737328356322343217 62919551802996267241757413)
        ·
          refine ⟨11797415963061800107829515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62919551802996267241757413 11797415963061800107829515)
          ·
            refine ⟨17696123944592700161744273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11797415963061800107829515 17696123944592700161744273)
            ·
              refine ⟨13272092958444525121308205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17696123944592700161744273 13272092958444525121308205)
              ·
                refine ⟨4977034859416696920490577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13272092958444525121308205 4977034859416696920490577)
                ·
                  refine ⟨3732776144562522690367933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4977034859416696920490577 3732776144562522690367933)
                  ·
                    refine ⟨1399791054210946008887975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3732776144562522690367933 1399791054210946008887975)
                    ·
                      rfl

theorem cell22_4089125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_4089125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089125 prefixEnd_4089125 := by exact prefixLift 4089125
  have htrace : WordTrace (prefixWord ++ tailWord_4089125) baseStart_4089125 baseEnd_4089125 := by
    simpa [prefixWord, tailWord_4089125, baseEnd_4089125] using wordTrace_append hprefix tailTrace_4089125
  have hstable : (prefixWord ++ tailWord_4089125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089125).length < 2 ^ (prefixWord ++ tailWord_4089125).sum := by decide
  have hdescent : baseEnd_4089125 < baseStart_4089125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089247 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 1, 4]
def baseStart_4089247 : Nat := 118140960795 + 4089247 * 2 ^ 59
def prefixEnd_4089247 : Nat := 4983230072969 + 3 ^ 40 * 4089247 * 2
def baseEnd_4089247 : Nat := 1399832817304178357337601

theorem tailTrace_4089247 : CollatzResearch.WordTrace tailWord_4089247 prefixEnd_4089247 1399832817304178357337601 := by
  unfold tailWord_4089247
  simp only [CollatzResearch.WordTrace]
  refine ⟨149147091016363981631217995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99431394010909321087478663 149147091016363981631217995)
  ·
    refine ⟨223720636524545972446826993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149147091016363981631217995 223720636524545972446826993)
    ·
      refine ⟨167790477393409479335120245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223720636524545972446826993 167790477393409479335120245)
      ·
        refine ⟨15730357255632138687667523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167790477393409479335120245 15730357255632138687667523)
        ·
          refine ⟨23595535883448208031501285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15730357255632138687667523 23595535883448208031501285)
          ·
            refine ⟨4424162978146539005906491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23595535883448208031501285 4424162978146539005906491)
            ·
              refine ⟨6636244467219808508859737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424162978146539005906491 6636244467219808508859737)
              ·
                refine ⟨4977183350414856381644803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6636244467219808508859737 4977183350414856381644803)
                ·
                  refine ⟨7465775025622284572467205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4977183350414856381644803 7465775025622284572467205)
                  ·
                    refine ⟨1399832817304178357337601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7465775025622284572467205 1399832817304178357337601)
                    ·
                      rfl

theorem cell22_4089247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 4].length) (baseStart_4089247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089247 prefixEnd_4089247 := by exact prefixLift 4089247
  have htrace : WordTrace (prefixWord ++ tailWord_4089247) baseStart_4089247 baseEnd_4089247 := by
    simpa [prefixWord, tailWord_4089247, baseEnd_4089247] using wordTrace_append hprefix tailTrace_4089247
  have hstable : (prefixWord ++ tailWord_4089247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089247).length < 2 ^ (prefixWord ++ tailWord_4089247).sum := by decide
  have hdescent : baseEnd_4089247 < baseStart_4089247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089273 : List Nat := [1, 2, 1, 4, 4, 10]
def baseStart_4089273 : Nat := 118140960795 + 4089273 * 2 ^ 59
def prefixEnd_4089273 : Nat := 4983230072969 + 3 ^ 40 * 4089273 * 2
def baseEnd_4089273 : Nat := 17281996514018801928241

theorem tailTrace_4089273 : CollatzResearch.WordTrace tailWord_4089273 prefixEnd_4089273 17281996514018801928241 := by
  unfold tailWord_4089273
  simp only [CollatzResearch.WordTrace]
  refine ⟨149148039314269788071664473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99432026209513192047776315 149148039314269788071664473)
  ·
    refine ⟨111861029485702341053748355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149148039314269788071664473 111861029485702341053748355)
    ·
      refine ⟨167791544228553511580622533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111861029485702341053748355 167791544228553511580622533)
      ·
        refine ⟨31460914542853783421366725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167791544228553511580622533 31460914542853783421366725)
        ·
          refine ⟨5898921476785084391506261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31460914542853783421366725 5898921476785084391506261)
          ·
            refine ⟨17281996514018801928241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5898921476785084391506261 17281996514018801928241)
            ·
              rfl

theorem cell22_4089273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 10].length) (baseStart_4089273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089273 prefixEnd_4089273 := by exact prefixLift 4089273
  have htrace : WordTrace (prefixWord ++ tailWord_4089273) baseStart_4089273 baseEnd_4089273 := by
    simpa [prefixWord, tailWord_4089273, baseEnd_4089273] using wordTrace_append hprefix tailTrace_4089273
  have hstable : (prefixWord ++ tailWord_4089273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089273).length < 2 ^ (prefixWord ++ tailWord_4089273).sum := by decide
  have hdescent : baseEnd_4089273 < baseStart_4089273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089277 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_4089277 : Nat := 118140960795 + 4089277 * 2 ^ 59
def prefixEnd_4089277 : Nat := 4983230072969 + 3 ^ 40 * 4089277 * 2
def baseEnd_4089277 : Nat := 1399843086917268279087509

theorem tailTrace_4089277 : CollatzResearch.WordTrace tailWord_4089277 prefixEnd_4089277 1399843086917268279087509 := by
  unfold tailWord_4089277
  simp only [CollatzResearch.WordTrace]
  refine ⟨149148185206255296754810085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99432123470836864503206723 149148185206255296754810085)
  ·
    refine ⟨27965284726172868141526891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149148185206255296754810085 27965284726172868141526891)
    ·
      refine ⟨41947927089259302212290337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27965284726172868141526891 41947927089259302212290337)
      ·
        refine ⟨31460945316944476659217753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41947927089259302212290337 31460945316944476659217753)
        ·
          refine ⟨23595708987708357494413315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31460945316944476659217753 23595708987708357494413315)
          ·
            refine ⟨35393563481562536241619973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23595708987708357494413315 35393563481562536241619973)
            ·
              refine ⟨6636293152792975545303745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35393563481562536241619973 6636293152792975545303745)
              ·
                refine ⟨4977219864594731658977809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6636293152792975545303745 4977219864594731658977809)
                ·
                  refine ⟨3732914898446048744233357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4977219864594731658977809 3732914898446048744233357)
                  ·
                    refine ⟨1399843086917268279087509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3732914898446048744233357 1399843086917268279087509)
                    ·
                      rfl

theorem cell22_4089277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_4089277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089277 prefixEnd_4089277 := by exact prefixLift 4089277
  have htrace : WordTrace (prefixWord ++ tailWord_4089277) baseStart_4089277 baseEnd_4089277 := by
    simpa [prefixWord, tailWord_4089277, baseEnd_4089277] using wordTrace_append hprefix tailTrace_4089277
  have hstable : (prefixWord ++ tailWord_4089277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089277).length < 2 ^ (prefixWord ++ tailWord_4089277).sum := by decide
  have hdescent : baseEnd_4089277 < baseStart_4089277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089290 : List Nat := [3, 1, 2, 1, 2, 5, 1, 7]
def baseStart_4089290 : Nat := 118140960795 + 4089290 * 2 ^ 59
def prefixEnd_4089290 : Nat := 4983230072969 + 3 ^ 40 * 4089290 * 2
def baseEnd_4089290 : Nat := 155538615231437842056941

theorem tailTrace_4089290 : CollatzResearch.WordTrace tailWord_4089290 prefixEnd_4089290 155538615231437842056941 := by
  unfold tailWord_4089290
  simp only [CollatzResearch.WordTrace]
  refine ⟨37287164838802049993758331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99432439570138799983355549 37287164838802049993758331)
  ·
    refine ⟨55930747258203074990637497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37287164838802049993758331 55930747258203074990637497)
    ·
      refine ⟨41948060443652306242978123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55930747258203074990637497 41948060443652306242978123)
      ·
        refine ⟨62922090665478459364467185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41948060443652306242978123 62922090665478459364467185)
        ·
          refine ⟨47191567999108844523350389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62922090665478459364467185 47191567999108844523350389)
          ·
            refine ⟨4424209499916454174064099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47191567999108844523350389 4424209499916454174064099)
            ·
              refine ⟨6636314249874681261096149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424209499916454174064099 6636314249874681261096149)
              ·
                refine ⟨155538615231437842056941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6636314249874681261096149 155538615231437842056941)
                ·
                  rfl

theorem cell22_4089290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_4089290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089290 prefixEnd_4089290 := by exact prefixLift 4089290
  have htrace : WordTrace (prefixWord ++ tailWord_4089290) baseStart_4089290 baseEnd_4089290 := by
    simpa [prefixWord, tailWord_4089290, baseEnd_4089290] using wordTrace_append hprefix tailTrace_4089290
  have hstable : (prefixWord ++ tailWord_4089290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089290).length < 2 ^ (prefixWord ++ tailWord_4089290).sum := by decide
  have hdescent : baseEnd_4089290 < baseStart_4089290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089305 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 5, 3]
def baseStart_4089305 : Nat := 118140960795 + 4089305 * 2 ^ 59
def prefixEnd_4089305 : Nat := 4983230072969 + 3 ^ 40 * 4089305 * 2
def baseEnd_4089305 : Nat := 1399852671889485539387423

theorem tailTrace_4089305 : CollatzResearch.WordTrace tailWord_4089305 prefixEnd_4089305 1399852671889485539387423 := by
  unfold tailWord_4089305
  simp only [CollatzResearch.WordTrace]
  refine ⟨149149206450153857536829369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99432804300102571691219579 149149206450153857536829369)
  ·
    refine ⟨111861904837615393152622027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149149206450153857536829369 111861904837615393152622027)
    ·
      refine ⟨167792857256423089728933041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111861904837615393152622027 167792857256423089728933041)
      ·
        refine ⟨125844642942317317296699781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167792857256423089728933041 125844642942317317296699781)
        ·
          refine ⟨23595870551684496993131209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125844642942317317296699781 23595870551684496993131209)
          ·
            refine ⟨17696902913763372744848407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23595870551684496993131209 17696902913763372744848407)
            ·
              refine ⟨26545354370645059117272611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17696902913763372744848407 26545354370645059117272611)
              ·
                refine ⟨39818031555967588675908917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26545354370645059117272611 39818031555967588675908917)
                ·
                  refine ⟨3732940458371961438366461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39818031555967588675908917 3732940458371961438366461)
                  ·
                    refine ⟨1399852671889485539387423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3732940458371961438366461 1399852671889485539387423)
                    ·
                      rfl

theorem cell22_4089305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 3].length) (baseStart_4089305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089305 prefixEnd_4089305 := by exact prefixLift 4089305
  have htrace : WordTrace (prefixWord ++ tailWord_4089305) baseStart_4089305 baseEnd_4089305 := by
    simpa [prefixWord, tailWord_4089305, baseEnd_4089305] using wordTrace_append hprefix tailTrace_4089305
  have hstable : (prefixWord ++ tailWord_4089305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089305).length < 2 ^ (prefixWord ++ tailWord_4089305).sum := by decide
  have hdescent : baseEnd_4089305 < baseStart_4089305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089397 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 6]
def baseStart_4089397 : Nat := 118140960795 + 4089397 * 2 ^ 59
def prefixEnd_4089397 : Nat := 4983230072969 + 3 ^ 40 * 4089397 * 2
def baseEnd_4089397 : Nat := 466628055123209322029047

theorem tailTrace_4089397 : CollatzResearch.WordTrace tailWord_4089397 prefixEnd_4089397 466628055123209322029047 := by
  unfold tailWord_4089397
  simp only [CollatzResearch.WordTrace]
  refine ⟨149152561965820557249178445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99435041310547038166118963 149152561965820557249178445)
  ·
    refine ⟨55932210737182708968441917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149152561965820557249178445 55932210737182708968441917)
    ·
      refine ⟨20974579026443515863165719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55932210737182708968441917 20974579026443515863165719)
      ·
        refine ⟨31461868539665273794748579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20974579026443515863165719 31461868539665273794748579)
        ·
          refine ⟨47192802809497910692122869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31461868539665273794748579 47192802809497910692122869)
          ·
            refine ⟨4424325263390429127386519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47192802809497910692122869 4424325263390429127386519)
            ·
              refine ⟨6636487895085643691079779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424325263390429127386519 6636487895085643691079779)
              ·
                refine ⟨9954731842628465536619669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636487895085643691079779 9954731842628465536619669)
                ·
                  refine ⟨466628055123209322029047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9954731842628465536619669 466628055123209322029047)
                  ·
                    rfl

theorem cell22_4089397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_4089397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089397 prefixEnd_4089397 := by exact prefixLift 4089397
  have htrace : WordTrace (prefixWord ++ tailWord_4089397) baseStart_4089397 baseEnd_4089397 := by
    simpa [prefixWord, tailWord_4089397, baseEnd_4089397] using wordTrace_append hprefix tailTrace_4089397
  have hstable : (prefixWord ++ tailWord_4089397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089397).length < 2 ^ (prefixWord ++ tailWord_4089397).sum := by decide
  have hdescent : baseEnd_4089397 < baseStart_4089397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089504 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 5]
def baseStart_4089504 : Nat := 118140960795 + 4089504 * 2 ^ 59
def prefixEnd_4089504 : Nat := 4983230072969 + 3 ^ 40 * 4089504 * 2
def baseEnd_4089504 : Nat := 466640264552105117887271

theorem tailTrace_4089504 : CollatzResearch.WordTrace tailWord_4089504 prefixEnd_4089504 466640264552105117887271 := by
  unfold tailWord_4089504
  simp only [CollatzResearch.WordTrace]
  refine ⟨74578232288216457261661783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99437643050955276348882377 74578232288216457261661783)
  ·
    refine ⟨111867348432324685892492675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74578232288216457261661783 111867348432324685892492675)
    ·
      refine ⟨167801022648487028838739013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111867348432324685892492675 167801022648487028838739013)
      ·
        refine ⟨31462691746591317907263565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167801022648487028838739013 31462691746591317907263565)
        ·
          refine ⟨11798509404971744215223837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31462691746591317907263565 11798509404971744215223837)
          ·
            refine ⟨4424441026864404080708939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11798509404971744215223837 4424441026864404080708939)
            ·
              refine ⟨6636661540296606121063409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424441026864404080708939 6636661540296606121063409)
              ·
                refine ⟨4977496155222454590797557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6636661540296606121063409 4977496155222454590797557)
                ·
                  refine ⟨466640264552105117887271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4977496155222454590797557 466640264552105117887271)
                  ·
                    rfl

theorem cell22_4089504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 5].length) (baseStart_4089504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089504 prefixEnd_4089504 := by exact prefixLift 4089504
  have htrace : WordTrace (prefixWord ++ tailWord_4089504) baseStart_4089504 baseEnd_4089504 := by
    simpa [prefixWord, tailWord_4089504, baseEnd_4089504] using wordTrace_append hprefix tailTrace_4089504
  have hstable : (prefixWord ++ tailWord_4089504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089504).length < 2 ^ (prefixWord ++ tailWord_4089504).sum := by decide
  have hdescent : baseEnd_4089504 < baseStart_4089504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089532 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 6]
def baseStart_4089532 : Nat := 118140960795 + 4089532 * 2 ^ 59
def prefixEnd_4089532 : Nat := 4983230072969 + 3 ^ 40 * 4089532 * 2
def baseEnd_4089532 : Nat := 466643459542844204653909

theorem tailTrace_4089532 : CollatzResearch.WordTrace tailWord_4089532 prefixEnd_4089532 466643459542844204653909 := by
  unfold tailWord_4089532
  simp only [CollatzResearch.WordTrace]
  refine ⟨74578742910165737652671425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99438323880220983536895233 74578742910165737652671425)
  ·
    refine ⟨55934057182624303239503569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74578742910165737652671425 55934057182624303239503569)
    ·
      refine ⟨41950542886968227429627677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55934057182624303239503569 41950542886968227429627677)
      ·
        refine ⟨15731453582613085286110379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41950542886968227429627677 15731453582613085286110379)
        ·
          refine ⟨23597180373919627929165569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15731453582613085286110379 23597180373919627929165569)
          ·
            refine ⟨17697885280439720946874177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23597180373919627929165569 17697885280439720946874177)
            ·
              refine ⟨13273413960329790710155633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17697885280439720946874177 13273413960329790710155633)
              ·
                refine ⟨9955060470247343032616725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13273413960329790710155633 9955060470247343032616725)
                ·
                  refine ⟨466643459542844204653909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9955060470247343032616725 466643459542844204653909)
                  ·
                    rfl

theorem cell22_4089532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_4089532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089532 prefixEnd_4089532 := by exact prefixLift 4089532
  have htrace : WordTrace (prefixWord ++ tailWord_4089532) baseStart_4089532 baseEnd_4089532 := by
    simpa [prefixWord, tailWord_4089532, baseEnd_4089532] using wordTrace_append hprefix tailTrace_4089532
  have hstable : (prefixWord ++ tailWord_4089532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089532).length < 2 ^ (prefixWord ++ tailWord_4089532).sum := by decide
  have hdescent : baseEnd_4089532 < baseStart_4089532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089534 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_4089534 : Nat := 118140960795 + 4089534 * 2 ^ 59
def prefixEnd_4089534 : Nat := 4983230072969 + 3 ^ 40 * 4089534 * 2
def baseEnd_4089534 : Nat := 1399931063269405275411721

theorem tailTrace_4089534 : CollatzResearch.WordTrace tailWord_4089534 prefixEnd_4089534 1399931063269405275411721 := by
  unfold tailWord_4089534
  simp only [CollatzResearch.WordTrace]
  refine ⟨18644694845790528705864457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99438372510882819764610437 18644694845790528705864457)
  ·
    refine ⟨13983521134342896529398343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18644694845790528705864457 13983521134342896529398343)
    ·
      refine ⟨20975281701514344794097515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13983521134342896529398343 20975281701514344794097515)
      ·
        refine ⟨31462922552271517191146273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20975281701514344794097515 31462922552271517191146273)
        ·
          refine ⟨23597191914203637893359705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31462922552271517191146273 23597191914203637893359705)
          ·
            refine ⟨17697893935652728420019779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23597191914203637893359705 17697893935652728420019779)
            ·
              refine ⟨26546840903479092630029669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17697893935652728420019779 26546840903479092630029669)
              ·
                refine ⟨4977532669402329868130563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26546840903479092630029669 4977532669402329868130563)
                ·
                  refine ⟨7466299004103494802195845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4977532669402329868130563 7466299004103494802195845)
                  ·
                    refine ⟨1399931063269405275411721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7466299004103494802195845 1399931063269405275411721)
                    ·
                      rfl

theorem cell22_4089534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_4089534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089534 prefixEnd_4089534 := by exact prefixLift 4089534
  have htrace : WordTrace (prefixWord ++ tailWord_4089534) baseStart_4089534 baseEnd_4089534 := by
    simpa [prefixWord, tailWord_4089534, baseEnd_4089534] using wordTrace_append hprefix tailTrace_4089534
  have hstable : (prefixWord ++ tailWord_4089534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089534).length < 2 ^ (prefixWord ++ tailWord_4089534).sum := by decide
  have hdescent : baseEnd_4089534 < baseStart_4089534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089542 : List Nat := [6, 1, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_4089542 : Nat := 118140960795 + 4089542 * 2 ^ 59
def prefixEnd_4089542 : Nat := 4983230072969 + 3 ^ 40 * 4089542 * 2
def baseEnd_4089542 : Nat := 1399933801832895921211697

theorem tailTrace_4089542 : CollatzResearch.WordTrace tailWord_4089542 prefixEnd_4089542 1399933801832895921211697 := by
  unfold tailWord_4089542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4661182829696726469162715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99438567033530164675471253 4661182829696726469162715)
  ·
    refine ⟨6991774244545089703744073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4661182829696726469162715 6991774244545089703744073)
    ·
      refine ⟨5243830683408817277808055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6991774244545089703744073 5243830683408817277808055)
      ·
        refine ⟨7865746025113225916712083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243830683408817277808055 7865746025113225916712083)
        ·
          refine ⟨11798619037669838875068125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7865746025113225916712083 11798619037669838875068125)
          ·
            refine ⟨4424482139126189578150547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11798619037669838875068125 4424482139126189578150547)
            ·
              refine ⟨6636723208689284367225821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424482139126189578150547 6636723208689284367225821)
              ·
                refine ⟨2488771203258481637709683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6636723208689284367225821 2488771203258481637709683)
                ·
                  refine ⟨3733156804887722456564525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488771203258481637709683 3733156804887722456564525)
                  ·
                    refine ⟨1399933801832895921211697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3733156804887722456564525 1399933801832895921211697)
                    ·
                      rfl

theorem cell22_4089542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_4089542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089542 prefixEnd_4089542 := by exact prefixLift 4089542
  have htrace : WordTrace (prefixWord ++ tailWord_4089542) baseStart_4089542 baseEnd_4089542 := by
    simpa [prefixWord, tailWord_4089542, baseEnd_4089542] using wordTrace_append hprefix tailTrace_4089542
  have hstable : (prefixWord ++ tailWord_4089542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089542).length < 2 ^ (prefixWord ++ tailWord_4089542).sum := by decide
  have hdescent : baseEnd_4089542 < baseStart_4089542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089562 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_4089562 : Nat := 118140960795 + 4089562 * 2 ^ 59
def prefixEnd_4089562 : Nat := 4983230072969 + 3 ^ 40 * 4089562 * 2
def baseEnd_4089562 : Nat := 1399940648241622535711635

theorem tailTrace_4089562 : CollatzResearch.WordTrace tailWord_4089562 prefixEnd_4089562 1399940648241622535711635 := by
  unfold tailWord_4089562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37289645002555697607233735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99439053340148526952623293 37289645002555697607233735)
  ·
    refine ⟨55934467503833546410850603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37289645002555697607233735 55934467503833546410850603)
    ·
      refine ⟨83901701255750319616275905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55934467503833546410850603 83901701255750319616275905)
      ·
        refine ⟨62926275941812739712206929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83901701255750319616275905 62926275941812739712206929)
        ·
          refine ⟨47194706956359554784155197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62926275941812739712206929 47194706956359554784155197)
          ·
            refine ⟨17698015108634833044058199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47194706956359554784155197 17698015108634833044058199)
            ·
              refine ⟨26547022662952249566087299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17698015108634833044058199 26547022662952249566087299)
              ·
                refine ⟨39820533994428374349130949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26547022662952249566087299 39820533994428374349130949)
                ·
                  refine ⟨7466350123955320190462053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39820533994428374349130949 7466350123955320190462053)
                  ·
                    refine ⟨1399940648241622535711635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7466350123955320190462053 1399940648241622535711635)
                    ·
                      rfl

theorem cell22_4089562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_4089562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089562 prefixEnd_4089562 := by exact prefixLift 4089562
  have htrace : WordTrace (prefixWord ++ tailWord_4089562) baseStart_4089562 baseEnd_4089562 := by
    simpa [prefixWord, tailWord_4089562, baseEnd_4089562] using wordTrace_append hprefix tailTrace_4089562
  have hstable : (prefixWord ++ tailWord_4089562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089562).length < 2 ^ (prefixWord ++ tailWord_4089562).sum := by decide
  have hdescent : baseEnd_4089562 < baseStart_4089562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089581 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_4089581 : Nat := 118140960795 + 4089581 * 2 ^ 59
def prefixEnd_4089581 : Nat := 4983230072969 + 3 ^ 40 * 4089581 * 2
def baseEnd_4089581 : Nat := 1399947152329912819486577

theorem tailTrace_4089581 : CollatzResearch.WordTrace tailWord_4089581 prefixEnd_4089581 1399947152329912819486577 := by
  unfold tailWord_4089581
  simp only [CollatzResearch.WordTrace]
  refine ⟨149159272997153956673876597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99439515331435971115917731 149159272997153956673876597)
  ·
    refine ⟨13983681843483183438175931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149159272997153956673876597 13983681843483183438175931)
    ·
      refine ⟨20975522765224775157263897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13983681843483183438175931 20975522765224775157263897)
      ·
        refine ⟨15731642073918581367947923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20975522765224775157263897 15731642073918581367947923)
        ·
          refine ⟨23597463110877872051921885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15731642073918581367947923 23597463110877872051921885)
          ·
            refine ⟨8849048666579202019470707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23597463110877872051921885 8849048666579202019470707)
            ·
              refine ⟨13273572999868803029206061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8849048666579202019470707 13273572999868803029206061)
              ·
                refine ⟨4977589874950801135952273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13273572999868803029206061 4977589874950801135952273)
                ·
                  refine ⟨3733192406213100851964205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4977589874950801135952273 3733192406213100851964205)
                  ·
                    refine ⟨1399947152329912819486577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3733192406213100851964205 1399947152329912819486577)
                    ·
                      rfl

theorem cell22_4089581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_4089581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089581 prefixEnd_4089581 := by exact prefixLift 4089581
  have htrace : WordTrace (prefixWord ++ tailWord_4089581) baseStart_4089581 baseEnd_4089581 := by
    simpa [prefixWord, tailWord_4089581, baseEnd_4089581] using wordTrace_append hprefix tailTrace_4089581
  have hstable : (prefixWord ++ tailWord_4089581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089581).length < 2 ^ (prefixWord ++ tailWord_4089581).sum := by decide
  have hdescent : baseEnd_4089581 < baseStart_4089581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089637 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_4089637 : Nat := 118140960795 + 4089637 * 2 ^ 59
def prefixEnd_4089637 : Nat := 4983230072969 + 3 ^ 40 * 4089637 * 2
def baseEnd_4089637 : Nat := 1399966322274347340086405

theorem tailTrace_4089637 : CollatzResearch.WordTrace tailWord_4089637 prefixEnd_4089637 1399966322274347340086405 := by
  unfold tailWord_4089637
  simp only [CollatzResearch.WordTrace]
  refine ⟨149161315484951078237915165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99440876989967385491943443 149161315484951078237915165)
  ·
    refine ⟨55935493306856654339218187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149161315484951078237915165 55935493306856654339218187)
    ·
      refine ⟨83903239960284981508827281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55935493306856654339218187 83903239960284981508827281)
      ·
        refine ⟨62927429970213736131620461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83903239960284981508827281 62927429970213736131620461)
        ·
          refine ⟨23597786238830151049357673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62927429970213736131620461 23597786238830151049357673)
          ·
            refine ⟨17698339679122613287018255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23597786238830151049357673 17698339679122613287018255)
            ·
              refine ⟨26547509518683919930527383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17698339679122613287018255 26547509518683919930527383)
              ·
                refine ⟨39821264278025879895791075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26547509518683919930527383 39821264278025879895791075)
                ·
                  refine ⟨59731896417038819843686613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39821264278025879895791075 59731896417038819843686613)
                  ·
                    refine ⟨1399966322274347340086405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59731896417038819843686613 1399966322274347340086405)
                    ·
                      rfl

theorem cell22_4089637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_4089637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089637 prefixEnd_4089637 := by exact prefixLift 4089637
  have htrace : WordTrace (prefixWord ++ tailWord_4089637) baseStart_4089637 baseEnd_4089637 := by
    simpa [prefixWord, tailWord_4089637, baseEnd_4089637] using wordTrace_append hprefix tailTrace_4089637
  have hstable : (prefixWord ++ tailWord_4089637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089637).length < 2 ^ (prefixWord ++ tailWord_4089637).sum := by decide
  have hdescent : baseEnd_4089637 < baseStart_4089637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089669 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_4089669 : Nat := 118140960795 + 4089669 * 2 ^ 59
def prefixEnd_4089669 : Nat := 4983230072969 + 3 ^ 40 * 4089669 * 2
def baseEnd_4089669 : Nat := 1399977276528309923286307

theorem tailTrace_4089669 : CollatzResearch.WordTrace tailWord_4089669 prefixEnd_4089669 1399977276528309923286307 := by
  unfold tailWord_4089669
  simp only [CollatzResearch.WordTrace]
  refine ⟨149162482620835147703080061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99441655080556765135386707 149162482620835147703080061)
  ·
    refine ⟨55935930982813180388655023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149162482620835147703080061 55935930982813180388655023)
    ·
      refine ⟨83903896474219770582982535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55935930982813180388655023 83903896474219770582982535)
      ·
        refine ⟨125855844711329655874473803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83903896474219770582982535 125855844711329655874473803)
        ·
          refine ⟨188783767066994483811710705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125855844711329655874473803 188783767066994483811710705)
          ·
            refine ⟨141587825300245862858783029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188783767066994483811710705 141587825300245862858783029)
            ·
              refine ⟨13273858621898049643010909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141587825300245862858783029 13273858621898049643010909)
              ·
                refine ⟨4977696983211768616129091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13273858621898049643010909 4977696983211768616129091)
                ·
                  refine ⟨7466545474817652924193637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4977696983211768616129091 7466545474817652924193637)
                  ·
                    refine ⟨1399977276528309923286307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7466545474817652924193637 1399977276528309923286307)
                    ·
                      rfl

theorem cell22_4089669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_4089669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089669 prefixEnd_4089669 := by exact prefixLift 4089669
  have htrace : WordTrace (prefixWord ++ tailWord_4089669) baseStart_4089669 baseEnd_4089669 := by
    simpa [prefixWord, tailWord_4089669, baseEnd_4089669] using wordTrace_append hprefix tailTrace_4089669
  have hstable : (prefixWord ++ tailWord_4089669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089669).length < 2 ^ (prefixWord ++ tailWord_4089669).sum := by decide
  have hdescent : baseEnd_4089669 < baseStart_4089669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089684 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 6]
def baseStart_4089684 : Nat := 118140960795 + 4089684 * 2 ^ 59
def prefixEnd_4089684 : Nat := 4983230072969 + 3 ^ 40 * 4089684 * 2
def baseEnd_4089684 : Nat := 466660803778284961387087

theorem tailTrace_4089684 : CollatzResearch.WordTrace tailWord_4089684 prefixEnd_4089684 466660803778284961387087 := by
  unfold tailWord_4089684
  simp only [CollatzResearch.WordTrace]
  refine ⟨74581514857890402632438053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99442019810520536843250737 74581514857890402632438053)
  ·
    refine ⟨13984034035854450493582135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74581514857890402632438053 13984034035854450493582135)
    ·
      refine ⟨20976051053781675740373203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13984034035854450493582135 20976051053781675740373203)
      ·
        refine ⟨31464076580672513610559805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20976051053781675740373203 31464076580672513610559805)
        ·
          refine ⟨11799028717752192603959927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31464076580672513610559805 11799028717752192603959927)
          ·
            refine ⟨17698543076628288905939891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11799028717752192603959927 17698543076628288905939891)
            ·
              refine ⟨26547814614942433358909837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17698543076628288905939891 26547814614942433358909837)
              ·
                refine ⟨9955430480603412509591189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26547814614942433358909837 9955430480603412509591189)
                ·
                  refine ⟨466660803778284961387087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9955430480603412509591189 466660803778284961387087)
                  ·
                    rfl

theorem cell22_4089684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_4089684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089684 prefixEnd_4089684 := by exact prefixLift 4089684
  have htrace : WordTrace (prefixWord ++ tailWord_4089684) baseStart_4089684 baseEnd_4089684 := by
    simpa [prefixWord, tailWord_4089684, baseEnd_4089684] using wordTrace_append hprefix tailTrace_4089684
  have hstable : (prefixWord ++ tailWord_4089684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089684).length < 2 ^ (prefixWord ++ tailWord_4089684).sum := by decide
  have hdescent : baseEnd_4089684 < baseStart_4089684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089697 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_4089697 : Nat := 118140960795 + 4089697 * 2 ^ 59
def prefixEnd_4089697 : Nat := 4983230072969 + 3 ^ 40 * 4089697 * 2
def baseEnd_4089697 : Nat := 1399986861500527183586221

theorem tailTrace_4089697 : CollatzResearch.WordTrace tailWord_4089697 prefixEnd_4089697 1399986861500527183586221 := by
  unfold tailWord_4089697
  simp only [CollatzResearch.WordTrace]
  refine ⟨149163503864733708485099345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99442335909822472323399563 149163503864733708485099345)
  ·
    refine ⟨111872627898550281363824509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149163503864733708485099345 111872627898550281363824509)
    ·
      refine ⟨41952235461956355511434191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111872627898550281363824509 41952235461956355511434191)
      ·
        refine ⟨62928353192934533267151287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41952235461956355511434191 62928353192934533267151287)
        ·
          refine ⟨94392529789401799900726931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62928353192934533267151287 94392529789401799900726931)
          ·
            refine ⟨141588794684102699851090397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94392529789401799900726931 141588794684102699851090397)
            ·
              refine ⟨53095798006538512444158899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141588794684102699851090397 53095798006538512444158899)
              ·
                refine ⟨79643697009807768666238349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53095798006538512444158899 79643697009807768666238349)
                ·
                  refine ⟨29866386378677913249839381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79643697009807768666238349 29866386378677913249839381)
                  ·
                    refine ⟨1399986861500527183586221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29866386378677913249839381 1399986861500527183586221)
                    ·
                      rfl

theorem cell22_4089697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_4089697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089697 prefixEnd_4089697 := by exact prefixLift 4089697
  have htrace : WordTrace (prefixWord ++ tailWord_4089697) baseStart_4089697 baseEnd_4089697 := by
    simpa [prefixWord, tailWord_4089697, baseEnd_4089697] using wordTrace_append hprefix tailTrace_4089697
  have hstable : (prefixWord ++ tailWord_4089697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089697).length < 2 ^ (prefixWord ++ tailWord_4089697).sum := by decide
  have hdescent : baseEnd_4089697 < baseStart_4089697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089714 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_4089714 : Nat := 118140960795 + 4089714 * 2 ^ 59
def prefixEnd_4089714 : Nat := 4983230072969 + 3 ^ 40 * 4089714 * 2
def baseEnd_4089714 : Nat := 1399992680947944805911169

theorem tailTrace_4089714 : CollatzResearch.WordTrace tailWord_4089714 prefixEnd_4089714 1399992680947944805911169 := by
  unfold tailWord_4089714
  simp only [CollatzResearch.WordTrace]
  refine ⟨37291030976418030097117049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99442749270448080258978797 37291030976418030097117049)
  ·
    refine ⟨27968273232313522572837787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37291030976418030097117049 27968273232313522572837787)
    ·
      refine ⟨41952409848470283859256681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27968273232313522572837787 41952409848470283859256681)
      ·
        refine ⟨31464307386352712894442511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41952409848470283859256681 31464307386352712894442511)
        ·
          refine ⟨47196461079529069341663767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31464307386352712894442511 47196461079529069341663767)
          ·
            refine ⟨70794691619293604012495651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47196461079529069341663767 70794691619293604012495651)
            ·
              refine ⟨106192037428940406018743477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70794691619293604012495651 106192037428940406018743477)
              ·
                refine ⟨9955503508963163064257201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106192037428940406018743477 9955503508963163064257201)
                ·
                  refine ⟨7466627631722372298192901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9955503508963163064257201 7466627631722372298192901)
                  ·
                    refine ⟨1399992680947944805911169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7466627631722372298192901 1399992680947944805911169)
                    ·
                      rfl

theorem cell22_4089714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_4089714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089714 prefixEnd_4089714 := by exact prefixLift 4089714
  have htrace : WordTrace (prefixWord ++ tailWord_4089714) baseStart_4089714 baseEnd_4089714 := by
    simpa [prefixWord, tailWord_4089714, baseEnd_4089714] using wordTrace_append hprefix tailTrace_4089714
  have hstable : (prefixWord ++ tailWord_4089714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089714).length < 2 ^ (prefixWord ++ tailWord_4089714).sum := by decide
  have hdescent : baseEnd_4089714 < baseStart_4089714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089746 : List Nat := [3, 2, 3, 2, 1, 2, 2, 7]
def baseStart_4089746 : Nat := 118140960795 + 4089746 * 2 ^ 59
def prefixEnd_4089746 : Nat := 4983230072969 + 3 ^ 40 * 4089746 * 2
def baseEnd_4089746 : Nat := 155555959466878598790119

theorem tailTrace_4089746 : CollatzResearch.WordTrace tailWord_4089746 prefixEnd_4089746 155555959466878598790119 := by
  unfold tailWord_4089746
  simp only [CollatzResearch.WordTrace]
  refine ⟨37291322760389047463408273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99443527361037459902422061 37291322760389047463408273)
  ·
    refine ⟨27968492070291785597556205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37291322760389047463408273 27968492070291785597556205)
    ·
      refine ⟨10488184526359419599083577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27968492070291785597556205 10488184526359419599083577)
      ·
        refine ⟨7866138394769564699312683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10488184526359419599083577 7866138394769564699312683)
        ·
          refine ⟨11799207592154347048969025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7866138394769564699312683 11799207592154347048969025)
          ·
            refine ⟨8849405694115760286726769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11799207592154347048969025 8849405694115760286726769)
            ·
              refine ⟨6637054270586820215045077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8849405694115760286726769 6637054270586820215045077)
              ·
                refine ⟨155555959466878598790119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6637054270586820215045077 155555959466878598790119)
                ·
                  rfl

theorem cell22_4089746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_4089746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089746 prefixEnd_4089746 := by exact prefixLift 4089746
  have htrace : WordTrace (prefixWord ++ tailWord_4089746) baseStart_4089746 baseEnd_4089746 := by
    simpa [prefixWord, tailWord_4089746, baseEnd_4089746] using wordTrace_append hprefix tailTrace_4089746
  have hstable : (prefixWord ++ tailWord_4089746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089746).length < 2 ^ (prefixWord ++ tailWord_4089746).sum := by decide
  have hdescent : baseEnd_4089746 < baseStart_4089746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089838 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_4089838 : Nat := 118140960795 + 4089838 * 2 ^ 59
def prefixEnd_4089838 : Nat := 4983230072969 + 3 ^ 40 * 4089838 * 2
def baseEnd_4089838 : Nat := 1400035128682049815810789

theorem tailTrace_4089838 : CollatzResearch.WordTrace tailWord_4089838 prefixEnd_4089838 1400035128682049815810789 := by
  unfold tailWord_4089838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18646080819652861195747771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99445764371481926377321445 18646080819652861195747771)
  ·
    refine ⟨27969121229479291793621657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18646080819652861195747771 27969121229479291793621657)
    ·
      refine ⟨20976840922109468845216243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27969121229479291793621657 20976840922109468845216243)
      ·
        refine ⟨31465261383164203267824365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20976840922109468845216243 31465261383164203267824365)
        ·
          refine ⟨11799473018686576225434137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31465261383164203267824365 11799473018686576225434137)
          ·
            refine ⟨8849604764014932169075603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11799473018686576225434137 8849604764014932169075603)
            ·
              refine ⟨13274407146022398253613405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8849604764014932169075603 13274407146022398253613405)
              ·
                refine ⟨4977902679758399345105027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13274407146022398253613405 4977902679758399345105027)
                ·
                  refine ⟨7466854019637599017657541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4977902679758399345105027 7466854019637599017657541)
                  ·
                    refine ⟨1400035128682049815810789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7466854019637599017657541 1400035128682049815810789)
                    ·
                      rfl

theorem cell22_4089838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_4089838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089838 prefixEnd_4089838 := by exact prefixLift 4089838
  have htrace : WordTrace (prefixWord ++ tailWord_4089838) baseStart_4089838 baseEnd_4089838 := by
    simpa [prefixWord, tailWord_4089838, baseEnd_4089838] using wordTrace_append hprefix tailTrace_4089838
  have hstable : (prefixWord ++ tailWord_4089838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089838).length < 2 ^ (prefixWord ++ tailWord_4089838).sum := by decide
  have hdescent : baseEnd_4089838 < baseStart_4089838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089864 : List Nat := [2, 1, 3, 2, 1, 2, 2, 9]
def baseStart_4089864 : Nat := 118140960795 + 4089864 * 2 ^ 59
def prefixEnd_4089864 : Nat := 4983230072969 + 3 ^ 40 * 4089864 * 2
def baseEnd_4089864 : Nat := 155560447668154934962301

theorem tailTrace_4089864 : CollatzResearch.WordTrace tailWord_4089864 prefixEnd_4089864 155560447668154934962301 := by
  unfold tailWord_4089864
  simp only [CollatzResearch.WordTrace]
  refine ⟨74584797427564348003214323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99446396570085797337619097 74584797427564348003214323)
  ·
    refine ⟨111877196141346522004821485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74584797427564348003214323 111877196141346522004821485)
    ·
      refine ⟨41953948553004945751808057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111877196141346522004821485 41953948553004945751808057)
      ·
        refine ⟨31465461414753709313856043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41953948553004945751808057 31465461414753709313856043)
        ·
          refine ⟨47198192122130563970784065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31465461414753709313856043 47198192122130563970784065)
          ·
            refine ⟨35398644091597922978088049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47198192122130563970784065 35398644091597922978088049)
            ·
              refine ⟨26548983068698442233566037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35398644091597922978088049 26548983068698442233566037)
              ·
                refine ⟨155560447668154934962301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26548983068698442233566037 155560447668154934962301)
                ·
                  rfl

theorem cell22_4089864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 9].length) (baseStart_4089864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4089864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4089864 prefixEnd_4089864 := by exact prefixLift 4089864
  have htrace : WordTrace (prefixWord ++ tailWord_4089864) baseStart_4089864 baseEnd_4089864 := by
    simpa [prefixWord, tailWord_4089864, baseEnd_4089864] using wordTrace_append hprefix tailTrace_4089864
  have hstable : (prefixWord ++ tailWord_4089864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089864).length < 2 ^ (prefixWord ++ tailWord_4089864).sum := by decide
  have hdescent : baseEnd_4089864 < baseStart_4089864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090007 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 1, 4]
def baseStart_4090007 : Nat := 118140960795 + 4090007 * 2 ^ 59
def prefixEnd_4090007 : Nat := 4983230072969 + 3 ^ 40 * 4090007 * 2
def baseEnd_4090007 : Nat := 1400092980835789708335271

theorem tailTrace_4090007 : CollatzResearch.WordTrace tailWord_4090007 prefixEnd_4090007 1400092980835789708335271 := by
  unfold tailWord_4090007
  simp only [CollatzResearch.WordTrace]
  refine ⟨149174810493610631428884275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99449873662407087619256183 149174810493610631428884275)
  ·
    refine ⟨223762215740415947143326413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149174810493610631428884275 223762215740415947143326413)
    ·
      refine ⟨83910830902655980178747405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223762215740415947143326413 83910830902655980178747405)
      ·
        refine ⟨31466561588495992567030277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83910830902655980178747405 31466561588495992567030277)
        ·
          refine ⟨5899980297842998606318177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31466561588495992567030277 5899980297842998606318177)
          ·
            refine ⟨4424985223382248954738633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5899980297842998606318177 4424985223382248954738633)
            ·
              refine ⟨3318738917536686716053975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4424985223382248954738633 3318738917536686716053975)
              ·
                refine ⟨4978108376305030074080963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3318738917536686716053975 4978108376305030074080963)
                ·
                  refine ⟨7467162564457545111121445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4978108376305030074080963 7467162564457545111121445)
                  ·
                    refine ⟨1400092980835789708335271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7467162564457545111121445 1400092980835789708335271)
                    ·
                      rfl

theorem cell22_4090007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_4090007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090007 prefixEnd_4090007 := by exact prefixLift 4090007
  have htrace : WordTrace (prefixWord ++ tailWord_4090007) baseStart_4090007 baseEnd_4090007 := by
    simpa [prefixWord, tailWord_4090007, baseEnd_4090007] using wordTrace_append hprefix tailTrace_4090007
  have hstable : (prefixWord ++ tailWord_4090007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090007).length < 2 ^ (prefixWord ++ tailWord_4090007).sum := by decide
  have hdescent : baseEnd_4090007 < baseStart_4090007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090016 : List Nat := [2, 1, 1, 4, 2, 3, 9]
def baseStart_4090016 : Nat := 118140960795 + 4090016 * 2 ^ 59
def prefixEnd_4090016 : Nat := 4983230072969 + 3 ^ 40 * 4090016 * 2
def baseEnd_4090016 : Nat := 51855409693322840180009

theorem tailTrace_4090016 : CollatzResearch.WordTrace tailWord_4090016 prefixEnd_4090016 51855409693322840180009 := by
  unfold tailWord_4090016
  simp only [CollatzResearch.WordTrace]
  refine ⟨74587569375289012982980951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99450092500385350643974601 74587569375289012982980951)
  ·
    refine ⟨111881354062933519474471427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74587569375289012982980951 111881354062933519474471427)
    ·
      refine ⟨167822031094400279211707141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111881354062933519474471427 167822031094400279211707141)
      ·
        refine ⟨31466630830200052352195089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167822031094400279211707141 31466630830200052352195089)
        ·
          refine ⟨23599973122650039264146317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31466630830200052352195089 23599973122650039264146317)
          ·
            refine ⟨8849989920993764724054869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23599973122650039264146317 8849989920993764724054869)
            ·
              refine ⟨51855409693322840180009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8849989920993764724054869 51855409693322840180009)
              ·
                rfl

theorem cell22_4090016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 9].length) (baseStart_4090016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090016 prefixEnd_4090016 := by exact prefixLift 4090016
  have htrace : WordTrace (prefixWord ++ tailWord_4090016) baseStart_4090016 baseEnd_4090016 := by
    simpa [prefixWord, tailWord_4090016, baseEnd_4090016] using wordTrace_append hprefix tailTrace_4090016
  have hstable : (prefixWord ++ tailWord_4090016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090016).length < 2 ^ (prefixWord ++ tailWord_4090016).sum := by decide
  have hdescent : baseEnd_4090016 < baseStart_4090016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090020 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_4090020 : Nat := 118140960795 + 4090020 * 2 ^ 59
def prefixEnd_4090020 : Nat := 4983230072969 + 3 ^ 40 * 4090020 * 2
def baseEnd_4090020 : Nat := 1400097431001462007760231

theorem tailTrace_4090020 : CollatzResearch.WordTrace tailWord_4090020 prefixEnd_4090020 1400097431001462007760231 := by
  unfold tailWord_4090020
  simp only [CollatzResearch.WordTrace]
  refine ⟨74587642321281767324553757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99450189761709023099405009 74587642321281767324553757)
  ·
    refine ⟨27970365870480662746707659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74587642321281767324553757 27970365870480662746707659)
    ·
      refine ⟨41955548805720994120061489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27970365870480662746707659 41955548805720994120061489)
      ·
        refine ⟨31466661604290745590046117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41955548805720994120061489 31466661604290745590046117)
        ·
          refine ⟨5899999050804514798133647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31466661604290745590046117 5899999050804514798133647)
          ·
            refine ⟨8849998576206772197200471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5899999050804514798133647 8849998576206772197200471)
            ·
              refine ⟨13274997864310158295800707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8849998576206772197200471 13274997864310158295800707)
              ·
                refine ⟨19912496796465237443701061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13274997864310158295800707 19912496796465237443701061)
                ·
                  refine ⟨3733593149337232020693949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19912496796465237443701061 3733593149337232020693949)
                  ·
                    refine ⟨1400097431001462007760231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3733593149337232020693949 1400097431001462007760231)
                    ·
                      rfl

theorem cell22_4090020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_4090020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090020 prefixEnd_4090020 := by exact prefixLift 4090020
  have htrace : WordTrace (prefixWord ++ tailWord_4090020) baseStart_4090020 baseEnd_4090020 := by
    simpa [prefixWord, tailWord_4090020, baseEnd_4090020] using wordTrace_append hprefix tailTrace_4090020
  have hstable : (prefixWord ++ tailWord_4090020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090020).length < 2 ^ (prefixWord ++ tailWord_4090020).sum := by decide
  have hdescent : baseEnd_4090020 < baseStart_4090020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090037 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 1, 5]
def baseStart_4090037 : Nat := 118140960795 + 4090037 * 2 ^ 59
def prefixEnd_4090037 : Nat := 4983230072969 + 3 ^ 40 * 4090037 * 2
def baseEnd_4090037 : Nat := 1400103250448879630085179

theorem tailTrace_4090037 : CollatzResearch.WordTrace tailWord_4090037 prefixEnd_4090037 1400103250448879630085179 := by
  unfold tailWord_4090037
  simp only [CollatzResearch.WordTrace]
  refine ⟨149175904683501946552476365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99450603122334631034984243 149175904683501946552476365)
  ·
    refine ⟨55940964256313229957178637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149175904683501946552476365 55940964256313229957178637)
    ·
      refine ⟨20977861596117461233941989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55940964256313229957178637 20977861596117461233941989)
      ·
        refine ⟨3933349049272023981364123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20977861596117461233941989 3933349049272023981364123)
        ·
          refine ⟨5900023573908035972046185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3933349049272023981364123 5900023573908035972046185)
          ·
            refine ⟨4425017680431026979034639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5900023573908035972046185 4425017680431026979034639)
            ·
              refine ⟨6637526520646540468551959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4425017680431026979034639 6637526520646540468551959)
              ·
                refine ⟨9956289780969810702827939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6637526520646540468551959 9956289780969810702827939)
                ·
                  refine ⟨14934434671454716054241909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9956289780969810702827939 14934434671454716054241909)
                  ·
                    refine ⟨1400103250448879630085179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14934434671454716054241909 1400103250448879630085179)
                    ·
                      rfl

theorem cell22_4090037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_4090037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090037 prefixEnd_4090037 := by exact prefixLift 4090037
  have htrace : WordTrace (prefixWord ++ tailWord_4090037) baseStart_4090037 baseEnd_4090037 := by
    simpa [prefixWord, tailWord_4090037, baseEnd_4090037] using wordTrace_append hprefix tailTrace_4090037
  have hstable : (prefixWord ++ tailWord_4090037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090037).length < 2 ^ (prefixWord ++ tailWord_4090037).sum := by decide
  have hdescent : baseEnd_4090037 < baseStart_4090037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090095 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 5]
def baseStart_4090095 : Nat := 118140960795 + 4090095 * 2 ^ 59
def prefixEnd_4090095 : Nat := 4983230072969 + 3 ^ 40 * 4090095 * 2
def baseEnd_4090095 : Nat := 466707701678062270711667

theorem tailTrace_4090095 : CollatzResearch.WordTrace tailWord_4090095 prefixEnd_4090095 466707701678062270711667 := by
  unfold tailWord_4090095
  simp only [CollatzResearch.WordTrace]
  refine ⟨149178020117291822458087739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99452013411527881638725159 149178020117291822458087739)
  ·
    refine ⟨223767030175937733687131609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149178020117291822458087739 223767030175937733687131609)
    ·
      refine ⟨167825272631953300265348707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223767030175937733687131609 167825272631953300265348707)
      ·
        refine ⟨251737908947929950398023061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167825272631953300265348707 251737908947929950398023061)
        ·
          refine ⟨11800214481934216424907331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251737908947929950398023061 11800214481934216424907331)
          ·
            refine ⟨17700321722901324637360997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11800214481934216424907331 17700321722901324637360997)
            ·
              refine ⟨3318810323043998369505187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17700321722901324637360997 3318810323043998369505187)
              ·
                refine ⟨4978215484565997554257781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3318810323043998369505187 4978215484565997554257781)
                ·
                  refine ⟨466707701678062270711667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4978215484565997554257781 466707701678062270711667)
                  ·
                    rfl

theorem cell22_4090095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 5].length) (baseStart_4090095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090095 prefixEnd_4090095 := by exact prefixLift 4090095
  have htrace : WordTrace (prefixWord ++ tailWord_4090095) baseStart_4090095 baseEnd_4090095 := by
    simpa [prefixWord, tailWord_4090095, baseEnd_4090095] using wordTrace_append hprefix tailTrace_4090095
  have hstable : (prefixWord ++ tailWord_4090095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090095).length < 2 ^ (prefixWord ++ tailWord_4090095).sum := by decide
  have hdescent : baseEnd_4090095 < baseStart_4090095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090142 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4090142 : Nat := 118140960795 + 4090142 * 2 ^ 59
def prefixEnd_4090142 : Nat := 4983230072969 + 3 ^ 40 * 4090142 * 2
def baseEnd_4090142 : Nat := 1400139194094694356209857

theorem tailTrace_4090142 : CollatzResearch.WordTrace tailWord_4090142 prefixEnd_4090142 1400139194094694356209857 := by
  unfold tailWord_4090142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18647466793515193685631085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99453156232081032990032453 18647466793515193685631085)
  ·
    refine ⟨6992800047568197632111657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18647466793515193685631085 6992800047568197632111657)
    ·
      refine ⟨5244600035676148224083743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6992800047568197632111657 5244600035676148224083743)
      ·
        refine ⟨7866900053514222336125615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5244600035676148224083743 7866900053514222336125615)
        ·
          refine ⟨11800350080271333504188423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7866900053514222336125615 11800350080271333504188423)
          ·
            refine ⟨17700525120407000256282635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11800350080271333504188423 17700525120407000256282635)
            ·
              refine ⟨26550787680610500384423953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17700525120407000256282635 26550787680610500384423953)
              ·
                refine ⟨19913090760457875288317965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26550787680610500384423953 19913090760457875288317965)
                ·
                  refine ⟨7467409035171703233119237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19913090760457875288317965 7467409035171703233119237)
                  ·
                    refine ⟨1400139194094694356209857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7467409035171703233119237 1400139194094694356209857)
                    ·
                      rfl

theorem cell22_4090142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4090142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090142 prefixEnd_4090142 := by exact prefixLift 4090142
  have htrace : WordTrace (prefixWord ++ tailWord_4090142) baseStart_4090142 baseEnd_4090142 := by
    simpa [prefixWord, tailWord_4090142, baseEnd_4090142] using wordTrace_append hprefix tailTrace_4090142
  have hstable : (prefixWord ++ tailWord_4090142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090142).length < 2 ^ (prefixWord ++ tailWord_4090142).sum := by decide
  have hdescent : baseEnd_4090142 < baseStart_4090142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090157 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 6]
def baseStart_4090157 : Nat := 118140960795 + 4090157 * 2 ^ 59
def prefixEnd_4090157 : Nat := 4983230072969 + 3 ^ 40 * 4090157 * 2
def baseEnd_4090157 : Nat := 466714776300413105694937

theorem tailTrace_4090157 : CollatzResearch.WordTrace tailWord_4090157 prefixEnd_4090157 466714776300413105694937 := by
  unfold tailWord_4090157
  simp only [CollatzResearch.WordTrace]
  refine ⟨149180281443067207046844725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99453520962044804697896483 149180281443067207046844725)
  ·
    refine ⟨13985651385287550660641693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149180281443067207046844725 13985651385287550660641693)
    ·
      refine ⟨5244619269482831497740635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13985651385287550660641693 5244619269482831497740635)
      ·
        refine ⟨7866928904224247246610953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5244619269482831497740635 7866928904224247246610953)
        ·
          refine ⟨5900196678168185434958215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7866928904224247246610953 5900196678168185434958215)
          ·
            refine ⟨8850295017252278152437323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5900196678168185434958215 8850295017252278152437323)
            ·
              refine ⟨13275442525878417228655985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8850295017252278152437323 13275442525878417228655985)
              ·
                refine ⟨9956581894408812921491989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13275442525878417228655985 9956581894408812921491989)
                ·
                  refine ⟨466714776300413105694937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9956581894408812921491989 466714776300413105694937)
                  ·
                    rfl

theorem cell22_4090157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_4090157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090157 prefixEnd_4090157 := by exact prefixLift 4090157
  have htrace : WordTrace (prefixWord ++ tailWord_4090157) baseStart_4090157 baseEnd_4090157 := by
    simpa [prefixWord, tailWord_4090157, baseEnd_4090157] using wordTrace_append hprefix tailTrace_4090157
  have hstable : (prefixWord ++ tailWord_4090157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090157).length < 2 ^ (prefixWord ++ tailWord_4090157).sum := by decide
  have hdescent : baseEnd_4090157 < baseStart_4090157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090170 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_4090170 : Nat := 118140960795 + 4090170 * 2 ^ 59
def prefixEnd_4090170 : Nat := 4983230072969 + 3 ^ 40 * 4090170 * 2
def baseEnd_4090170 : Nat := 1400148779066911616509771

theorem tailTrace_4090170 : CollatzResearch.WordTrace tailWord_4090170 prefixEnd_4090170 1400148779066911616509771 := by
  unfold tailWord_4090170
  simp only [CollatzResearch.WordTrace]
  refine ⟨37295188898005027566766991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99453837061346740178045309 37295188898005027566766991)
  ·
    refine ⟨55942783347007541350150487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37295188898005027566766991 55942783347007541350150487)
    ·
      refine ⟨83914175020511312025225731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55942783347007541350150487 83914175020511312025225731)
      ·
        refine ⟨125871262530766968037838597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83914175020511312025225731 125871262530766968037838597)
        ·
          refine ⟨23600861724518806507094737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125871262530766968037838597 23600861724518806507094737)
          ·
            refine ⟨17700646293389104880321053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23600861724518806507094737 17700646293389104880321053)
            ·
              refine ⟨6637742360020914330120395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17700646293389104880321053 6637742360020914330120395)
              ·
                refine ⟨9956613540031371495180593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6637742360020914330120395 9956613540031371495180593)
                ·
                  refine ⟨7467460155023528621385445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9956613540031371495180593 7467460155023528621385445)
                  ·
                    refine ⟨1400148779066911616509771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7467460155023528621385445 1400148779066911616509771)
                    ·
                      rfl

theorem cell22_4090170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_4090170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090170 prefixEnd_4090170 := by exact prefixLift 4090170
  have htrace : WordTrace (prefixWord ++ tailWord_4090170) baseStart_4090170 baseEnd_4090170 := by
    simpa [prefixWord, tailWord_4090170, baseEnd_4090170] using wordTrace_append hprefix tailTrace_4090170
  have hstable : (prefixWord ++ tailWord_4090170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090170).length < 2 ^ (prefixWord ++ tailWord_4090170).sum := by decide
  have hdescent : baseEnd_4090170 < baseStart_4090170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090264 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 5]
def baseStart_4090264 : Nat := 118140960795 + 4090264 * 2 ^ 59
def prefixEnd_4090264 : Nat := 4983230072969 + 3 ^ 40 * 4090264 * 2
def baseEnd_4090264 : Nat := 466726985729308901553161

theorem tailTrace_4090264 : CollatzResearch.WordTrace tailWord_4090264 prefixEnd_4090264 466726985729308901553161 := by
  unfold tailWord_4090264
  simp only [CollatzResearch.WordTrace]
  refine ⟨74592092026839782160494923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99456122702453042880659897 74592092026839782160494923)
  ·
    refine ⟨111888138040259673240742385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74592092026839782160494923 111888138040259673240742385)
    ·
      refine ⟨83916103530194754930556789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111888138040259673240742385 83916103530194754930556789)
      ·
        refine ⟨7867134705955758274739699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83916103530194754930556789 7867134705955758274739699)
        ·
          refine ⟨11800702058933637412109549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7867134705955758274739699 11800702058933637412109549)
          ·
            refine ⟨4425263272100114029541081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11800702058933637412109549 4425263272100114029541081)
            ·
              refine ⟨3318947454075085522155811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4425263272100114029541081 3318947454075085522155811)
              ·
                refine ⟨4978421181112628283233717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3318947454075085522155811 4978421181112628283233717)
                ·
                  refine ⟨466726985729308901553161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4978421181112628283233717 466726985729308901553161)
                  ·
                    rfl

theorem cell22_4090264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 5].length) (baseStart_4090264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090264 prefixEnd_4090264 := by exact prefixLift 4090264
  have htrace : WordTrace (prefixWord ++ tailWord_4090264) baseStart_4090264 baseEnd_4090264 := by
    simpa [prefixWord, tailWord_4090264, baseEnd_4090264] using wordTrace_append hprefix tailTrace_4090264
  have hstable : (prefixWord ++ tailWord_4090264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090264).length < 2 ^ (prefixWord ++ tailWord_4090264).sum := by decide
  have hdescent : baseEnd_4090264 < baseStart_4090264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090288 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_4090288 : Nat := 118140960795 + 4090288 * 2 ^ 59
def prefixEnd_4090288 : Nat := 4983230072969 + 3 ^ 40 * 4090288 * 2
def baseEnd_4090288 : Nat := 1400189172878398642059409

theorem tailTrace_4090288 : CollatzResearch.WordTrace tailWord_4090288 prefixEnd_4090288 1400189172878398642059409 := by
  unfold tailWord_4090288
  simp only [CollatzResearch.WordTrace]
  refine ⟨74592529702796308209931759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99456706270395077613242345 74592529702796308209931759)
  ·
    refine ⟨111888794554194462314897639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74592529702796308209931759 111888794554194462314897639)
    ·
      refine ⟨167833191831291693472346459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111888794554194462314897639 167833191831291693472346459)
      ·
        refine ⟨251749787746937540208519689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167833191831291693472346459 251749787746937540208519689)
        ·
          refine ⟨188812340810203155156389767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251749787746937540208519689 188812340810203155156389767)
          ·
            refine ⟨283218511215304732734584651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188812340810203155156389767 283218511215304732734584651)
            ·
              refine ⟨424827766822957099101876977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283218511215304732734584651 424827766822957099101876977)
              ·
                refine ⟨318620825117217824326407733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424827766822957099101876977 318620825117217824326407733)
                ·
                  refine ⟨29870702354739171030600725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318620825117217824326407733 29870702354739171030600725)
                  ·
                    refine ⟨1400189172878398642059409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29870702354739171030600725 1400189172878398642059409)
                    ·
                      rfl

theorem cell22_4090288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_4090288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090288 prefixEnd_4090288 := by exact prefixLift 4090288
  have htrace : WordTrace (prefixWord ++ tailWord_4090288) baseStart_4090288 baseEnd_4090288 := by
    simpa [prefixWord, tailWord_4090288, baseEnd_4090288] using wordTrace_append hprefix tailTrace_4090288
  have hstable : (prefixWord ++ tailWord_4090288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090288).length < 2 ^ (prefixWord ++ tailWord_4090288).sum := by decide
  have hdescent : baseEnd_4090288 < baseStart_4090288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090290 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_4090290 : Nat := 118140960795 + 4090290 * 2 ^ 59
def prefixEnd_4090290 : Nat := 4983230072969 + 3 ^ 40 * 4090290 * 2
def baseEnd_4090290 : Nat := 1400189857519271303509403

theorem tailTrace_4090290 : CollatzResearch.WordTrace tailWord_4090290 prefixEnd_4090290 1400189857519271303509403 := by
  unfold tailWord_4090290
  simp only [CollatzResearch.WordTrace]
  refine ⟨37296283087896342690359081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99456754901056913840957549 37296283087896342690359081)
  ·
    refine ⟨27972212315922257017769311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37296283087896342690359081 27972212315922257017769311)
    ·
      refine ⟨41958318473883385526653967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27972212315922257017769311 41958318473883385526653967)
      ·
        refine ⟨62937477710825078289980951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41958318473883385526653967 62937477710825078289980951)
        ·
          refine ⟨94406216566237617434971427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62937477710825078289980951 94406216566237617434971427)
          ·
            refine ⟨141609324849356426152457141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94406216566237617434971427 141609324849356426152457141)
            ·
              refine ⟨13275874204627164951792857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141609324849356426152457141 13275874204627164951792857)
              ·
                refine ⟨9956905653470373713844643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13275874204627164951792857 9956905653470373713844643)
                ·
                  refine ⟨14935358480205560570766965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9956905653470373713844643 14935358480205560570766965)
                  ·
                    refine ⟨1400189857519271303509403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14935358480205560570766965 1400189857519271303509403)
                    ·
                      rfl

theorem cell22_4090290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_4090290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090290 prefixEnd_4090290 := by exact prefixLift 4090290
  have htrace : WordTrace (prefixWord ++ tailWord_4090290) baseStart_4090290 baseEnd_4090290 := by
    simpa [prefixWord, tailWord_4090290, baseEnd_4090290] using wordTrace_append hprefix tailTrace_4090290
  have hstable : (prefixWord ++ tailWord_4090290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090290).length < 2 ^ (prefixWord ++ tailWord_4090290).sum := by decide
  have hdescent : baseEnd_4090290 < baseStart_4090290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090324 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_4090324 : Nat := 118140960795 + 4090324 * 2 ^ 59
def prefixEnd_4090324 : Nat := 4983230072969 + 3 ^ 40 * 4090324 * 2
def baseEnd_4090324 : Nat := 1400201496414106548159299

theorem tailTrace_4090324 : CollatzResearch.WordTrace tailWord_4090324 prefixEnd_4090324 1400201496414106548159299 := by
  unfold tailWord_4090324
  simp only [CollatzResearch.WordTrace]
  refine ⟨74593186216731097284087013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99457581622308129712116017 74593186216731097284087013)
  ·
    refine ⟨13986222415637080740766315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74593186216731097284087013 13986222415637080740766315)
    ·
      refine ⟨20979333623455621111149473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13986222415637080740766315 20979333623455621111149473)
      ·
        refine ⟨15734500217591715833362105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20979333623455621111149473 15734500217591715833362105)
        ·
          refine ⟨11800875163193786875021579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15734500217591715833362105 11800875163193786875021579)
          ·
            refine ⟨17701312744790680312532369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11800875163193786875021579 17701312744790680312532369)
            ·
              refine ⟨13275984558593010234399277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17701312744790680312532369 13275984558593010234399277)
              ·
                refine ⟨4978494209472378837899729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13275984558593010234399277 4978494209472378837899729)
                ·
                  refine ⟨3733870657104284128424797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4978494209472378837899729 3733870657104284128424797)
                  ·
                    refine ⟨1400201496414106548159299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3733870657104284128424797 1400201496414106548159299)
                    ·
                      rfl

theorem cell22_4090324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_4090324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090324 prefixEnd_4090324 := by exact prefixLift 4090324
  have htrace : WordTrace (prefixWord ++ tailWord_4090324) baseStart_4090324 baseEnd_4090324 := by
    simpa [prefixWord, tailWord_4090324, baseEnd_4090324] using wordTrace_append hprefix tailTrace_4090324
  have hstable : (prefixWord ++ tailWord_4090324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090324).length < 2 ^ (prefixWord ++ tailWord_4090324).sum := by decide
  have hdescent : baseEnd_4090324 < baseStart_4090324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090339 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 2, 4]
def baseStart_4090339 : Nat := 118140960795 + 4090339 * 2 ^ 59
def prefixEnd_4090339 : Nat := 4983230072969 + 3 ^ 40 * 4090339 * 2
def baseEnd_4090339 : Nat := 1400206631220651509034253

theorem tailTrace_4090339 : CollatzResearch.WordTrace tailWord_4090339 prefixEnd_4090339 1400206631220651509034253 := by
  unfold tailWord_4090339
  simp only [CollatzResearch.WordTrace]
  refine ⟨149186919528407852129970071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99457946352271901419980047 149186919528407852129970071)
  ·
    refine ⟨223780379292611778194955107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149186919528407852129970071 223780379292611778194955107)
    ·
      refine ⟨335670568938917667292432661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223780379292611778194955107 335670568938917667292432661)
      ·
        refine ⟨15734557919011765654332781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 335670568938917667292432661 15734557919011765654332781)
        ·
          refine ⟨5900459219629412120374793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15734557919011765654332781 5900459219629412120374793)
          ·
            refine ⟨4425344414722059090281095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5900459219629412120374793 4425344414722059090281095)
            ·
              refine ⟨6638016622083088635421643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4425344414722059090281095 6638016622083088635421643)
              ·
                refine ⟨9957024933124632953132465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6638016622083088635421643 9957024933124632953132465)
                ·
                  refine ⟨7467768699843474714849349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9957024933124632953132465 7467768699843474714849349)
                  ·
                    refine ⟨1400206631220651509034253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7467768699843474714849349 1400206631220651509034253)
                    ·
                      rfl

theorem cell22_4090339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 4].length) (baseStart_4090339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090339 prefixEnd_4090339 := by exact prefixLift 4090339
  have htrace : WordTrace (prefixWord ++ tailWord_4090339) baseStart_4090339 baseEnd_4090339 := by
    simpa [prefixWord, tailWord_4090339, baseEnd_4090339] using wordTrace_append hprefix tailTrace_4090339
  have hstable : (prefixWord ++ tailWord_4090339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090339).length < 2 ^ (prefixWord ++ tailWord_4090339).sum := by decide
  have hdescent : baseEnd_4090339 < baseStart_4090339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090365 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 7]
def baseStart_4090365 : Nat := 118140960795 + 4090365 * 2 ^ 59
def prefixEnd_4090365 : Nat := 4983230072969 + 3 ^ 40 * 4090365 * 2
def baseEnd_4090365 : Nat := 466738510517332035961391

theorem tailTrace_4090365 : CollatzResearch.WordTrace tailWord_4090365 prefixEnd_4090365 466738510517332035961391 := by
  unfold tailWord_4090365
  simp only [CollatzResearch.WordTrace]
  refine ⟨149187867826313658570416549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99458578550875772380277699 149187867826313658570416549)
  ·
    refine ⟨27972725217433810981953103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149187867826313658570416549 27972725217433810981953103)
    ·
      refine ⟨41959087826150716472929655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27972725217433810981953103 41959087826150716472929655)
      ·
        refine ⟨62938631739226074709394483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41959087826150716472929655 62938631739226074709394483)
        ·
          refine ⟨94407947608839112064091725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62938631739226074709394483 94407947608839112064091725)
          ·
            refine ⟨35402980353314667024034397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94407947608839112064091725 35402980353314667024034397)
            ·
              refine ⟨13276117632493000134012899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35402980353314667024034397 13276117632493000134012899)
              ·
                refine ⟨19914176448739500201019349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13276117632493000134012899 19914176448739500201019349)
                ·
                  refine ⟨466738510517332035961391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19914176448739500201019349 466738510517332035961391)
                  ·
                    rfl

theorem cell22_4090365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_4090365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090365 prefixEnd_4090365 := by exact prefixLift 4090365
  have htrace : WordTrace (prefixWord ++ tailWord_4090365) baseStart_4090365 baseEnd_4090365 := by
    simpa [prefixWord, tailWord_4090365, baseEnd_4090365] using wordTrace_append hprefix tailTrace_4090365
  have hstable : (prefixWord ++ tailWord_4090365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090365).length < 2 ^ (prefixWord ++ tailWord_4090365).sum := by decide
  have hdescent : baseEnd_4090365 < baseStart_4090365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090369 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 3, 3]
def baseStart_4090369 : Nat := 118140960795 + 4090369 * 2 ^ 59
def prefixEnd_4090369 : Nat := 4983230072969 + 3 ^ 40 * 4090369 * 2
def baseEnd_4090369 : Nat := 1400216900833741430784161

theorem tailTrace_4090369 : CollatzResearch.WordTrace tailWord_4090369 prefixEnd_4090369 1400216900833741430784161 := by
  unfold tailWord_4090369
  simp only [CollatzResearch.WordTrace]
  refine ⟨149188013718299167253562161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99458675812199444835708107 149188013718299167253562161)
  ·
    refine ⟨111891010288724375440171621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149188013718299167253562161 111891010288724375440171621)
    ·
      refine ⟨20979564429135820395032179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111891010288724375440171621 20979564429135820395032179)
      ·
        refine ⟨31469346643703730592548269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20979564429135820395032179 31469346643703730592548269)
        ·
          refine ⟨11801004991388898972205601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31469346643703730592548269 11801004991388898972205601)
          ·
            refine ⟨8850753743541674229154201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11801004991388898972205601 8850753743541674229154201)
            ·
              refine ⟨6638065307656255671865651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8850753743541674229154201 6638065307656255671865651)
              ·
                refine ⟨9957097961484383507798477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6638065307656255671865651 9957097961484383507798477)
                ·
                  refine ⟨3733911735556643815424429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9957097961484383507798477 3733911735556643815424429)
                  ·
                    refine ⟨1400216900833741430784161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3733911735556643815424429 1400216900833741430784161)
                    ·
                      rfl

theorem cell22_4090369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_4090369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090369 prefixEnd_4090369 := by exact prefixLift 4090369
  have htrace : WordTrace (prefixWord ++ tailWord_4090369) baseStart_4090369 baseEnd_4090369 := by
    simpa [prefixWord, tailWord_4090369, baseEnd_4090369] using wordTrace_append hprefix tailTrace_4090369
  have hstable : (prefixWord ++ tailWord_4090369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090369).length < 2 ^ (prefixWord ++ tailWord_4090369).sum := by decide
  have hdescent : baseEnd_4090369 < baseStart_4090369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090420 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_4090420 : Nat := 118140960795 + 4090420 * 2 ^ 59
def prefixEnd_4090420 : Nat := 4983230072969 + 3 ^ 40 * 4090420 * 2
def baseEnd_4090420 : Nat := 1400234359175994297759005

theorem tailTrace_4090420 : CollatzResearch.WordTrace tailWord_4090420 prefixEnd_4090420 1400234359175994297759005 := by
  unfold tailWord_4090420
  simp only [CollatzResearch.WordTrace]
  refine ⟨74594936920557201481834357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99459915894076268642445809 74594936920557201481834357)
  ·
    refine ⟨6993275336302237638921971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74594936920557201481834357 6993275336302237638921971)
    ·
      refine ⟨10489913004453356458382957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6993275336302237638921971 10489913004453356458382957)
      ·
        refine ⟨3933717376670008671893609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10489913004453356458382957 3933717376670008671893609)
        ·
          refine ⟨2950288032502506503920207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3933717376670008671893609 2950288032502506503920207)
          ·
            refine ⟨4425432048753759755880311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950288032502506503920207 4425432048753759755880311)
            ·
              refine ⟨6638148073130639633820467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4425432048753759755880311 6638148073130639633820467)
              ·
                refine ⟨9957222109695959450730701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6638148073130639633820467 9957222109695959450730701)
                ·
                  refine ⟨3733958291135984794024013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9957222109695959450730701 3733958291135984794024013)
                  ·
                    refine ⟨1400234359175994297759005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3733958291135984794024013 1400234359175994297759005)
                    ·
                      rfl

theorem cell22_4090420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_4090420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090420 prefixEnd_4090420 := by exact prefixLift 4090420
  have htrace : WordTrace (prefixWord ++ tailWord_4090420) baseStart_4090420 baseEnd_4090420 := by
    simpa [prefixWord, tailWord_4090420, baseEnd_4090420] using wordTrace_append hprefix tailTrace_4090420
  have hstable : (prefixWord ++ tailWord_4090420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090420).length < 2 ^ (prefixWord ++ tailWord_4090420).sum := by decide
  have hdescent : baseEnd_4090420 < baseStart_4090420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090440 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_4090440 : Nat := 118140960795 + 4090440 * 2 ^ 59
def prefixEnd_4090440 : Nat := 4983230072969 + 3 ^ 40 * 4090440 * 2
def baseEnd_4090440 : Nat := 1400241205584720912258943

theorem tailTrace_4090440 : CollatzResearch.WordTrace tailWord_4090440 prefixEnd_4090440 1400241205584720912258943 := by
  unfold tailWord_4090440
  simp only [CollatzResearch.WordTrace]
  refine ⟨74595301650520973189698387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99460402200694630919597849 74595301650520973189698387)
  ·
    refine ⟨111892952475781459784547581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74595301650520973189698387 111892952475781459784547581)
    ·
      refine ⟨41959857178418047419205343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111892952475781459784547581 41959857178418047419205343)
      ·
        refine ⟨62939785767627071128808015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41959857178418047419205343 62939785767627071128808015)
        ·
          refine ⟨94409678651440606693212023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62939785767627071128808015 94409678651440606693212023)
          ·
            refine ⟨141614517977160910039818035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94409678651440606693212023 141614517977160910039818035)
            ·
              refine ⟨212421776965741365059727053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141614517977160910039818035 212421776965741365059727053)
              ·
                refine ⟨79658166362153011897397645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212421776965741365059727053 79658166362153011897397645)
                ·
                  refine ⟨29871812385807379461524117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79658166362153011897397645 29871812385807379461524117)
                  ·
                    refine ⟨1400241205584720912258943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29871812385807379461524117 1400241205584720912258943)
                    ·
                      rfl

theorem cell22_4090440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_4090440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090440 prefixEnd_4090440 := by exact prefixLift 4090440
  have htrace : WordTrace (prefixWord ++ tailWord_4090440) baseStart_4090440 baseEnd_4090440 := by
    simpa [prefixWord, tailWord_4090440, baseEnd_4090440] using wordTrace_append hprefix tailTrace_4090440
  have hstable : (prefixWord ++ tailWord_4090440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090440).length < 2 ^ (prefixWord ++ tailWord_4090440).sum := by decide
  have hdescent : baseEnd_4090440 < baseStart_4090440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090455 : List Nat := [1, 1, 3, 2, 2, 2, 1, 10]
def baseStart_4090455 : Nat := 118140960795 + 4090455 * 2 ^ 59
def prefixEnd_4090455 : Nat := 4983230072969 + 3 ^ 40 * 4090455 * 2
def baseEnd_4090455 : Nat := 155582926710140652570433

theorem tailTrace_4090455 : CollatzResearch.WordTrace tailWord_4090455 prefixEnd_4090455 155582926710140652570433 := by
  unfold tailWord_4090455
  simp only [CollatzResearch.WordTrace]
  refine ⟨149191150395987603941192819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99460766930658402627461879 149191150395987603941192819)
  ·
    refine ⟨223786725593981405911789229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149191150395987603941192819 223786725593981405911789229)
    ·
      refine ⟨83920022097743027216920961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223786725593981405911789229 83920022097743027216920961)
      ·
        refine ⟨62940016573307270412690721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83920022097743027216920961 62940016573307270412690721)
        ·
          refine ⟨47205012429980452809518041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62940016573307270412690721 47205012429980452809518041)
          ·
            refine ⟨35403759322485339607138531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47205012429980452809518041 35403759322485339607138531)
            ·
              refine ⟨53105638983728009410707797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35403759322485339607138531 53105638983728009410707797)
              ·
                refine ⟨155582926710140652570433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53105638983728009410707797 155582926710140652570433)
                ·
                  rfl

theorem cell22_4090455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 10].length) (baseStart_4090455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4090455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4090455 prefixEnd_4090455 := by exact prefixLift 4090455
  have htrace : WordTrace (prefixWord ++ tailWord_4090455) baseStart_4090455 baseEnd_4090455 := by
    simpa [prefixWord, tailWord_4090455, baseEnd_4090455] using wordTrace_append hprefix tailTrace_4090455
  have hstable : (prefixWord ++ tailWord_4090455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090455).length < 2 ^ (prefixWord ++ tailWord_4090455).sum := by decide
  have hdescent : baseEnd_4090455 < baseStart_4090455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
